
//--  (w) Frank F. Hirsch (2011)

module main;

import debg;
import libs;
import lexer;
import cells;
import types;
import utils;
import llparse;
import hlparse;
import signatures;
import environments;
import std.file;
import std.stdio;
import std.string;

Env* global_env;

const bool require_declaration_before_use=true;

struct State {
  Cell val;
  int  ret;
  int  brk;
  int  cnt;
}
State state;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- eval
//----------------
Env* mk_lambda_environment(Lamb* lam,Cell[] args,Env* env) {
  Env* lamenv=env_clone(lam.env);
  //-- at least as much parameters as arguments (rest must be defaulted)
  assert(lam.pars.length>=args.length);
  for (int k=0;k<lam.pars.length;++k) {
    //-- formal parameter
    Cell par=lam.pars[k];
    //-- handle defaulted parameter declaration ((type name value))
    if (k>=args.length) {
      //- no argument for this parameter
      if (isa(par,TList) && (par.lst.length==3)) {
        //- default argument available
        Cell t=par.lst[0];
        string n=as_symbol(par.lst[1]);
        env_put(lamenv,n,par.lst[2]);
        continue;
      }
      //- no default argument
      assert(false,"Missing invokation argument(s)");
    }
    //-- call argument
    Cell arg=args[k];
    //-- handle untyped parameter declaration (name)
    if (isa(par,TSymbol)) {
      env_put(lamenv,par.sym,eval(arg,env));
      continue;
    }
    //-- handle typed parameter declaration (type name)
    if (isa(par,TList)) {
      assert(par.lst.length>1);
      Cell t=par.lst[0];
      string n=as_symbol(par.lst[1]);
      env_put(lamenv,n,eval(arg,env));
      continue;
    }
    //
    assert(false,"Invokation error");
  }
  return lamenv;
}
int depth=0;
int maxdepth=0;
Cell evalcell;
Cell eval(Cell x,Env* env) {
  static if (debf) {debEnter("eval('%.*s',Env)",cells.str(x));scope (exit) debLeave();}
  evalcell=x;
  static if (0) {
    maxdepth=max(maxdepth,++depth);
    scope (exit) --depth;
  }
start:
  static if (0) {
    indent(depth);
    printf("%.*s\n",str(x));
  }
  if (state.ret||state.brk||state.cnt) return state.val;
  if (isa(x,TSymbol)) return env_get(env,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$].dup; // !!! dup needed
  Cell help=x.lst[0];
  Cell x0=eval(x.lst[0],env);
  if (isa(x0,TFtab)) {
    // !!! this is a mess and needs a cleanup
    // also, it fails if an FTab value in the current scope shadows
    // a value of a different type in one of the outer scopes
    foreach (ref arg;args) arg=eval(arg,env);
    FTabEntry* fte;
    Env* e=env;
    for (;;) {
      string name;
      if (isa(help,TSymbol)) name=help.sym;
      fte=ftab_resolve(x0.ftab,args,name);
      if (fte) break;
      if (!e.outer) assert(false,"function lookup failed");
      e=e.outer;
      x0=eval(x.lst[0],e);
    }
    while (args.length<fte.sig.length) {
      args~=fte.sig[args.length].defv;
    }
    x0=fte.fun;
  }
  if (isa(x0,TLfun)) {
    return x0.lfn(args,env);
  }
  if (isa(x0,TFun)) {
    foreach (ref arg;args) arg=eval(arg,env);
    return x0.fun(args);
  }
  if (isa(x0,TLambda)) {
    Lamb* lam=as_lambda(x0);
    Env* lamenv=mk_lambda_environment(lam,args,env);
    Cell c=eval(lam.expr,lamenv);
    state.ret=0;
    return c;
  } else {
    printf("[unexpected type %i]\n",x0.type);
    printf("[type name is %.*s]\n",types.str(x0.type));
    assert(false);
  }
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- test
//----------------

void ltest(string filename) {
  Cell c=lparse(cast(string)std.file.read(filename));
  c.show(true);
  eval(c,global_env);
}
void atest(string filename) {
  bool showflag=true;
  Token t=parse(cast(string)std.file.read(filename));
  //if (showflag) t.show_short();
  Cell c=token2cell(t);
  c.lst=sym_cell("seq")~c.lst;
  if (showflag) c.show(true);
  eval(c,global_env);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- main
//----------------

void init() {
  global_env=mk_env();
  init_hlparse();
  init_types(global_env);
  add_globals(global_env);
}

void main(string[] args) {
  init();
  try {
    if (args.length>1) {
      atest(args[1]~".ast");
    } else {
      atest("test.ast");
      //ltest("tests.l");
    }
  } catch (Exception e) {
    printf("evalcell = %.*s\n",cells.str(evalcell));
    throw(e);
  }
}
