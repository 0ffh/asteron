
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
      env_put(lamenv,par.sym,eval(arg));
      continue;
    }
    //-- handle typed parameter declaration (type name)
    if (isa(par,TList)) {
      assert(par.lst.length>1);
      Cell t=par.lst[0];
      string n=as_symbol(par.lst[1]);
      env_put(lamenv,n,eval(arg));
      continue;
    }
    //
    assert(false,"Invokation error");
  }
  return lamenv;
}
Cell resolve_function(Cell sym,Cell[] args,Cell[] eargs,Env* env) {
  Cell candidate;
  string name=sym.sym;
  Env* e=environment;
  for (;;) {
//printf("looking up Function '%.*s' int environment %p\n",name,e);
    if (e) e=env_find(e,name);
    if (!e) {
      printf("*** Error: Function '%.*s' lookup failed!\n",name);
      assert(false);
      return null_cell();
    }
    candidate=evalin(sym,e);
    if (!isa(candidate,TFtab)) break;
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
    }
    FTabEntry* fte=ftab_resolve(candidate.ftab,eargs,name);
    if (fte) {
      while (eargs.length<fte.sig.length) {
        eargs~=fte.sig[eargs.length].defv;
      }
      args=eargs;
      candidate=fte.fun;
      break;
    }
    e=e.outer;
  }
  return candidate;
}
int depth=0;
int maxdepth=0;
Cell evalcell;
Cell evalin(Cell x,Env* env) {
  push_env(env);
  x=eval(x);
  pop_env();
  return x;
}
Cell eval(Cell x) {
  static if (debf) {debEnter("eval('%.*s')",cells.str(x));scope (exit) debLeave();}
  evalcell=x;
  static if (0) {
    maxdepth=max(maxdepth,++depth);
    scope (exit) --depth;
  }
  static if (0) {
    indent(depth);
    printf("%.*s\n",str(x));
  }
  if (state.ret||state.brk||state.cnt) return state.val;
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$].dup; // !!! dup needed
  Cell[] eargs;
  Cell x0=x.lst[0];
  while (isa(x0,TList)) x0=eval(x0);
  static if (1) {
    string name;
    if (isa(x0,TSymbol)) {
      Cell candidate;
      name=x0.sym;
      Env* e=environment;
      for (;;) {
  //      printf("looking up Function '%.*s' int environment %p\n",name,e);
        if (e) e=env_find(e,name);
        if (!e) {
          printf("*** Error: Function '%.*s' lookup failed!\n",name);
          assert(false);
          return null_cell();
        }
        candidate=evalin(x0,e);
        if (!isa(candidate,TFtab)) break;
        if (!eargs.length) {
          eargs.length=args.length;
          for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
        }
        FTabEntry* fte=ftab_resolve(candidate.ftab,eargs,name);
        if (fte) {
          while (eargs.length<fte.sig.length) {
            eargs~=fte.sig[eargs.length].defv;
          }
          args=eargs;
          candidate=fte.fun;
          break;
        }
        e=e.outer;
      }
      x0=candidate;
    }
  } else {
    if (isa(x0,TSymbol)) {
      x0=resolve_function(x0,args,eargs,environment);
    }
  }
  if (isa(x0,TLfun)) {
    return x0.lfn(args);
  }
  if (isa(x0,TFun)) {
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
    }
    return x0.fun(eargs);
  }
  if (isa(x0,TLambda)) {
    Lamb* lam=as_lambda(x0);
    Env* lamenv=mk_lambda_environment(lam,args,environment);
    Cell c=evalin(lam.expr,lamenv);
    state.ret=0;
    return c;
  }
  printf("[unexpected type %i]\n",x0.type);
  printf("[type name is %.*s]\n",types.str(x0.type));
  assert(false);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- test
//----------------

void ltest(string filename) {
  Cell c=lparse(cast(string)std.file.read(filename));
  c.show(true);
  eval(c);
}
void atest(string filename) {
  bool showflag=true;
  Token t=parse(cast(string)std.file.read(filename));
  //if (showflag) t.show_short();
  Cell c=token2cell(t);
  c.lst=sym_cell("seq")~c.lst;
  if (showflag) c.show(true);
  eval(c);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- main
//----------------

void init() {
  push_env(mk_env());
  init_hlparse();
  init_types();
  add_globals();
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
