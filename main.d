
//--  (w) Frank F. Hirsch (2011)

/*
*** todo
 - do static analysis
 - generate code
 - type literals
 - all types global (?)
*/

module main;

import debg;
import libs;
import ablibs;
import lexer;
import cells;
import types;
import trafo;
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

Env* base_env;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- eval helpers
//----------------
Env* mk_lambda_environment(Lamb* lam,Cell[] args,Env* env) {
  Env* lamenv=env_clone(lam.env);
  //-- at least as much parameters as arguments (rest must be defaulted)
//  assert(lam.pars.length>=args.length);
  for (int k=0;k<lam.pars.length;++k) {
    //-- formal parameter
    Cell par=lam.pars[k];
    //-- handle ellipse (...)
    if (k==(lam.pars.length-1)) {
      string n;
      if (isa(par,TSymbol)) {
        n=par.sym;
      }
      if (isa(par,TList) && (par.lst.length==2)) {
        n=as_symbol(par.lst[1]);
      }
      if (n=="...") {
        Cell[] eargs;
        for (int ka=k;ka<args.length;++ka) {
          eargs~=eval(args[ka]);
//          printf("### %.*s -> %.*s\n",cells.str(args[ka]),cells.str(eargs[$-1]));
        }
//        printf("### %i\n",eargs.length);
        env_put(lamenv,"ellipse",array_cell(eargs));
        break;
      }
    }
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
//      Cell t=par.lst[0];
      string n=as_symbol(par.lst[1]);
      env_put(lamenv,n,eval(arg));
      continue;
    }
    //
    assert(false,"Invokation error");
  }
  return lamenv;
}
Cell resolve_function(Cell sym,ref Cell[] args,ref Cell[] eargs) {
  FTabEntry* candidate_entry;
  Signature candidate_sig;
  Cell candidate;
  Cell[] teargs;
  string name=as_symbol(sym);
  Env* e=environment;
  for (;;) {
//printf("looking up Function '%.*s' in environment %p\n",name,e);
    if (e) e=env_find(e,name);
    if (!e) {
      printf("*** Error: Function '%.*s' lookup failed!\n",name);
      assert(false);
      return null_cell();
    }
    candidate=evalin(sym,e);
    if (!isa(candidate,TFtab)) return candidate;
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
    }
    candidate_entry=ftab_resolve(candidate.ftab,eargs,name);
    if (candidate_entry) {
      candidate_sig=candidate_entry.sig;
      teargs=eargs.dup;
      while (eargs.length<candidate_sig.length) {
        if (candidate_sig[eargs.length].name=="...") break;
        eargs~=candidate_sig[eargs.length].defv;
      }
      args=eargs;
      break;
    }
    e=e.outer;
  }
  return candidate_entry.fun;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- eval
//----------------
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
//  printf("+++ A %i\n",args.length);
  if (isa(x0,TSymbol)) {
    x0=resolve_function(x0,args,eargs);
  }
//  printf("+++ B %i\n",args.length);
  if (isa(x0,TLfun)) {
    return x0.lfn(args);
  }
//  printf("+++ C %i\n",args.length);
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
void lexec(string filename) {
  Cell c=lparse(cast(string)std.file.read(filename));
  c.show(true);
  eval(c);
}
void aexec(string filename) {
  bool showflag=true;
  bool reorder=true;
  Cell c=parse_file_to_cell(filename);
//  if (showflag) c.show(true);
  reduce_seq_of_one(&c);
  if (reorder) {
    operators_to_front(c,["defun","def"]);
    operator_to_front(c,"supertype");
    operator_to_front(c,"aliastype");
    operator_to_front(c,"deftype");
    if (showflag) printf("%.*s\n",pretty_str(c,0));
  }
  eval(c);
//  if (showflag) c.show(true);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- main
//----------------

Env* mk_base_env() {
  Env* e=mk_env();
  push_env(e);
  init_hlparse();
  init_types();
  return e;
}

void dump_info() {
//  env_pr(base_env);
  env_pr(environment);
}

void exec(string fn) {
  base_env=mk_base_env();
  init_libs();
  push_env();
  //try {
    aexec(fn);
  /*} catch (Exception e) {
    //printf("[%.*s] ",cells.str(evalcell));
    //printf("%.*s\n",e.toString());
  }*/
}
void env_info() {
  for (int k=0;k<envstack.length;++k) printf("%p ",envstack[k]);
  printf("[%i] be=%p e=%p\n",envstack.length,base_env,environment);
}
void main(string[] args) {
  string fn;
  if (args.length>1) fn=args[1]~".ast";
  else fn="test.ast";
  exec(fn);
}
