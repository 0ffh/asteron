
//--  (w) Frank F. Hirsch (2011)

// todo: more than you can shake a stick at

module ai;

import eval_helpers;
import debg;
import libs;
import lexer;
import cells;
import types;
import trafo;
import utils;
import sexpr_parser;
import signatures;
import environments;
import std.file;
import std.stdio;
import std.string;
import std.format;

const bool debf=debflag && 01;

const bool require_declaration_before_use=true;

enum StC {run=0,ret,brk,cnt,abt};

struct State {
  StC    code;
  Cell   val;
}
State state;

Env* base_env;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- eval helpers
//----------------
Env* mk_lambda_environment(Lamb* lam,Cell[] args) {
  static if (debf) {debEnter("mk_lambda_environment");scope (exit) debLeave();}
  Env* lamenv=env_clone(lam.env);
  //-- at least as much parameters as arguments (rest must be defaulted)
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
        env_put(lamenv,"ellipse",array_cell(args[k..$]));
        break;
      }
    }
    //-- handle defaulted parameter declaration ((type name value))
    if (k>=args.length) {
      //- no argument for this parameter
      if (isa(par,TList) && (par.lst.length==3)) {
        //- default argument available
//        Cell t=par.lst[0];
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
//      writefln("  put %s <- %s",par.sym,cells.str(arg));
      env_put(lamenv,par.sym,arg);
      continue;
    }
    //-- handle typed parameter declaration (type name)
    if (isa(par,TList)) {
      assert(par.lst.length>1);
//      Cell t=par.lst[0];
      string n=as_symbol(par.lst[1]);
      env_put(lamenv,n,arg);
      continue;
    }
    //
    assert(false,"Invokation error");
  }
  return lamenv;
}
Cell resolve_function(Cell sym,ref Cell[] args) {
  static if (debf) {debEnter("resolve_function");scope (exit) debLeave();}
  string name=as_symbol(sym);
  FTabEntry* entry=resolve_name_as_ftab_entry(name,args);
  if (!entry) {
    writef("*** Error: Function '%s' lookup failed!\n",name);
    assert(false);
  }
  return entry.fun;
}
void eval_args(ref Cell[] args,ref Cell[] eargs) {
  if (!eargs.length) {
    eargs.length=args.length;
    for (int k;k<args.length;++k) {
      eargs[k]=eval(args[k]);
      unalias_type_of(eargs[k]);
    }
  }
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- eval
//----------------
int depth=0;
int maxdepth=0;
Cell[] evalcell;
Cell evalin(Cell x,Env* env) {
  push_env(env);
  x=eval(x);
  pop_env();
  return x;
}
Cell eval(Cell x) {
  static if (debf) {debEnter("eval('%s')",cells.str(x));scope (exit) debLeave();}
  evalcell~=x;
  scope (exit) evalcell.length=evalcell.length-1;
  x=x.clone(); // *** TODO: get by without cloning here
  static if (0) {
    maxdepth=max(maxdepth,++depth);
    scope (exit) --depth;
  }
  static if (0) {
    indent(depth);
    writef("%s\n",str(x));
  }
  if (state.code) {
//    writefln("code = %s\n",state.code);
    return state.val;
  }
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$].dup; // !!! dup needed
  Cell[] eargs;
  Cell x0=x.lst[0];
  while (isa(x0,TList)) x0=eval(x0);
  if (isa(x0,TSymbol)) {
    Cell r=resolve_symbol_except_ftabs(x0);
    if (isa(r,TNull)) {
      eval_args(args,eargs);
      r=resolve_function(x0,eargs);
    }
    x0=r;
  }
  if (isa(x0,TLfun)) {
//    writefln("lazy %s",cells.str(x.lst[0]));
    return x0.lfn(args);
  }
  if (isa(x0,TFun)) {
    eval_args(args,eargs);
    return x0.fun(eargs);
  }
  if (isa(x0,TLambda)) {
    eval_args(args,eargs);
    Lamb* lam=as_lambda(x0);
    Env* lamenv=mk_lambda_environment(lam,eargs);
    static if (0) {
      writef("----- lamenv\n");
      lamenv.show();
      writef("----- lamenv.outer\n");
      if (lamenv.outer) lamenv.outer.show();
    }
    Cell c=evalin(lam.expr,lamenv);
    if (state.code==StC.ret) state.code=StC.run;
    return c;
  }
  writef("[unexpected type %d]\n",x0.type);
  writef("[type name is %s]\n",types.str(x0.type));
  assert(false);
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- test
//----------------
void exec_l(string filename) {
  Cell c=parse_sexpr(cast(string)std.file.read(filename));
  c.show(true);
  eval(c);
}
void exec_ast(string filename) {
  bool showflag=!true;
  bool reorder=true;
  Cell c=parse_sexpr_file(filename);
//  if (showflag) c.show(true);
  reduce_seq_of_one(c);
  if (reorder) {
    operators_to_front(c,["defun","def"]);
    operator_to_front(c,"supertype");
    operator_to_front(c,"aliastype");
    operator_to_front(c,"deftype");
    if (showflag) writef("%s\n",pretty_str(c,0));
  }
  writef("%s\n",pretty_str(c,0));
//  Cell run=list_cell([symbol_cell("main")]);
  push_env();
  eval(c);
//  eval(run);
  pop_env();
//  push_env();eval(c);eval(run);pop_env();
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
  init_types();
  return e;
}
void dump_info() {
  env_pr(environment);
}
void exec(string fn) {
  base_env=mk_base_env();
  init_libs();
  push_env();
  exec_ast(fn);
}
void env_info() {
  for (int k=0;k<envstack.length;++k) writef("%p ",envstack[k]);
  writef("[%d] be=%p e=%p\n",envstack.length,base_env,environment);
}
void main(string[] args) {
  string fn;
  if (args.length>1) fn=args[1]~".l";
  else fn="itests.l";
  exec(fn);
}
