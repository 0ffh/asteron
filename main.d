
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

const bool debf=debflag;

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
Env* mk_lambda_environment(Lamb* lam,Cell[] args,Env* env) {
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
  string name=as_symbol(sym);
  Env* e=environment;
  for (;;) {
//printf("looking up Function '%.*s' in environment %p\n",name,e);
    if (e) e=env_find(e,name);
    if (!e) {
      printf("*** Error: Function '%.*s' lookup failed!\n",name);
      assert(false);
    }
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) return candidate;
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
    }
    candidate_entry=ftab_resolve(candidate.ftab,eargs,name);
    if (candidate_entry) {
      candidate_sig=candidate_entry.sig;
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
  if (state.code) return state.val;
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$].dup; // !!! dup needed
  Cell[] eargs;
  Cell x0=x.lst[0];
  while (isa(x0,TList)) x0=eval(x0);
  if (isa(x0,TSymbol)) {
    x0=resolve_function(x0,args,eargs);
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
    static if (0) {
      printf("----- lamenv\n");
      lamenv.show();
      printf("----- lamenv.outer\n");
      if (lamenv.outer) lamenv.outer.show();
    }
    Cell c=evalin(lam.expr,lamenv);
    if (state.code==StC.ret) state.code=StC.run;
    return c;
  }
  printf("[unexpected type %i]\n",x0.type);
  printf("[type name is %.*s]\n",types.str(x0.type));
  assert(false);
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- abstract eval helpers
//----------------
class FunListEntry {
  string     nam;
  FTabEntry* fte;
  Cell[]     par; // parameters
  Cell       fun; // function cell
  Cell       res; // result value
  bool       abt; // aborted
  static FunListEntry opCall(string nam,FTabEntry* fte,Cell[] par,Cell fun) {
    FunListEntry fle=new FunListEntry();
    fle.nam=nam;
    fle.fte=fte;
    fle.par=par;
    fle.fun=clone_cell(fun);
    fle.res=null_cell();
    fle.abt=false;
    return fle;
  }
}
FunListEntry[] fun_list;
FunListEntry[] call_stack;
FunListEntry call_stack_top() {
  assert(call_stack.length,"Abstract interpreter error: Call stack empty.");
  return call_stack[$-1];
}
void call_stack_push(FunListEntry e) {
  call_stack~=e;
}
FunListEntry call_stack_pop() {
  FunListEntry e=call_stack_top();
  call_stack.length=call_stack.length-1;
  return e;
}
int[string] fun_name_cnt;
void show_fun_list() {
  for (int kfl;kfl<fun_list.length;++kfl) {
    FunListEntry fle=fun_list[kfl];
    static if (0) {
      printf("*************** function %.*s\n",fle.nam);
    } else {
      printf("*************** function %.*s(",fle.nam);
      for (int k=0;k<fle.par.length;++k) {
        printf("%.*s",types.str(fle.par[k].type));
        if (k+1<fle.par.length) printf(",");
      }
      printf(") : %.*s\n",types.str(fle.res.type));
    }
    static if (0) {
      printf("%.*s\n",pretty_str(fle.fun,0));
    }
  }
}
FunListEntry find_in_fun_list(FTabEntry* fte,Cell[] par) {
  for (int kfl;kfl<fun_list.length;++kfl) {
    FunListEntry fle=fun_list[kfl];
    if (fte!=fle.fte) continue;
    if (par.length!=fle.par.length) continue;
    for (int k;k<par.length;++k) {
      if (par[k].type!=fle.par[k].type) break;
      if (k==par.length-1) return fun_list[kfl];
    }
  }
  return null;
}
Cell abs_get_result_from_fun_list(string name) {
  static if (debf) {debEnter("abs_get_result_from_fun_list");scope (exit) debLeave();}
  for (int kfl;kfl<fun_list.length;++kfl) {
    FunListEntry fle=fun_list[kfl];
    if (fle.nam==name) return fle.res;
  }
  assert(false);
}
Cell abs_resolve_function(Cell sym,ref Cell[] args,ref Cell[] eargs,Cell* px0) {
  string lmsg;
  static if (debf) {
    debEnter("abs_resolve_function('"~sym.sym~"')");
    scope (exit) debLeave(cfrm("%.*s / %i",lmsg,state.code));
  }
  printf("abs_resolve_function('%.*s')\n",sym.sym);
  FTabEntry* candidate_entry;
  Signature candidate_sig;
  Cell candidate;
  string name=as_symbol(sym);
  Env* e=environment;
  Cell[] args_bak;
  for (;;) {
    if (e) e=env_find(e,name);
    if (!e) {
      printf("*** Error: Function '%.*s' lookup failed!\n",name);
      assert(false,cfrm("Function '%.*s' lookup failed!\n",name));
    }
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) {
      return candidate;
    }
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) eargs[k]=abs_eval(args[k]);
      if (state.code) {
        lmsg="Parameter abort";
        eargs.length=0;
        return list_cell([any_cell()]);
      }
    }
    args_bak=eargs.dup;
    candidate_entry=ftab_resolve(candidate.ftab,eargs,name);
    if (candidate_entry) {
      candidate_sig=candidate_entry.sig;
      while (eargs.length<candidate_sig.length) {
        if (candidate_sig[eargs.length].name=="...") break;
        eargs~=candidate_sig[eargs.length].defv;
      }
      args=eargs;
      break;
    }
    e=e.outer;
  }
  FunListEntry fle=find_in_fun_list(candidate_entry,args);
  if (fle is null) {
    //printf("!FLE:%.*s\n",name);
    name=cfrm("$%.*s_%d",name,fun_list.length);
    px0.sym=name;
    fle=FunListEntry(name,candidate_entry,args,candidate_entry.fun);
    fun_list~=fle;
    call_stack_push(fle);
    Cell h=abs_eval(list_cell([fle.fun]~args));
    if (!isa(h,TNull)) fle.res=h;
    while (fle.abt) {
      fle.abt=false;
      Cell r=abs_eval(list_cell([fle.fun]~args));
      if (!isa(r,TNull)) fle.res=r;
    }
    call_stack_pop();
  } else {
    //printf("FLE:%.*s (%.*s)\n",name,fle.nam);
    name=fle.nam;
    px0.sym=name;
    if ((fle.res.type==TAny) || (fle.res.type==TNull)) {
      //printf("+++++++ Recursion return type unavailable for %.*s\n",fle.nam);
      fle.abt=true;
      state.code=StC.abt;
      state.val=fle.res;
    }
  }
  lmsg=cfrm("%.*s",types.str(fle.res.type));
  return list_cell([fle.res]);
}
Env* abs_mk_lambda_environment(Lamb* lam,Cell[] args,Env* env) {
  static if (debf) {debEnter("abs_mk_lambda_environment");scope (exit) debLeave();}
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
        Cell[] eargs;
        for (int ka=k;ka<args.length;++ka) {
          eargs~=abs_eval(args[ka]);
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
      env_put(lamenv,par.sym,abs_eval(arg));
      continue;
    }
    //-- handle typed parameter declaration (type name)
    if (isa(par,TList)) {
      assert(par.lst.length>1);
      string n=as_symbol(par.lst[1]);
      env_put(lamenv,n,abs_eval(arg));
      continue;
    }
    //
    assert(false,"Invokation error");
  }
  return lamenv;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- abstract eval
//----------------
Cell abs_evalin(Cell x,Env* env) {
  push_env(env);
  x=abs_eval(x);
  pop_env();
  return x;
}
Cell abs_eval(Cell x) {
  static if (debf) {debEnter("abs_eval('%.*s')",cells.str(x));scope (exit) debLeave();}
  //if (state.code) {printf("!!! state.code is %i\n",state.code);return state.val;}
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$].dup; // !!! dup needed
  Cell[] eargs;
  Cell x0=x.lst[0];
  Cell *px0=&(x.lst[0]);
  while (isa(x0,TList)) {
    x0=abs_eval(x0);
  }
  if (isa(x0,TSymbol)) {
    if (x0.sym[0]=='$') return abs_get_result_from_fun_list(x0.sym);
    x0=abs_resolve_function(x0,args,eargs,px0);
    if (isa(x0,TList)) return x0.lst[0]; // result packed in list
  }
  if (isa(x0,TLfun)) {
    return x0.lfn(args);
  }
  if (isa(x0,TFun)) {
    if (!eargs.length) {
      eargs.length=args.length;
      for (int k;k<args.length;++k) {
        eargs[k]=abs_eval(args[k]);
      }
    }
    return x0.fun(eargs);
  }
  if (isa(x0,TLambda)) {
    Lamb* lam=as_lambda(x0);
    Env* lamenv=abs_mk_lambda_environment(lam,args,environment);
//    printf("******* evaluate lambda\n%.*s\n",pretty_str(lam.expr,0));
    Cell c=abs_evalin(lam.expr,lamenv);
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
void exec_l(string filename) {
  Cell c=lparse(cast(string)std.file.read(filename));
  c.show(true);
  eval(c);
}
void exec_ast(string filename) {
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
void abs_exec_ast(string filename) {
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
  abs_eval(c);
  if (showflag) printf("%.*s\n",pretty_str(c,0));
  if (showflag) show_fun_list();
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
  env_pr(environment);
}
void exec(string fn) {
  base_env=mk_base_env();
  init_libs();
  push_env();
  exec_ast(fn);
}
void abs_exec(string fn) {
  base_env=mk_base_env();
  init_abs_libs();
  push_env();
  abs_exec_ast(fn);
}
void env_info() {
  for (int k=0;k<envstack.length;++k) printf("%p ",envstack[k]);
  printf("[%i] be=%p e=%p\n",envstack.length,base_env,environment);
}
void main(string[] args) {
  string fn;
  if (args.length>1) fn=args[1]~".ast";
  else fn="test.ast";
//  state.code=StC.run;
  if (0) {
    exec(fn);
  } else {
    abs_exec(fn);
  }
//  printf("state.code=%i\n",state.code);
}
