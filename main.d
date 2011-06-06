
//--  (w) Frank F. Hirsch (2011)

/*
*** todo
 - type literals
 - all types global (?)
*/

module main;

import emit_d;
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
import std.format;

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
Cell resolve_symbol_except_ftabs(Cell sym) {
  static if (debf) {debEnter("resolve_symbol_except_ftabs");scope (exit) debLeave();}
  Cell candidate;
  string name=as_symbol(sym);
  Env* e=environment;
  while (e) {
    e=env_find(e,name);
    if (!e) break;
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) return candidate;
    e=e.outer;
  }
  return null_cell();
}
FTabEntry* resolve_name_as_ftab_entry(string name,ref Cell[] args,ref Env* e) {
  static if (debf) {debEnter("resolve_name_as_ftab_entry(%s)",name);scope (exit) debLeave();}
  FTabEntry* candidate_entry;
  Cell candidate;
  e=environment;
  for (;;) {
    //writef("looking up Function '%s' in environment %s\n",name,e);
    if (e) e=env_find(e,name);
    if (!e) {
//      writef("*** Error: Function '%s' lookup failed!\n",name);
      return null;
    }
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) continue;
    candidate_entry=ftab_resolve(candidate.ftab,args,name);
    if (candidate_entry) break;
    e=e.outer;
  }
  return candidate_entry;
}
FTabEntry* resolve_name_as_ftab_entry(string name,ref Cell[] args) {
  Env* e;
  return resolve_name_as_ftab_entry(name,args,e);
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
    for (int k;k<args.length;++k) eargs[k]=eval(args[k]);
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
//---------------- abstract eval helpers
//----------------
string[Type] type_list;
class FunListEntry {
  string     nam;
  FTabEntry* fte;
  Cell[]     par; // parameters
  Cell       fun; // function cell
  Cell       res; // result value
  bool       abt; // aborted
  Env*       env;
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
FunListEntry[string] fun_hash;
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
    static if (1) {
      //writef("*************** function %s\n",fle.nam);
    } else {
      writef("*************** function %s(",fle.nam);
      for (int k=0;k<fle.par.length;++k) {
        writef("%s",types.str(fle.par[k].type));
        if (k+1<fle.par.length) writef(",");
      }
      writef(") : %s\n",types.str(fle.res.type));
    }
    static if (0) {
      writef("%s\n",pretty_str(fle.fun,0));
    }
    if (fle.env !is null) {
      env_pr(fle.env);
    }
  }
}
FunListEntry find_in_fun_list(FTabEntry* fte,Cell[] par) {
  for (int kfl;kfl<fun_list.length;++kfl) {
    FunListEntry fle=fun_list[kfl];
    if (fte!=fle.fte) continue;
    if (par.length!=fle.par.length) continue;
    if (!par.length) return fun_list[kfl];
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
void abs_eval_args(ref Cell[] args,ref Cell[] eargs) {
  if (!eargs.length) {
    eargs.length=args.length;
    for (int k;k<args.length;++k) {
      eargs[k]=abs_eval(args[k]);
    }
  }
}
Cell abs_resolve_function(Cell sym,ref Cell[] args) {
  string lmsg;
  static if (debf) {
    debEnter("abs_resolve_function('"~sym.sym~"')");
    scope (exit) debLeave(frm("%s / %d",lmsg,state.code));
  }
  //writef("abs_resolve_function('%s')\n",sym.sym);
  FTabEntry* entry;
  string name=as_symbol(sym);
  //-- special handling for getters and setters
  if ((name=="dotget") || (name=="dotset")) {
    assert(args.length>1);
    assert(isa(args[1],TString));
    string fieldname=as_string(args[1]);
    string altname=name~"_"~fieldname;
    Cell[] altargs=args.dup;
    remove_element(altargs,1); // remove index element from args
    entry=resolve_name_as_ftab_entry(altname,altargs);
    if (entry) {
      // alternative name entry found
      name=altname;
      args=altargs;
    } else {
      // alternative name entry missing
      Env* env;
      entry=resolve_name_as_ftab_entry(name,args,env);
      if (entry && isa(entry.fun,TLambda)) {
        if (name=="dotset") {
          entry=specialise_dotset(entry,fieldname);
        } else {
          entry=specialise_dotget(entry,fieldname);
        }
//        entry=specialise_accessor(entry,fieldname);
        name=altname;
        args=altargs;
        writefln("### specialised accessor %s%s\n",name,entry.sig);
        Cell ftab_cell=env_putfun(env,name,entry.fun,entry.sig,entry.ret);
        entry=ftab_resolve(ftab_cell.ftab,args,name);
//        ftab_add(ftab,entry.fun,entry.sig,entry.ret);
      }
    }
  } else {
    entry=resolve_name_as_ftab_entry(name,args);
  }
  if (!entry) {
    writef("*** Error: Function '%s' lookup failed!\n",name);
    assert(false);
  }
  //--
//   writef("find %s\n",name);
  FunListEntry fle=find_in_fun_list(entry,args);
  if (fle is null) {
    //-- entry does not exist -> create it
    //writef("!FLE:%s\n",name);
    //writef("*** %s\n",cells.str(entry.fun));
    name=frm("$%s_%d",name,fun_list.length);
    fle=FunListEntry(name,entry,args,entry.fun);
    if (isa(entry.fun,TLambda)) {
      fun_list~=fle;
      sym.sym=name;
      fun_hash[name]=fle;
    }
    call_stack_push(fle);
    Cell h=abs_eval(list_cell([fle.fun]~args));
//    writef("### %s -> [%s] %s\n",name,cells.str(h),cells.str(fle.res));
    if (!(isa(fle.fun,TLambda) || isa(h,TNull))) {
      fle.res=h;
    }
    while (fle.abt) {
      fle.abt=false;
      Cell r=abs_eval(list_cell([fle.fun]~args));
      if (!isa(r,TNull)) fle.res=r;
    }
    call_stack_pop();
  } else {
    //-- entry does exist -> use it
    //writef("FLE:%s (%s)\n",name,fle.nam);
    name=fle.nam;
    if (isa(fle.fun,TLambda)) {
      sym.sym=name;
    }
//    if ((fle.res.type==TAny) || (fle.res.type==TNull)) {
    if (fle.res.type==TAny) {
      //writef("+++++++ Recursion return type unavailable for %s\n",fle.nam);
      fle.abt=true;
      state.code=StC.abt;
      state.val=fle.res;
    }
  }
  lmsg=frm("%s",types.str(fle.res.type));
  return list_cell([fle.res]);
}
Env* abs_mk_lambda_environment(Lamb* lam,Cell[] args) {
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
//          writef("### %s -> %s\n",cells.str(args[ka]),cells.str(eargs[$-1]));
        }
//        writef("### %d\n",eargs.length);
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
//Cell current_x;
Cell abs_eval(Cell x) {
  static if (debf) {debEnter("abs_eval('%s')",cells.str(x));scope (exit) debLeave();}
  evalcell~=x;
  //writef("eval %s\n",pretty_str(x,0));
  scope (exit) evalcell.length=evalcell.length-1;
  //if (state.code) {writef("!!! state.code is %d\n",state.code);return state.val;}
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$];
  Cell[] eargs;
  Cell x0=x.lst[0];
  while (isa(x0,TList)) x0=abs_eval(x0);
  if (isa(x0,TSymbol)) {
    if (x0.sym[0]=='$') return abs_get_result_from_fun_list(x0.sym);
    Cell r=resolve_symbol_except_ftabs(x0);
    if (isa(r,TNull)) {
      abs_eval_args(args,eargs);
      bool accessor=(x0.sym=="dotget") || (x0.sym=="dotset");
      r=abs_resolve_function(x0,eargs);
      if (accessor && (x0.sym[0]=='$')) {
        assert(args.length>1);
        assert(isa(args[1],TString));
        //writefln("*********** DOT %s %s",x0.sym,x);
        remove_element(args,1);
        remove_element(eargs,1);
        x.set(list_cell(x0~args));
      } else {
        //writefln("*********** NOT %s %s",x0.sym,x);
      }
    }
    x0=r;
    if (isa(x0,TList)) return x0.lst[0]; // result packed in list
  }
  if (isa(x0,TLfun)) {
    return x0.lfn(args);
  }
  if (isa(x0,TFun)) {
    abs_eval_args(args,eargs);
    return x0.fun(eargs);
  }
  if (isa(x0,TLambda)) {
    abs_eval_args(args,eargs);
    Lamb* lam=as_lambda(x0);
    Env* lamenv=abs_mk_lambda_environment(lam,args);
//    writef("******* evaluate lambda\n%s\n",pretty_str(lam.expr,0));
    FunListEntry tocs=call_stack_top();
    if (tocs.env is null) tocs.env=lamenv;
    Cell c=abs_evalin(lam.expr,lamenv);
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
  Cell c=lparse(cast(string)std.file.read(filename));
  c.show(true);
  eval(c);
}
void exec_ast(string filename) {
  bool showflag=!true;
  bool reorder=true;
  Cell c=parse_file_to_cell(filename);
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
  Cell run=list_cell([symbol_cell("main")]);
  push_env();
  eval(c);
  eval(run);
  pop_env();
//  push_env();eval(c);eval(run);pop_env();
//  if (showflag) c.show(true);
}
void abs_exec_ast(string filename) {
  bool showflag=!true;
  bool test=true;
  Cell root=parse_file_to_cell(filename);
  if (showflag) root.show(true);
  //
  reduce_seq_of_one(root);
  //insert_outer_seq_in_defuns(root);
  //if (test) return;
  //if (root !is null) return;
  //writef("%s\n",pretty_str(root,0));
  operators_to_front(root,["defun","def"]);
  move_typedefs_to_root(root);
  operator_to_front(root,"supertype");
  operator_to_front(root,"aliastype");
  operator_to_front(root,"deftype");
  replace_anonymous_structs_and_unions(root);
  if (showflag) writef("%s\n",pretty_str(root,0));
  static if (1) {
    writef("%s\n",pretty_str(root,0));
    abs_eval(root);
    abs_eval(parse_string_to_cell("main();"));
    if (showflag) writef("%s\n",pretty_str(root,0));
    if (showflag) show_fun_list();
    emit_d_main(root,fun_list,"out.d");
    //writef("%s\n",pretty_str(root,0));
  }
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
//   push_env();
  abs_exec_ast(fn);
}
void env_info() {
  for (int k=0;k<envstack.length;++k) writef("%p ",envstack[k]);
  writef("[%d] be=%p e=%p\n",envstack.length,base_env,environment);
}
void main(string[] args) {
  string fn;
//  state.code=StC.run;
  if (0) {
    if (args.length>1) fn=args[1]~".ast";
    else fn="tests.ast";
    exec(fn);
  } else {
    if (args.length>1) fn=args[1]~".ast";
    else fn="test.ast";
    abs_exec(fn);
  }
//  writef("state.code=%d\n",state.code);
}
