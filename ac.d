
//--  (w) Frank F. Hirsch (2011)

// todo: more than you can shake a stick at

module ac;

import eval_helpers;
import emit_d;
import debg;
import ablibs;
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

const bool debf=debflag && 0;

const bool require_declaration_before_use=true;

enum StC {run=0,ret,brk,cnt,abt};

struct State {
  StC    code;
  Cell   val;
}
State state;

Env* base_env;

int depth=0;
int maxdepth=0;
Cell[] evalcell;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- abstract eval helpers
//----------------
int[string] fun_index;
int next_fun_index(string n) {
  if (n in fun_index) return fun_index[n]=fun_index[n]+1;
  return fun_index[n]=0;
}
FTabEntry*[string] dollar_res;
int[FTabEntry*] fun_flag;
FTabEntry*[] call_stack;
FTabEntry* call_stack_top() {
  assert(call_stack.length,"Abstract interpreter error: Call stack empty.");
  return call_stack[$-1];
}
void call_stack_push(FTabEntry* e) {
  call_stack~=e;
}
FTabEntry* call_stack_pop() {
  FTabEntry* e=call_stack_top();
  call_stack.length=call_stack.length-1;
  return e;
}
void abs_eval_args(ref Cell[] args,ref Cell[] eargs) {
  if (!eargs.length) {
    eargs.length=args.length;
    for (int k;k<args.length;++k) {
      eargs[k]=abs_eval(args[k]);
//      args[k].ann["ret"]=type_cell(eargs[k].type);
//      unalias_type_of(eargs[k]);
    }
  }
}
Env* abs_mk_lambda_environment(Lamb* lam,Cell[] args) {
  static if (debf) {debEnter("abs_mk_lambda_environment");scope (exit) debLeave();}
//  writefln("0 env for %s %s %s",lam.pars,lam.expr,lambda_cell(lam));
  Env* lamenv=lam.env;//env_clone(lam.env);
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
//  writefln("1 env for %s %s %s",lam.pars,lam.expr,lambda_cell(lam));
  return lamenv;
}
Cell abs_resolve_function(Cell sym,ref Cell[] args,Cell x) {
  string debug_leave_message;
  static if (debf) {
    debEnter("abs_resolve_function('%s',%s)",sym.sym,args);
    scope (exit) debLeave(frm("%s / %d",debug_leave_message,state.code));
  }
//  writef("--------------- abs_resolve_function('%s')\n",sym.sym);
  FTabEntry* entry;
  Env* ftab_env;
  string name=as_symbol(sym);
  //-- special handling for getters and setters
  if ((name=="dotget") || (name=="dotset")) {
    assert(args.length>1);
    assert(isa(args[1],TString));
    string fieldname=as_string(args[1]);
    string altname=name~"_"~fieldname;
    Cell[] altargs=args.dup;
    remove_element(altargs,1); // remove index element from altargs
    entry=resolve_name_as_ftab_entry(altname,altargs,ftab_env);
    if (entry) {
      // alternative name entry found
      name=altname;
      args=altargs;
    } else {
      // alternative name entry missing
      entry=resolve_name_as_ftab_entry(name,args,ftab_env);
      if (entry && isa(entry.fun,TLambda)) {
        if (name=="dotset") {
          entry=specialise_dotset(entry,fieldname);
        } else {
          entry=specialise_dotget(entry,fieldname);
        }
        args=altargs;
        name=altname;
        Cell ftab_cell=env_putfun(ftab_env,name,entry.fun,entry.sig,TAny);
        entry=ftab_resolve(ftab_cell.ftab,args,name);
      }
    }
    //printf("entry=%p\n",cast(void*)entry);
  } else {
    entry=resolve_name_as_ftab_entry(name,args,ftab_env);
  }
  if (!entry) {
    writef("*** Error: Function '%s' lookup failed!\n",name);
    assert(false);
  }
  bool perfect_match=signature_matches_perfectly(entry.sig,args);
//  writefln("--> %s",perfect_match);
  if (!entry.nam.length) entry.nam=name;
  if (entry.sig.ses.length>args.length) {
    //writef("appending to %s parameters %s",name,x.lst);
    for (int k=args.length;k<entry.sig.ses.length;++k) {
      x.lst~=entry.sig.ses[k].defv;
    }
    //writef(" -> %s\n",x.lst);
  }
  if (!perfect_match) {
//    writefln("+++ not perfect match : %s",name);
    entry=entry.clone();
    for (int k;k<entry.sig.ses.length;++k) {
      if (k>=args.length) break;
      entry.sig.ses[k].type=args[k].type;
    }
    for (int k=entry.sig.ses.length;k<args.length;++k) {
      SigElement se;
      se.defv=null_cell();
      se.name="";
      se.type=args[k].type;
      entry.sig.ses~=se;
    }
    entry.sig.open.cell=null;
    entry.ret=TAny;
    env_putfun(ftab_env,name,entry);
  }
  //--
  if ((entry.ret==TAny) || (!isa(entry.fun,TLambda))) {
    if (isa(entry.fun,TLambda)) {
//      writefln("*** visitation handling 0: %s is lambda",entry.nam);
      if (entry.nam[0]!='$') {
        // generate new unique callee name for this signature
        entry.nam="$"~entry.nam~"_"~toString(next_fun_index(entry.nam));
      }
      // change call site symbol to new name
      sym.sym=entry.nam;
      dollar_res[sym.sym]=entry;
    }
    //-- return type unknown
    if (!(entry in fun_flag)) fun_flag[entry]=fun_flag.length-1; // aa length is always one too big, it seems
    call_stack_push(entry);
    Cell h=abs_eval(list_cell([entry.fun]~args));
    if ((entry.ret==TAny) || (!isa(entry.fun,TLambda))) entry.ret=h.type;
    assert(!(entry.ret==TAny));
    call_stack_pop();
  } else {
    //-- return type known
    if (isa(entry.fun,TLambda)) {
//      writefln("*** visitation handling 1: %s is lambda",entry.nam);
      if (entry.nam[0]!='$') {
        // generate new unique callee name for this signature
        entry.nam="$"~entry.nam~"_"~toString(next_fun_index(entry.nam));
      }
      // change call site symbol to new name
      sym.sym=entry.nam;
      dollar_res[sym.sym]=entry;
    }
  }
  debug_leave_message=frm("%s",types.str(entry.ret));
  return list_cell([new_cell(entry.ret)]);
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
  if (Cell* rtc=("res" in x.ann)) {
    //writefln("cutting short %s -> %s",x,*rtc);
    return *rtc;
  }
  Cell res=abs_eval_sub(x);
  if (!state.code) x.ann["res"]=res;
  return res;
}
Cell abs_eval_sub(Cell x) {
  static if (debf) {debEnter("abs_eval('%s')",cells.str(x));scope (exit) debLeave();}
  evalcell~=x;
  //writef("eval %s\n",pretty_str(x,0));
  scope (exit) {evalcell.length=evalcell.length-1;}
  if (state.code) {/*writef("!!! state.code is %d\n",state.code);*/return state.val;}
  if (isa(x,TSymbol)) return env_get(environment,x.sym);
  if (!isa(x,TList)) return x;
  if (!x.lst.length) return x;
  Cell[] args=x.lst[1..$];
  Cell[] eargs;
  Cell x0=x.lst[0];
  while (isa(x0,TList)) x0=abs_eval(x0);
  if (isa(x0,TSymbol)) {
    if (x0.sym[0]=='$') {
      // $ is mark we have already visited this call site, so we can break recursions
//      writefln("*** visitation handling 2: symbol %s has $",x0.sym);
      Cell r=new_cell(dollar_res[x0.sym].ret);
      if (isa(r,TAny)) {
        state.code=StC.abt;
        state.val=r;
      }
      return r;
    }
    Cell r=resolve_symbol_except_ftabs(x0);
    if (isa(r,TNull) || isa(r,TType)) {
      bool dotget=(x0.sym=="dotget");
      bool dotset=(x0.sym=="dotset");
      if (dotset) {
        args[0]=list_cell([symbol_cell("&")]~args[0]);
      }
//      writefln("/// %s args=%s",x0,args);
      abs_eval_args(args,eargs);
      if (state.code) {/*writef("!!!a state.code is %d\n",state.code);*/return state.val;}
//      writefln("/// %s eargs=%s",x0,eargs);
      r=abs_resolve_function(x0,eargs,x);
      if ((dotget || dotset) && (x0.sym[0]=='$')) {
        // is accessor call site with visitation mark
        assert(args.length>1);
        assert(isa(args[1],TString));
//        writefln("*** visitation handling 3: accessor %s %s",x0.sym,x);
        remove_element(args,1);
        remove_element(eargs,1);
        x.set(list_cell(x0~args));
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
    FTabEntry* fte=call_stack_top();
    fte.env=lamenv;
    Cell c=abs_evalin(lam.expr,lamenv);
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
void abs_exec_ast(string filename) {
  bool showflag=!true;
  bool test=true;
  Cell root=parse_sexpr_file(filename);
  if (showflag) root.show(true);
  //
  reduce_seq_of_one(root);
  //insert_outer_seq_in_defuns(root);
  //if (test) return;
  //if (root !is null) return;
  writef("%s\n",pretty_str(root,0));
  operators_to_front(root,["defun","def"]);
  move_typedefs_to_root(root);
  operator_to_front(root,"supertype");
  operator_to_front(root,"deftype");
  replace_alias_types(root);
  //remove_empty_lists(root);
  if (showflag) writef("%s\n",pretty_str(root,0));
  writef("%s\n",pretty_str(root,0));
  static if (1) {
    abs_eval(root);
    abs_eval(parse_sexpr("(main)"));
    if (showflag) writef("%s\n",pretty_str(root,0));
    //if (showflag) show_fun_flag();
    FTabEntry*[] fun_list;
    fun_list.length=fun_flag.length;
    int k;
    foreach (key;fun_flag.keys) {
//      writefln("key %s/%s:%s",k++,fun_flag.length,fun_flag[key]);
      fun_list[fun_flag[key]]=key;
    }
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
  init_types();
  return e;
}
void dump_info() {
  env_pr(environment);
}
void abs_exec(string base_filename) {
  base_env=mk_base_env();
  init_abs_libs();
//  push_env();
  abs_exec_ast(base_filename~".l");
}
void env_info() {
  for (int k=0;k<envstack.length;++k) writef("%p ",envstack[k]);
  writef("[%d] be=%p e=%p\n",envstack.length,base_env,environment);
}
void main(string[] args) {
  string base_filename;
  if (args.length>1) base_filename=args[1];
//  else base_filename="ctests";
  else base_filename="test";
  abs_exec(base_filename);
}
