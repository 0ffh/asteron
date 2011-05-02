module libs;

import debg;
import main;
import cells;
import types;
import signatures;
import environments;
import utils;
import std.math;
import std.stdio;

const bool debf=debflag;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- core functions
//----------------

Cell op_if(Cell[] args) {
  static if (debf) {debEnter("[if]");scope (exit) debLeave();}
  if (args.length==2) {
    return (istrue(eval(args[0])))?(eval(args[1])):(null_cell());
  }
  if (args.length==3) {
    return (istrue(eval(args[0])))?(eval(args[1])):(eval(args[2]));
  }
  assert(false);
}
Cell op_switch(Cell[] args) {
  static if (debf) {debEnter("[switch]");scope (exit) debLeave();}
  Cell c=eval(args[0]);
  int k=1;
  while ((k+1)<args.length) {
    Cell exp=list_cell([symbol_cell("=="),c,args[k]]);
    if (istrue(eval(exp))) break;
    k=k+2;
  }
  k=k+1;
  while (k<args.length) {
    c=eval(args[k]);
    if (state.code==StC.brk) {
      state.code=StC.run;
      break;
    }
    k=k+2;
  }
//  state.code=StC.run;
  return null_cell();
}
Cell op_for(Cell[] args) {
  static if (debf) {debEnter("[for]");scope (exit) debLeave();}
  assert(args.length==4);
  push_env(); // we get our own scope
  Cell c;
  for (eval(args[0]);istrue(eval(args[1]));eval(args[2])) {
    c=eval(args[3]);
    if (state.code==StC.brk) {state.code=StC.run;break;}
    if (state.code==StC.cnt) {state.code=StC.run;continue;}
  }
  pop_env();
  return c;
}
Cell op_while(Cell[] args) {
  static if (debf) {debEnter("[while]");scope (exit) debLeave();}
  assert(args.length==2);
  push_env(); // we get our own scope
  Cell c;
  while (istrue(eval(args[0]))) {
    c=eval(args[1]);
    if (state.code==StC.brk) {state.code=StC.run;break;}
    if (state.code==StC.cnt) {state.code=StC.run;continue;}
  }
  //state.brk=0;
  pop_env();
  return c;
}
Cell op_dowhile(Cell[] args) {
  static if (debf) {debEnter("[dowhile]");scope (exit) debLeave();}
  assert(args.length==2);
  push_env(); // we get our own scope
  Cell c;
  do {
    c=eval(args[0]);
    if (state.code==StC.brk) {state.code=StC.run;break;}
    if (state.code==StC.cnt) {state.code=StC.run;continue;}
  } while (istrue(eval(args[1])));
//  state.brk=0;
  pop_env();
  return c;
}
Cell op_assign(Cell[] args) {
  static if (debf) {debEnter("[assign]");scope (exit) debLeave();}
  assert(args.length==2);
  string id=as_symbol(args[0]);
  Env* e=env_find(environment,id);
  static if (require_declaration_before_use) {
    assert(e !is null,"Undeclared identifier "~id);
  } else {
    if (e is null) e=environment; // lenient
  }
  return env_put(e,id,eval(args[1]));
}
Cell op_def(Cell[] args) {
  static if (debf) {debEnter("[def]");scope (exit) debLeave();}
  //- cases:
  //   (def type name)
  //   (def type name value)
  //-
  Type type;
  string name;
  Cell value;
  assert(args.length>1);
  //args[0].show();
  type=as_type(eval(args[0]));
  name=as_symbol(args[1]);
  if (args.length>2) {
    assert(args.length==3);
    //args[2].show();
    value=eval(args[2]);
  } else {
    //writef("new %s\n",types.str(type));
    value=new_cell(type);
  }
  //-
  if (env_find(environment,name)==environment) {
    writef("Error: Symbol '%s' is already defined in this scope!\n",name);
    assert(false);
  }
  return env_put(environment,name,value);
}
Cell op_deftype(Cell[] args) {
  static if (debf) {debEnter("[deftype]");scope (exit) debLeave();}
  assert(args.length==2);
  string name=as_symbol(args[0]);
  Type typ=type_deftype(name,type(args[1]));
  Cell val=type_cell(typ);
  //writef("deftype %s / %s\n",name,types.str(type(args[1])));
  return env_put(environment,name,val);
}
Cell op_aliastype(Cell[] args) {
  static if (debf) {debEnter("[aliastype]");scope (exit) debLeave();}
  assert(args.length==2);
  string name=as_symbol(args[0]);
  Type typ=type_aliastype(name,type(args[1]));
  Cell val=type_cell(typ);
  //writef("deftype %s / %s\n",name,types.str(type(args[1])));
  return env_put(environment,name,val);
}
Cell op_supertype(Cell[] args) {
  static if (debf) {debEnter("[supertype]");scope (exit) debLeave();}
  assert(args.length>=2);
  string name=as_symbol(args[0]);
  Type[] st;
  for (int k=1;k<args.length;++k) st~=type(args[k]);
  Type typ=type_supertype(name,st);
  Cell val=type_cell(typ);
  //writef("supertype %s / %s\n",name,types.str(type(args[1])));
  return env_put(environment,name,val);
}
Cell op_defun(Cell[] args) {
  static if (debf) {debEnter("[defun]");scope (exit) debLeave();}
  assert(args.length>=2);
  string name=as_symbol(args[0]);
  Cell val=eval(list_cell(symbol_cell("function")~args[1..$]));
  Signature sig=parameter_cell2signature(args[1]);
  return env_putfun(environment,name,val,sig,TAny);
}
Cell op_quote(Cell[] args) {
  static if (debf) {debEnter("[quote]");scope (exit) debLeave();}
  assert(args.length==1);
  return args[0];
}
Cell op_function(Cell[] args) {
  static if (debf) {debEnter("[fun]");scope (exit) debLeave();}
  assert(args.length>=2); // args[0]:vars args[1..$]:expressions
  // collect parameter names
  Cell[] pars=as_list(args[0]);
  // create and return lambda cell
  if (args.length>2) {
    // more than one expression -> implicit sequence
    return lambda_cell(mk_lamb(list_cell(symbol_cell("seq")~args[1..$]),pars,mk_env(environment)));
  } else {
    return lambda_cell(mk_lamb(args[1],pars,mk_env(environment)));
  }
}
Cell op_seq(Cell[] args) {
  static if (debf) {debEnter("[seq]");scope (exit) debLeave();}
  Cell res;
  for (int k=0;k<args.length;++k) res=eval(args[k]);
  return res;
}
Cell op_scope(Cell[] args) {
  static if (debf) {debEnter("[scope]");scope (exit) debLeave();}
  if (args.length==1) {
    push_env(); // we get our own scope
    Cell res=eval(args[0]);
    pop_env();
    return res;
  }
  if (args.length==2) {
    Env* e=mk_env(environment);
    Cell ce=env_cell(e);
    env_put(environment,as_symbol(args[0]),ce);
    push_env(e); // we get our own scope
    Cell res=eval(args[1]); // sequence in new environment
    pop_env();
    return res;
  }
  assert(false,"scope got unexpected number of arguments");
}
Cell op_break(Cell[] args) {
  static if (debf) {debEnter("[break]");scope (exit) debLeave();}
  state.code=StC.brk;
  return null_cell();
}
Cell op_continue(Cell[] args) {
  static if (debf) {debEnter("[continue]");scope (exit) debLeave();}
  state.code=StC.cnt;
  return null_cell();
}
Cell op_return(Cell[] args) {
  static if (debf) {debEnter("[return]");scope (exit) debLeave();}
  if (args.length) {
    Cell c=eval(args[0]);
    state.code=StC.ret;
    state.val=c;
    return c;
  } else {
    return null_cell();
  }
}
Cell op_ftab_set(Cell[] args) {
  static if (debf) {debEnter("[op_ftab_set]");scope (exit) debLeave();}
  assert(false,"function table setter not implemented");
  assert(args.length==3);
  // set env key value
  env_put(as_env(args[0]),as_str(args[1]),args[2]);
  return args[2];
}
Cell op_ftab_get(Cell[] args) {
  static if (debf) {debEnter("[op_ftab_get]");scope (exit) debLeave();}
  assert(args.length);
  // get env key
  Type[] targs;
  for (int k=1;k<args.length;++k) {
    targs~=as_type(args[k]);
  }
  //return resolve_function(as_ftab(args[0]),targs);
  FTabEntry* fte=ftab_resolve(as_ftab(args[0]),targs);
  if (fte) return fte.fun;
  return null_cell();
}
Cell op_call(Cell[] args) {
  static if (debf) {debEnter("[call]");scope (exit) debLeave();}
  assert(args.length>1);
  //-- get object
  Cell obj=eval(args[0]);
  if (is_assoc_type(obj.type)) {
    //-- make object environment
    Env* objenv=mk_env(environment);
    objenv.inner=obj.asc.inner;
    objenv.inner["this"]=obj;
    //-- get lambda
    Cell fun=evalin(args[1],objenv);
    assert(fun.type==TLambda);
    //-- make lambda environment
    Env* lamenv=mk_lambda_environment(fun.lam,args[2..$],environment);
    //-- relink environments
    objenv.outer=lamenv.outer;
    lamenv.outer=objenv;
    //-- eval lambda expression
    return evalin(fun.lam.expr,lamenv);
  }
  if (isa(obj,TEnv)) {
    for (int k=2;k<args.length;++k) args[k]=eval(args[k]);
    return evalin(list_cell(args[1..$]),as_env(obj));
  }
  args[0]=args[1];
  args[1]=obj;
  return eval(list_cell(args));
}
Cell op_prenv(Cell[] args) {
  env_pr(environment);
  return assoc_cell(environment.inner);
}
void init_libs() {
  Env* env=environment;
  assert(types_initialised);
  // lazy functions
  env_put(env,"=",lfun_cell(&op_assign));
  env_put(env,"switch",lfun_cell(&op_switch));
  env_put(env,"if",lfun_cell(&op_if));
  env_put(env,"for",lfun_cell(&op_for));
  env_put(env,"while",lfun_cell(&op_while));
  env_put(env,"dowhile",lfun_cell(&op_dowhile));
  env_put(env,"def",lfun_cell(&op_def));
  env_put(env,"defun",lfun_cell(&op_defun));
  env_put(env,"deftype",lfun_cell(&op_deftype));
  env_put(env,"aliastype",lfun_cell(&op_aliastype));
  env_put(env,"supertype",lfun_cell(&op_supertype));
  env_put(env,"quote",lfun_cell(&op_quote));
  env_put(env,"function",lfun_cell(&op_function));
  env_put(env,"seq",lfun_cell(&op_seq));
  env_put(env,"scope",lfun_cell(&op_scope));
  env_put(env,"return",lfun_cell(&op_return));
  env_put(env,"break",lfun_cell(&op_break));
  env_put(env,"continue",lfun_cell(&op_continue));
  env_put(env,"call",lfun_cell(&op_call));
  env_put(env,"prenv",lfun_cell(&op_prenv));
  // library functions
  add_libs(env);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- more functions
//----------------

Cell op_tron(Cell[] args) {
  static if (debf) {debEnter("[tron()]");scope (exit) debLeave();}
  trace=true;
  return null_cell();
}
Cell op_troff(Cell[] args) {
  static if (debf) {debEnter("[troff()]");scope (exit) debLeave();}
  trace=false;
  return null_cell();
}
Cell op_add_int_int(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  return int_cell(as_int(args[0])+as_int(args[1]));
}
Cell op_add_int_float(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  return float_cell(as_int(args[0])+as_float(args[1]));
}
Cell op_add_float_int(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])+as_int(args[1]));
}
Cell op_add_float_float(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])+as_float(args[1]));
}
Cell op_neg_int(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return int_cell(-as_int(args[0]));
}
Cell op_neg_float(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return float_cell(-as_float(args[0]));
}
Cell op_sub_int_int(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return int_cell(as_int(args[0])-as_int(args[1]));
}
Cell op_sub_int_float(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return float_cell(as_int(args[0])-as_float(args[1]));
}
Cell op_sub_float_int(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])-as_int(args[1]));
}
Cell op_sub_float_float(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])-as_float(args[1]));
}
Cell op_mul_int_int(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  return int_cell(as_int(args[0])*as_int(args[1]));
}
Cell op_mul_int_float(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  return float_cell(as_int(args[0])*as_float(args[1]));
}
Cell op_mul_float_int(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])*as_int(args[1]));
}
Cell op_mul_float_float(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])*as_float(args[1]));
}
Cell op_div_int_int(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  return int_cell(as_int(args[0])/as_int(args[1]));
}
Cell op_div_int_float(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  return float_cell(as_int(args[0])/as_float(args[1]));
}
Cell op_div_float_int(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])/as_int(args[1]));
}
Cell op_div_float_float(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  return float_cell(as_float(args[0])/as_float(args[1]));
}
Cell op_less(Cell[] args) {
  static if (debf) {debEnter("[<]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(as_number(args[0])<as_number(args[1]));
}
Cell op_greater(Cell[] args) {
  static if (debf) {debEnter("[>]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(as_number(args[0])>as_number(args[1]));
}
Cell op_less_equal(Cell[] args) {
  static if (debf) {debEnter("[<=]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(as_number(args[0])<=as_number(args[1]));
}
Cell op_greater_equal(Cell[] args) {
  static if (debf) {debEnter("[>=]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(as_number(args[0])>=as_number(args[1]));
}
int op_equal_sub(Cell a,Cell b) {
  if (!type_equal(a.type,b.type)) return 0;
  if (a.type==TInt) return (as_int(a)==as_int(b));
  if (a.type==TFloat) return (as_float(a)==as_float(b));
  if (a.type==TString) return (as_str(a)==as_str(b));
  if (is_array_type(a.type)) {
    if (a.arr.inner.length!=b.arr.inner.length) return 0;
    for (int k=0;k<a.arr.inner.length;++k) {
      if (!op_equal_sub(a.arr.inner[k],b.arr.inner[k])) return 0;
    }
    return 1;
  }
//   writef("\n%s [%s] ?= %s [%s]\n",cells.str(a),types.str(a.type),cells.str(b),types.str(b.type));
  if (a.type==TType) return (type(a.typ)==type(b.typ));
  return (a==b);
}
Cell op_equal(Cell[] args) {
  static if (debf) {debEnter("[==]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(op_equal_sub(args[0],args[1]));
}
Cell op_not_equal(Cell[] args) {
  static if (debf) {debEnter("[!=]");scope (exit) debLeave();}
  assert(args.length==2);
  return int_cell(!as_int(op_equal(args)));
}
Cell op_sqrt(Cell[] args) {
  static if (debf) {debEnter("[sqrt]");scope (exit) debLeave();}
  assert(args.length==1);
  return float_cell(sqrt(as_number(args[0])));
}
Cell op_car(Cell[] args) {
  static if (debf) {debEnter("[car]");scope (exit) debLeave();}
  assert(args.length==1);
  Cell[] help=as_list(args[0]);
  if (!help.length) return args[0];
  return help[0];
}
Cell op_cdr(Cell[] args) {
  static if (debf) {debEnter("[cdr]");scope (exit) debLeave();}
  assert(args.length==1);
  Cell[] help=as_list(args[0]);
  if (help.length<2) return list_cell();
  return list_cell(help[1..$].dup);
}
Cell op_cons(Cell[] args) {
  static if (debf) {debEnter("[cons]");scope (exit) debLeave();}
  assert(args.length==2);
  if (isa(args[1],TList)) {
    return list_cell([args[0]]~args[1].lst);
  } else {
    return list_cell([args[0]]~args[1]);
  }
}
Cell op_append(Cell[] args) {
  static if (debf) {debEnter("[append]");scope (exit) debLeave();}
  assert(args.length==2);
  return list_cell(as_list(args[0])~as_list(args[1]));
}
Cell op_list(Cell[] args) {
  static if (debf) {debEnter("[list]");scope (exit) debLeave();}
  return list_cell(args);
}
Cell op_listp(Cell[] args) {
  static if (debf) {debEnter("[list?]");scope (exit) debLeave();}
  assert(args.length==1);
  return int_cell(isa(args[0],TList));
}
Cell op_length(Cell[] args) {
  static if (debf) {debEnter("[length]");scope (exit) debLeave();}
  assert(args.length==1);
  Cell arg=args[0];
  while (is_def_type(arg.type)) arg.type=get_def_subtype(arg.type);
  if (arg.type==TList) return int_cell(arg.lst.length);
  if (arg.type==TString) return int_cell(arg.str.length);
  if (arg.type==TEnv) return int_cell(arg.env.inner.length);
  if (is_assoc_type(arg.type)) return int_cell(arg.asc.inner.length);
  if (is_array_type(arg.type)) return int_cell(arg.arr.inner.length);
  /* -- all catched by default
  if (arg.type==TFun) return int_cell(1);
  if (arg.type==TLfun) return int_cell(1);
  if (arg.type==TInt) return int_cell(1);
  if (arg.type==TFloat) return int_cell(1);
  if (arg.type==TSymbol) return int_cell(1);
  if (arg.type==TNull) return int_cell(1);
  if (arg.type==TLambda) return int_cell(1);
  */
  return int_cell(1);
}
Cell op_symbolp(Cell[] args) {
  static if (debf) {debEnter("[symbol?]");scope (exit) debLeave();}
  assert(args.length==1);
  return int_cell(isa(args[0],TSymbol));
}
Cell op_nullp(Cell[] args) {
  static if (debf) {debEnter("[null?]");scope (exit) debLeave();}
  assert(args.length==1);
  return int_cell(!(as_list(args[0]).length));
}
Cell op_tostr(Cell[] args) {
  static if (debf) {debEnter("[tostr]");scope (exit) debLeave();}
  if (!args.length) return string_cell("");
  string s;
  for (int k=0;k<args.length;++k) {
    if (k) s~=" ";
    if (isa(args[k],TList)) {
      s~=frm("%s",cells.str(args[k],1));
    } else {
      s~=frm("%s",cells.str(args[k],0));
    }
  }
  return string_cell(s);
}
Cell op_pr(Cell[] args) {
  static if (debf) {debEnter("[pr]");scope (exit) debLeave();}
  if (!args.length) return int_cell(0);
  for (int k=0;k<args.length;++k) {
    if (k) writef(" ");
    if (isa(args[k],TList)) {
      writef("%s",cells.str(args[k],1));
    } else {
      writef("%s",cells.str(args[k],0));
    }
  }
  return int_cell(args.length);
}
Cell op_prln(Cell[] args) {
  static if (debf) {debEnter("[prln]");scope (exit) debLeave();}
  Cell c=op_pr(args);
  writef("\n");
  return c;
}
Cell op_tic(Cell[] args) {
  static if (debf) {debEnter("[tic]");scope (exit) debLeave();}
  tic();
  return list_cell();
}
Cell op_toc(Cell[] args) {
  static if (debf) {debEnter("[toc]");scope (exit) debLeave();}
  float t=toc();
  writef("%.3fs\n",t);
  return float_cell(t);
}
Cell op_new_object(Cell[] args) {
  static if (debf) {debEnter("[new_object]");scope (exit) debLeave();}
  Cell c=assoc_cell_from_subtype(TAny);
  for (int k=0;(k+1)<args.length;k+=2) c.asc.inner[as_str(args[k])]=args[k+1];
//  c.asc.inner["this"]=c;
  return c;
}
Cell op_assoc_get(Cell[] args) {
  static if (debf) {debEnter("[op_assoc_get]");scope (exit) debLeave();}
  assert(args.length==2);
  // get assoc key
  try {
    return args[0].asc.inner[args[1].str];
  } catch {
    return null_cell();
  }
}
Cell op_assoc_set(Cell[] args) {
  static if (debf) {debEnter("[op_assoc_set]");scope (exit) debLeave();}
  assert(args.length==3);
  // put assoc key value
  return args[0].asc.inner[args[1].str]=args[2];
}
Cell op_env_get(Cell[] args) {
  static if (debf) {debEnter("[op_env_get]");scope (exit) debLeave();}
  assert(args.length==2);
  // get env key
  return env_get(as_env(args[0]),as_str(args[1]));
}
Cell op_env_set(Cell[] args) {
  static if (debf) {debEnter("[op_env_set]");scope (exit) debLeave();}
  assert(args.length==3);
  // set env key value
  env_put(as_env(args[0]),as_str(args[1]),args[2]);
  return args[2];
}
Cell op_new_array(Cell[] args) {
  static if (debf) {debEnter("[new_array]");scope (exit) debLeave();}
  Cell c=array_cell();
  for (int k=0;k<args.length;++k) c.arr.inner~=args[k];
  if (args.length) {
    Type t=args[0].type;
    for (int k=1;k<args.length;++k) if (args[k].type!=t) {
      //writef("created %s %s\n",types.str(c.type),cells.str(c));
      return c;
    }
    c.type=array_type_from_subtype(t);
  }
  //writef("created %s %s\n",types.str(c.type),cells.str(c));*/
  return c;
}
Cell op_array_cat(Cell[] args) {
  static if (debf) {debEnter("[array_cat]");scope (exit) debLeave();}
  assert(args.length==2);
  if (!is_array_type(args[0].type)) assert(false);
  if (is_array_type(args[1].type)) {
    return array_cell(args[0].arr.inner~args[1].arr.inner);
  } else {
    return array_cell(args[0].arr.inner~args[1]);
  }
}
Cell op_string_cat(Cell[] args) {
  static if (debf) {debEnter("[string_cat]");scope (exit) debLeave();}
  assert(args.length==2);
  assert(isa(args[0],TString) && isa(args[1],TString));
  return string_cell(args[0].str~args[1].str);
}
Cell op_array_get(Cell[] args) {
  static if (debf) {debEnter("[array_get]");scope (exit) debLeave();}
  assert(args.length==2);
  Cell arr=args[0];
  if (!is_array_type(arr.type)) assert(false);
  int idx=cast(int)(as_number(args[1]));
  assert(arr.arr.inner.length>idx,"Array index out of bounds");
  return arr.arr.inner[idx];
}
Cell op_array_set(Cell[] args) {
  static if (debf) {debEnter("[array_set]");scope (exit) debLeave();}
  assert(args.length==3);
  Cell arr=args[0];
  if (!is_array_type(arr.type)) assert(false,"Variable is not an array");
  /*
  if (!type_matches(get_array_subtype(arr.type),args[2].type)) {
    writef("[array]=%s [element]=%s\n",types.str(arr.type),types.str(args[2].type));
    assert(false,"Type error in element assignment");
  }
  */
  int idx=cast(int)(as_number(args[1]));
  assert(arr.arr.inner.length>idx,"Array index out of bounds");
  return (arr.arr.inner[idx]=args[2]);
}
// op_array_resize(array,int)
Cell op_array_resize(Cell[] args) {
  static if (debf) {debEnter("[array_resize]");scope (exit) debLeave();}
  Cell arr=args[0];
  if (!is_dynamic_array_type(arr.type)) assert(false,"Resize works on dynamic arrays only");
  //writef("resize %s\n",types.str(arr.type));
  Type subtyp=get_array_subtype(arr.type);
  //writef("resize %s[]\n",types.str(subtyp));
  int newlen=cast(int)(as_number(args[1]));
  int oldlen=arr.arr.inner.length;
  arr.arr.inner.length=newlen;
  for (int k=oldlen;k<newlen;++k) arr.arr.inner[k]=new_cell(subtyp);
  return arr;
}
Cell op_new__string(Cell[] args) {
  static if (debf) {debEnter("[new(string)]");scope (exit) debLeave();}
  return new_cell(args[0].str);
}
Cell op_new__type(Cell[] args) {
  static if (debf) {debEnter("[new(type)]");scope (exit) debLeave();}
  return new_cell(as_type(args[0]));
//  return new_cell(cells.str(*args[0].typ));
}
Cell op_alloc(Cell[] args) {
  static if (debf) {debEnter("[alloc(type)]");scope (exit) debLeave();}
  Cell c=new_cell(as_type(args[0]));
  return ref_cell_on_heap(c);
}
Cell op_typeof(Cell[] args) {
  static if (debf) {debEnter("[typeof(any)]");scope (exit) debLeave();}
  return type_cell(args[0].type);
}
Cell op_unpack(Cell[] args) {
  static if (debf) {debEnter("[unpack(any)]");scope (exit) debLeave();}
  Cell c=args[0].clone();
  c.type=get_def_subtype(c.type);
  return c;
}
Cell op_pack(Cell[] args) {
  static if (debf) {debEnter("[pack(any,type)]");scope (exit) debLeave();}
  Cell c=args[0].clone();
  c.type=as_type(args[1]);
  return c;
}
Cell op_array(Cell[] args) { // (array type) -> type
  static if (debf) {debEnter("[array]");scope (exit) debLeave();}
  Type t;
  if (args.length) {
    t=as_type(eval(args[0]));
  } else {
    t=TAny;
  }
  //writef("array %s\n",types.str(t));
  if (args.length>1) {
    assert(args.length==2);
    t=array_type_from_subtype_and_length(t,as_int(args[1]));
  } else {
    t=array_type_from_subtype(t);
  }
  //writef(" -> %s\n",types.str(t));
  return type_cell(t);
}
Cell op_struct(Cell[] args) {
  static if (debf) {debEnter("[struct]");scope (exit) debLeave();}
  foreach (ref arg;args) {
//    arg.show();
    assert(as_list(arg).length==2);
    arg.lst[0]=eval(arg.lst[0]);
    assert(isa(arg.lst[0],TType));
  }
  Type t=struct_type_from_fields(args);
  return type_cell(t);
}
Cell op_struct_get(Cell[] args) {
  static if (debf) {debEnter("[struct_get_field]");scope (exit) debLeave();}
  assert(args.length==2);
  Struct* s=as_struct(args[0]);
  string key=as_str(args[1]);
  return struct_get_field(s,key);
}
Cell op_struct_set(Cell[] args) {
  static if (debf) {debEnter("[struct_set_field]");scope (exit) debLeave();}
  assert(args.length==3);
  Struct* s=as_struct(args[0]);
  string key=as_str(args[1]);
  struct_set_field(s,key,args[2]);
  return args[2];
}
Cell op_union(Cell[] args) {
  static if (debf) {debEnter("[union]");scope (exit) debLeave();}
  foreach (ref arg;args) {
    assert(as_list(arg).length==2);
    arg.lst[0]=eval(arg.lst[0]);
    assert(isa(arg.lst[0],TType));
  }
  Type t=union_type_from_fields(args);
  return type_cell(t);
}
Cell op_union_get(Cell[] args) {
  static if (debf) {debEnter("[union_get]");scope (exit) debLeave();}
  assert(args.length==2);
  Union* u=as_union(args[0]);
  string key=as_str(args[1]);
  return union_get(u,key);
}
Cell op_union_set(Cell[] args) {
  static if (debf) {debEnter("[union_set]");scope (exit) debLeave();}
  assert(args.length==3);
  Union* u=as_union(args[0]);
  string key=as_str(args[1]);
  union_set(u,key,args[2]);
  return args[2];
}
Cell op_ref(Cell[] args) {
  static if (debf) {debEnter("[ref]");scope (exit) debLeave();}
  assert(args.length==1);
  Type t;
  if (args.length) {
    t=as_type(eval(args[0]));
  } else {
    t=TAny;
  }
  t=ref_type_from_subtype(t);
  return type_cell(t);
}
Cell op_getref(Cell[] args) {
  static if (debf) {debEnter("[ref]");scope (exit) debLeave();}
  assert(args.length==1);
  Cell c=args[0];
  assert(isa(c,TSymbol),"Cannot get reference of non-symbol cells (yet)");
  return ref_cell(environment,as_symbol(c));
}
Cell op_deref(Cell[] args) {
  static if (debf) {debEnter("[deref]");scope (exit) debLeave();}
  assert(args.length==1);
  Ref* r=as_ref(args[0]);
  assert(r.env,"Trying to deref null reference (env)");
  assert(r.id.length,"Trying to deref null reference (id)");
  return evalin(symbol_cell(r.id),r.env);
}
Cell op_ref_set(Cell[] args) {
  static if (debf) {debEnter("[deref]");scope (exit) debLeave();}
  assert(args.length==2);
  Ref* r=as_ref(args[0]);
  assert(r.env,"Trying to deref (left) null reference (env)");
  assert(r.id.length,"Trying to deref (left) null reference (id)");
  env_put(r.env,r.id,args[1]);
  return args[1];
}
/*Cell op_result(Cell[] args) {
  static if (debf) {debEnter("[$result]");scope (exit) debLeave();}
  assert(args.length==1);
  return args[1];
}*/
void add_libs(Env* env) {
  // normal functions
  env_putfun_sigstr(env,"+",fun_cell(&op_add_int_int),"(int int)","int");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_int_float),"(int float)","float");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_float_int),"(float int)","float");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_float_float),"(float float)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_neg_int),"(int)","int");
  env_putfun_sigstr(env,"-",fun_cell(&op_neg_float),"(float)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_int_int),"(int int)","int");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_int_float),"(int float)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_float_int),"(float int)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_float_float),"(float float)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_int_int),"(int int)","int");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_int_float),"(int float)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_float_int),"(float int)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_float_float),"(float float)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_int_int),"(int int)","int");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_int_float),"(int float)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_float_int),"(float int)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_float_float),"(float float)","float");

  env_put(env,"<",fun_cell(&op_less));
  env_put(env,">",fun_cell(&op_greater));
  env_put(env,"<=",fun_cell(&op_less_equal));
  env_put(env,">=",fun_cell(&op_greater_equal));
  env_put(env,"==",fun_cell(&op_equal));
  env_put(env,"!=",fun_cell(&op_not_equal));
  env_put(env,"sqrt",fun_cell(&op_sqrt));

  env_put(env,"equal?",env_get(env,"=="));
  env_put(env,"eq?",env_get(env,"=="));
  env_put(env,"length",fun_cell(&op_length));
  env_put(env,"car",fun_cell(&op_car));
  env_put(env,"cdr",fun_cell(&op_cdr));
  env_put(env,"cons",fun_cell(&op_cons));
  env_put(env,"append",fun_cell(&op_append));
  env_put(env,"list",fun_cell(&op_list));
  env_put(env,"list?",fun_cell(&op_listp));
  env_put(env,"symbol?",fun_cell(&op_symbolp));
  env_put(env,"null?",fun_cell(&op_nullp));
  env_put(env,"tostr",fun_cell(&op_tostr));
  env_put(env,"pr",fun_cell(&op_pr));
  env_put(env,"prln",fun_cell(&op_prln));
  env_put(env,"tic",fun_cell(&op_tic));
  env_put(env,"toc",fun_cell(&op_toc));

  env_put(env,"new_object",fun_cell(&op_new_object));
  env_putfun_sigstr(env,"get",fun_cell(&op_assoc_get),"((assoc) string)","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_assoc_set),"((assoc) string any)","any");

  env_putfun_sigstr(env,"get",fun_cell(&op_env_get),"(env string)","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_env_set),"(env string any)","any");

  env_putfun_sigstr(env,"get",fun_cell(&op_ftab_get),"(funtab (... type))","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_ftab_set),"(funtab (... type))","any");

  env_put(env,"new_array",fun_cell(&op_new_array));
  env_put(env,"array",lfun_cell(&op_array));
//  env_putfun_sigstr(env,"array",lfun_cell(&op_array),"(type = any)","type");
  env_putfun_sigstr(env,"get",fun_cell(&op_array_get),"((array) int)","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_array_set),"((array) int any)","any");
  env_putfun_sigstr(env,"resize",fun_cell(&op_array_resize),"((array any) int)","any");
  env_putfun_sigstr(env,"~",fun_cell(&op_array_cat),"((array) any)","any");
  env_putfun_sigstr(env,"~",fun_cell(&op_string_cat),"(string string)","string");

  env_put(env,"struct",lfun_cell(&op_struct));
  env_putfun_sigstr(env,"get",fun_cell(&op_struct_get),"((struct) string)","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_struct_set),"((struct) string any)","any");

  env_put(env,"union",lfun_cell(&op_union));
  env_putfun_sigstr(env,"get",fun_cell(&op_union_get),"((union) string)","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_union_set),"((union) string any)","any");

  env_put(env,"ref",lfun_cell(&op_ref));
  env_put(env,"&",lfun_cell(&op_getref));
  env_putfun_sigstr(env,"@",fun_cell(&op_deref),"((ref))","any");
  //env_putfun_sigstr(env,"get",fun_cell(&op_ref_get),"((ref))","any");
  env_putfun_sigstr(env,"set",fun_cell(&op_ref_set),"((ref) any)","any");

  env_putfun_sigstr(env,"new",fun_cell(&op_new__string),"(string)","any");
  env_putfun_sigstr(env,"new",fun_cell(&op_new__type),"(type)","any");
  env_putfun_sigstr(env,"alloc",fun_cell(&op_alloc),"(type)","any");
  env_putfun_sigstr(env,"typeof",fun_cell(&op_typeof),"(any)","type");
  env_putfun_sigstr(env,"unpack",fun_cell(&op_unpack),"(any)","any");
  env_putfun_sigstr(env,"pack",fun_cell(&op_pack),"(any type)","any");

//  env_putfun_sigstr(env,"tron",fun_cell(&op_tron),"()","any");
//  env_putfun_sigstr(env,"troff",fun_cell(&op_tron),"()","any");
//  env_put(env,"$result",fun_cell(&op_result));
}

