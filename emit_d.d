module emit_d;

import trafo;
import std.file;
import std.stdio;
import std.string;
import std.regexp;
import std.c.stdio;
import std.c.string;

import ac;
import debg;
import trafo;
import utils;
import cells;
import types;
import environments;

const bool debf=debflag && 1;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- emitter functions
//----------------

string emitstring="";
int indval=0;
bool newlnf=true;
bool emitted_line_is_empty() {
  return newlnf;
}
void indent(int n) {
  while (n-->0) emit("  ");
}
void emit(...) {
  static if (debf) {debEnter("emit(...)");scope (exit) debLeave();}
  string buffer;
  void putc(dchar c) {buffer~=c;}
  std.format.doFormat(&putc,_arguments,_argptr);
  if (newlnf) {
    newlnf=false;
    indent(indval);
  }
  emitstring~=buffer;
}
void ind() {++indval;}
void unind() {--indval;}
void crlf() {emit("\n");newlnf=true;}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- anonymous types - variables & helpers
//----------------

Type[string] anon_types;
int anon_type_count=0;

string new_anon_type(Type type) {
  // avoid duplicates
  foreach (name;anon_types.keys) {
    if (anon_types[name]==type) return name;
  }
  // generate new
  string name=frm("anon_type_%d",anon_type_count++);
  anon_types[name]=type;
  return name;
}
bool must_force_as_anon_type(Type type) {
  return (is_struct_type(type) || is_union_type(type));
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- job
//----------------

string callstr(Cell c) {
  string s;
  if (isa(c,TList)) {
    if (isa(c.lst[0],TSymbol)) {
      s=as_symbol(c.lst[0]);
    }
  }
  return s;
}
bool calls(Cell c,string s) {
  if (isa(c,TList)) {
    if (isa(c.lst[0],TSymbol)) {
      return s==as_symbol(c.lst[0]);
    }
  }
  return false;
}
bool id_in(string id,string[] cids) {
  foreach (cid;cids) if (cid==id) return true;
  return false;
}
void emit_ast(Cell c) {
  static if (debf) {debEnter("emit_ast(Cell='%s')",c);scope (exit) debLeave();}
  if (!isa(c,TList)) {
    if (isa(c,TType)) {
      emit("\"");
      emit_ast(abs_eval(c));
//       emit_ast(as_type(c));
      emit("\"");
    }
    if (is_uint(c)) {
      emit("%d",c.ufix);
    }
    if (is_sint(c)) {
      emit("%d",c.sfix);
    }
    if (isa(c,TFloat)) {
      emit("%gf",as_float(c));
    }
    if (isa(c,TSymbol)) {
      emit("%s",as_symbol(c));
    }
    if (isa(c,TString)) {
      emit("\"%s\"",as_string(c));
    }
    if (isa(c,TLambda)) {
      if (callstr(c.lam.expr)=="seq") {
        emit_ast(c.lam.expr);
      } else {
        emit("{");
        ind();
        crlf();
        emit_ast(c.lam.expr);
        emit(";");
        unind();
        crlf();
        emit("}");
      }
    }
    return;
  }
  if (!c.lst.length) {
    //emit("// line removed");
    return;
  }
  //writefln("%s",cells.str(c.lst[0]));
  if (!isa(c.lst[0],TSymbol)) {
    assert(false);
    emit_ast(c.lst[0]);
    c.lst[0]=symbol_cell(" ");
  }
  string id=as_symbol(c.lst[0]);
  Cell[] sub=[];
  if (c.lst.length>1) sub=c.lst[1..$];
//  emit("[%s]",id);
//  writefln("<%s>\n",id);//types.str(c.type));
  if (id=="seq") {
    emit("{");
    ind();
    foreach (Cell s;sub) {
      if (!emitted_line_is_empty()) crlf();
      emit_ast(s);
      if (!emitted_line_is_empty()) emit(";");
    }
    unind();
    crlf();
    emit("}");
  } else if (id=="if") {
    emit("if (");
    emit_ast(sub[0]);
    emit(") ");
    emit_ast(sub[1]);
    if (sub.length>2) {
      if (callstr(sub[1])!="seq") {
        emit(";");
        crlf();
      } else {
        emit(" ");
      }
      emit("else ");
      emit_ast(sub[2]);
    }
  } else if (id=="for") {
    Cell* env_cell=("environment" in c.ann);
    assert(env_cell,"Missing environment annotation in for node");
    push_env(as_env(*env_cell));
    emit("for (");
    emit_ast(sub[0]);
    emit(";");
    emit_ast(sub[1]);
    emit(";");
    emit_ast(sub[2]);
    emit(") ");
    emit_ast(sub[3]);
    pop_env();
  } else if (id=="while") {
    Cell* env_cell=("environment" in c.ann);
    assert(env_cell,"Missing environment annotation in for node");
    push_env(as_env(*env_cell));
    emit("while (");
    emit_ast(sub[0]);
    emit(") ");
    if (calls(sub[1],"seq")) {
      emit_ast(sub[1]);
    } else {
      emit("{");
      emit_ast(sub[1]);
      emit(";}");
    }
//     emit_ast(sub[1]);
    pop_env();
  } else if (id=="dowhile") {
    Cell* env_cell=("environment" in c.ann);
    assert(env_cell,"Missing environment annotation in for node");
    push_env(as_env(*env_cell));
    emit("do ");
    if (calls(sub[0],"seq")) {
      emit_ast(sub[0]);
    } else {
      emit("{");
      emit_ast(sub[0]);
      emit(";}");
    }
    emit(" while (");
    emit_ast(sub[1]);
    emit(")");
    pop_env();
  } else if (id=="switch") {
    emit("switch (");
    emit_ast(sub[0]);
    emit(") {");
    ind();
    crlf();
    int k=1;
    while ((k+1)<sub.length) {
      emit("case ");
      emit_ast(sub[k++]);
      emit(" : ");
      emit_ast(sub[k++]);
      emit(";");
      crlf();
    }
    unind();
    emit("}");
  } else if (id=="&") {
    emit("(&");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="@") {
    emit("(*");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="refset") {
    emit("(*");
    emit_ast(sub[0]);
    emit(")=");
    emit_ast(sub[1]);
    emit(";");
  } else if (id_in(id,["=","+=","-=","*=","/=","~="])) {
    //Cell d=abs_eval(sub[0]);
    emit("(");
    emit_ast(sub[0]);
    emit(id);
    //emit("cast()(");
    emit_ast(sub[1]);
    emit(")");
  } else if (id_in(id,["==","!="])) {
    emit("(");
    emit_ast(sub[0]);
    emit(id);
    emit_ast(sub[1]);
    emit(")");
  } else if (id_in(id,[">","<",">=","<=","+","-","*","/","~"])) {
    emit("(");
    if (sub.length>1) {
      emit_ast(sub[0]);
      emit(id);
      emit_ast(sub[1]);
    } else {
      emit(id);
      emit_ast(sub[0]);
    }
    emit(")");
  } else if (id=="dotset") {
    if (is_list_with_operator(sub[0],"&")) sub[0]=sub[0].lst[1];
    emit_ast(sub[0]);
    emit("."~as_string(sub[1]));
/*    emit(".");
    emit_ast(sub[1]);*/
    emit("=");
    emit_ast(sub[2]);
  } else if (id=="dotget") {
    emit_ast(sub[0]);
    emit("."~as_string(sub[1]));
/*    emit(".");
    emit_ast(sub[1]);*/
  } else if (id=="idxset") {
    emit_ast(sub[0]);
    /*if (isa(sub[1],TString)) {
      emit("."~as_string(sub[1]));
    } else if (isa(sub[1],TInt)) {
      emit("[%d]",as_int(sub[1]));
    } else {*/
      emit("[");
      emit_ast(sub[1]);
      emit("]");
    //}
    emit("=");
    emit_ast(sub[2]);
  } else if (id=="idxget") {
    emit_ast(sub[0]);
    /*if (isa(sub[1],TString)) {
      emit("."~as_string(sub[1]));
    } else if (isa(sub[1],TInt)) {
      emit("[%d]",as_int(sub[1]));
    } else {*/
      emit("[");
      emit_ast(sub[1]);
      emit("]");
    //}
  } else if (id=="call") {
    Cell cc=list_cell([sub[1],sub[0]]);
//    writefln("call : %s",cells.str(cc));
    emit_ast(cc);
  } else if (id=="resize") {
    emit_ast(sub[0]);
    emit(".length=");
    emit_ast(sub[1]);
  } else if (id=="new") {
    emit("my_new(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="array") {
    emit("my_array(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="typeof") {
    emit("my_typeof(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="tostr") {
    emit("tostr(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id_in(id,["break","continue"])) {
    emit(id);
  } else if (id=="return") {
    emit("return ");
    emit_ast(sub[0]);
  } else if (id=="new_array") {
    emit("[");
    for (int k=0;k<sub.length;++k) {
      if (k) emit(",");
      emit_ast(sub[k]);
    }
    emit("]");
  } else if (id=="prln") {
    emit("%s(",id);
    for (int k=0;k<sub.length;++k) {
      if (k) emit(",");
      emit_ast(sub[k]);
    }
    emit(")");
  } else if (id=="def") {
    string name=as_symbol(sub[1]);
    Cell cel=env_get(environment,name);
    if (must_force_as_anon_type(cel.type)) {
      emit(new_anon_type(cel.type));
    } else {
      emit_ast(cel.type);
    }
    emit(" %s",name);
    if (sub.length>2) {
      emit("=");
      emit_ast(sub[2]);
    }
  } else if (id[0]=='$') {
    emit("%s(",id[1..$]);
    for (int k=0;k<sub.length;++k) {
      if (k) emit(",");
      emit_ast(sub[k]);
    }
    emit(")");
  } else if (id=="defun") {
    // omit
    //emit("// local defun moved to outermost scope");
  } else if (id=="deftype") {
    // omit
    //emit("// omitting "~id);
  } else if (id=="aliastype") {
    // omit
    //emit("// omitting "~id);
  } else if (id=="supertype") {
    // omit
    //emit("// omitting "~id);
  } else if (id=="unpack") {
    assert(sub.length==1);
    emit_ast(sub[0]);
  } else {
    static if (1) {
      emit("%s(",id);
      for (int k=0;k<sub.length;++k) {
        if (k) emit(",");
        emit_ast(sub[k]);
      }
      emit(")");
    } else {
      crlf();
      emit("[%s]",cells.str(c));
//     writef("*** Unhandled: [%s]\n",cells.str(c));
//     assert(false);
    }
  }
  fflush(stdout);
}
void emit_ast(FTabEntry* entry) {
  static if (debf) {debEnter("emit_ast(FTabEntry)");scope (exit) debLeave();}
  if (!isa(entry.fun,TLambda)) return;
//  writefln("=== emitting fun %s env %s : %s",entry.nam,entry.env,cells.str(entry.fun));
/*  foreach (string key;entry.env.inner.keys) {
    writefln(" # %s : %s",key,entry.env.inner[key]);
  }*/
  //crlf();
  //emit("//----- defun %s",entry.nam);
  string[] nam=lambda_parameter_names(entry.fun);
  Cell[] def=lambda_parameter_defaults(entry.fun);
  crlf();
  if (entry.ret==TNull) {
    emit("void");
  } else {
    emit_ast(entry.ret);
  }
  //writefln("names = %s",nam);
  //writefln("pars  = %s",entry.par);
  emit(" %s(",entry.nam[1..$]);
  static if (1) {
    for (int k;k<entry.sig.ses.length;++k) {
      if (k) emit(",");
      emit_ast(entry.sig.ses[k].type);
      emit(" "~nam[k]);
      /*
      if (!isa(def[k],TNull)) {
        emit("=");
        emit_ast(def[k]);
      }
      */
    }
  } else {
    int knam=0;
    for (int k;k<entry.par.length;++k) {
      if (k) emit(",");
      emit_ast(entry.par[k].type);
      if (nam[knam]=="...") {
        emit(" ellipse");
      } else {
        emit(" "~nam[knam++]);
        if (!isa(def[k],TNull)) {
          emit("=");
          emit_ast(def[k]);
        }
      }
    }
  }
  emit(") ");
  emit_ast(entry.fun);
}
void emit_ast(Type t,string name="") {
  static if (debf) {debEnter("emit_ast(Type)");scope (exit) debLeave();}
  if (is_basic_type(t)) {
    emit(types.str(t));
  } else if (is_array_type(t)) {
    Type st=get_array_subtype(t);
    emit_ast(st);
    Cell[] cf=get_compound_fields(t);
//    writefln("cf=%s",cf);
    if (cf.length>1) {
      emit("[");
      emit(cf[1]);
      emit("]");
    } else {
      emit("[]");
    }
  } else if (is_ref_type(t)) {
    Type st=get_ref_subtype(t);
    emit_ast(st);
    emit("*");
  } else if (is_struct_type(t)) {
//    writef("emit struct type %s [%s]\n",name,types.str(t));
    //string type_name=get_atype_name(t);
    Cell[] sc=get_compound_fields(t);
    emit("struct ");
    if (name.length) emit(name~" ");
    emit("{");
    for (int k;k<sc.length;++k) {
      emit_ast(sc[k].lst[0]);
      emit(" "~as_symbol(sc[k].lst[1]));
      emit(";");
    }
    emit("}");
  } else if (is_union_type(t)) {
//    writef("emit union type %s [%s]\n",name,types.str(t));
    //string type_name=get_atype_name(t);
    Cell[] sc=get_compound_fields(t);
    emit("union ");
    if (name.length) emit(name~" ");
    emit("{");
    for (int k;k<sc.length;++k) {
      emit_ast(sc[k].lst[0]);
      emit(" "~as_symbol(sc[k].lst[1]));
      emit(";");
    }
    emit("}");
  } else if (is_def_type(t)) {
    emit(types.str(t));
  } else {
    emit("<"~types.str(t)~">");
  }
}
void emit_typedef(string name,Type t) {
  static if (debf) {debEnter("emit_typedef(...)");scope (exit) debLeave();}
//  writef("typedef %s = %s\n",name,types.str(t));
  if (is_basic_type(t)) {
    emit("typedef ");
    emit_ast(t);
    emit(" "~name~";");
    crlf();
  }
  if (is_struct_type(t)) {
    emit_ast(t,name);
    emit(";");
    crlf();
  }
  if (is_union_type(t)) {
    emit_ast(t,name);
    emit(";");
    crlf();
  }
  if (is_array_type(t)) {
    emit("typedef ");
    emit_ast(t);
    emit(" "~name~";");
    crlf();
  }
}
void emit_typedefs() {
  Cell[string] ei=environment.inner;
  foreach (string key;ei.keys) {
    Cell c=ei[key];
    if (isa(c,TType)) {
      Type t=type(c);
      if (is_def_type(t)) {
        t=get_def_subtype(t);
        emit_typedef(key,t);
      }
/*      if (is_alias_type(t) && is_forced_atype(t)) {
//        writef("emit alias typedef %s\n",key);
        t=get_alias_subtype(t);
        emit_typedef(key,t);
      }*/
    }
  }
}
void emit_anon_typedefs() {
  foreach (string key;anon_types.keys) {
    emit_typedef(key,anon_types[key]);
  }
}
void emit_globals(Cell root) {
  if (!calls(root,"seq")) return;
  Cell[] sub=root.lst;
  foreach (s;sub) {
    if (calls(s,"def")) {
      emit_ast(s);
      emit(";");
      crlf();
    }
  }
}
void emit_d_main(Cell root,FTabEntry*[] fun_list,string fn="stdout") {
  static if (debf) {debEnter("emit_d_main(...)");scope (exit) debLeave();}
  string source="";
  environment=base_env;
  bool[FTabEntry*] fun_done;
  for (int kfl=fun_list.length;kfl;) {
    FTabEntry* entry=fun_list[--kfl];
    if (!(entry in fun_done)) {
      push_env(entry.env);
      emit_ast(entry);
      pop_env();
    }
  }
  emit("\nvoid main() {main_0();}");
  crlf();
  //---
  source=emitstring;
  emitstring="";
  //---
  emit("import std.stdio;");crlf();
  emit("import rtlib;");crlf();
  crlf();
  emit_typedefs();
  emit_anon_typedefs();
  emit_globals(root);
  //---
  source=emitstring~source;
  emitstring="";
  //--
  FILE* dst;
  if (fn=="stdout") dst=stdout; else dst=fopen(tsz(fn),"wb");
  fwritef(dst,"%s",source);
  if (dst!=stdout) fclose(dst);
}
