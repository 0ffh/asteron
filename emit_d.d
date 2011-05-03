module emit_d;

import std.file;
import std.stdio;
import std.string;
import std.regexp;
import std.c.stdio;
import std.c.string;

import debg;
import main;
import trafo;
import utils;
import cells;
import types;
import environments;

const bool debf=debflag;

FILE* dst;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- emitter functions
//----------------

Cell dummy;

int indval=0;
bool newlnf=true;
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
  fprintf(dst,"%s",tsz(buffer));
}
void ind() {++indval;}
void unind() {--indval;}
void crlf() {fprintf(dst,"\n");newlnf=true;}

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
  static if (debf) {debEnter("emit_ast(Cell)");scope (exit) debLeave();}
  if (!isa(c,TList)) {
    if (isa(c,TType)) {
      emit("\"");
      emit_ast(abs_eval(c));
//       emit_ast(as_type(c));
      emit("\"");
    }
    if (isa(c,TInt)) {
      emit("%d",as_int(c));
    }
    if (isa(c,TFloat)) {
      emit("%g",as_float(c));
    }
    if (isa(c,TSymbol)) {
      emit("%s",as_symbol(c));
    }
    if (isa(c,TString)) {
      emit("\"%s\"",as_str(c));
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
  assert(c.lst.length);
  //writefln("%s",cells.str(c.lst[0]));
  assert(isa(c.lst[0],TSymbol));
  string id=as_symbol(c.lst[0]);
  Cell[] sub=[];
  if (c.lst.length>1) sub=c.lst[1..$];
//  emit("[%s]",id);
//  writefln("<%s>\n",id);//types.str(c.type));
  if (id=="seq") {
    emit("{");
    ind();
    foreach (Cell s;sub) {
      crlf();
      emit_ast(s);
      emit(";");
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
    emit("&(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id=="@") {
    emit("*(");
    emit_ast(sub[0]);
    emit(")");
  } else if (id_in(id,["=","+=","-=","*=","/=","~="])) {
    Cell d=abs_eval(sub[0]);
    emit_ast(sub[0]);
    emit(id);
    //emit("cast()(");
    emit_ast(sub[1]);
    //emit(")");
  } else if (id_in(id,["==","!="])) {
    emit("(");
    emit_ast(sub[0]);
    emit(id);
    emit_ast(sub[1]);
    emit(")");
  } else if (id_in(id,[">","<",">=","<=","+","-","*","/","~"])) {
    emit("(");
    emit_ast(sub[0]);
    emit(id);
    emit_ast(sub[1]);
    emit(")");
  } else if (id=="set") {
    emit_ast(sub[0]);
    if (isa(sub[1],TString)) {
      emit("."~as_str(sub[1]));
    } else if (isa(sub[1],TInt)) {
      emit("[%d]",as_int(sub[1]));
    } else {
      emit("[");
      emit_ast(sub[1]);
      emit("]");
    }
    emit("=");
    emit_ast(sub[2]);
  } else if (id=="get") {
    emit_ast(sub[0]);
    if (isa(sub[1],TString)) {
      emit("."~as_str(sub[1]));
    } else if (isa(sub[1],TInt)) {
      emit("[%d]",as_int(sub[1]));
    } else {
      emit("[");
      emit_ast(sub[1]);
      emit("]");
    }
  } else if (id=="call") {
    Cell cc=list_cell([sub[0],sub[1]]);
    writefln("call : %s",cells.str(cc));
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
    /*writef("### define %s %s\n",name,types.str(cel.type));
    writef("### define %s %s\n",name,cells.str(cel.type.cell));
    emit_ast(cel.type);*/
    string tn;
    Cell* tnp="typename" in cel.ann;
    writefln("%s : %s [%s]\n",name,cells.str(cel,1),types.str(cel.type));
    if (tnp is null) {
      writefln("~~~ no type annotation for %s",name);
      //assert(false);
      //tn=types.str(cel.type);
      emit_ast(cel.type);
    } else {
      tn=as_symbol(*tnp);
      emit("%s",tn);
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
    emit("// local defun moved to outermost scope");
  } else if (id=="deftype") {
    // omit
    emit("// omitting "~id);
  } else if (id=="aliastype") {
    // omit
    emit("// omitting "~id);
  } else if (id=="supertype") {
    // omit
    emit("// omitting "~id);
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
void emit_ast(FunListEntry fle) {
  static if (debf) {debEnter("emit_ast(FunListEntry)");scope (exit) debLeave();}
  if (!isa(fle.fun,TLambda)) return;
  //crlf();
  //emit("//----- defun %s",fle.nam);
  string[] nam=lambda_parameter_names(fle.fun);
  Cell[] def=lambda_parameter_defaults(fle.fun);
  crlf();
  if (isa(fle.res,TNull)) {
    emit("void");
  } else {
    emit_ast(fle.res.type);
  }
  emit(" %s(",fle.nam[1..$]);
  static if (1) {
    for (int k;k<fle.par.length;++k) {
      if (k) emit(",");
      emit_ast(fle.par[k].type);
      emit(" "~nam[k]);
      if (!isa(def[k],TNull)) {
        emit("=");
        emit_ast(def[k]);
      }
    }
  } else {
    int knam=0;
    for (int k;k<fle.par.length;++k) {
      if (k) emit(",");
      emit_ast(fle.par[k].type);
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
  emit_ast(fle.fun);
}
void emit_ast(Type t,string name="") {
  static if (debf) {debEnter("emit_ast(Type)");scope (exit) debLeave();}
  if (is_basic_type(t)) {
    emit(types.str(t));
  } else if (is_array_type(t)) {
    Type st=get_array_subtype(t);
    emit_ast(st);
    emit("[]");
  } else if (is_ref_type(t)) {
    Type st=get_ref_subtype(t);
    emit_ast(st);
    emit("*");
  } else if (is_struct_type(t)) {
    writef("emit struct type %s [%s]\n",name,types.str(t));
    string type_name=get_atype_name(t);
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
    writef("emit union type %s [%s]\n",name,types.str(t));
    string type_name=get_atype_name(t);
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
      if (is_alias_type(t)) {
//        writef("emit alias typedef %s\n",key);
        if (is_atype_name(key)) {
          t=get_alias_subtype(t);
          emit_typedef(key,t);
        }
      }
    }
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
void emit_d_main(Cell root,FunListEntry[] fun_list,string fn="stdout") {
  static if (debf) {debEnter("emit_d_main(...)");scope (exit) debLeave();}
  environment=base_env;
  if (fn=="stdout") dst=stdout;
  else dst=fopen(tsz(fn),"wb");
  emit("import std.stdio;");crlf();
  emit("import rtlib;");crlf();
  crlf();
  emit_typedefs();
  emit_globals(root);
//   emit_functions(root);
  for (int kfl=fun_list.length;kfl;) {
    FunListEntry fle=fun_list[--kfl];
    push_env(fle.env);
    emit_ast(fle);
    pop_env();
  }
  emit("\nvoid main() {main_0();}");
  crlf();
  if (dst!=stdout)
    fclose(dst);
}