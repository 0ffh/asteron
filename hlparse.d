module hlparse;

import debg;
import lexer;
import cells;
import types;
import llparse;
import environments;
import utils;
import std.conv;
import std.stdio;
import std.string;

const bool debf=debflag && 0;
const bool new_dot_operator=true;

string[string] opname;
string[string] opeq;
void init_hlparse() {
  opeq["+="]="+";
  opeq["-="]="-";
  opeq["*="]="*";
  opeq["/="]="/";
  opeq["~="]="~";
  opname["+"]="opAdd";
  opname["-"]="opSub";
  opname["*"]="opMul";
  opname["/"]="opDiv";
}
bool tav(Token t,string a,string v="") {
  // check token arity and value
  return (t.arity==a) && ((!v.length) || (t.value==v));
}
Cell[] tokens2cells(Token[] t) {
  Cell[] c;
  c.length=t.length;
  for (int k;k<t.length;++k) c[k]=token2cell(t[k]);
  return c;
}
Cell tag(Cell c,string tn) {
  //c.ann["typename"]=symbol_cell(tn);
  return c;
}
Cell token2cell(Token t) {
  //static if (debf) {debEnter("token2cell()");scope (exit) debLeave();}
  if (tav(t,"name")) return symbol_cell(t.value);
  if (tav(t,"string")) return tag(string_cell(t.value),"string");
  if (tav(t,"literal","true")) return tag(int_cell(1),"int");
  if (tav(t,"literal","false")) return tag(int_cell(0),"int");
  if (tav(t,"literal","null")) return null_cell();
  if (tav(t,"this")) return symbol_cell(t.value);
  if (tav(t,"number")) {
    try {
      return tag(int_cell(toInt(t.value)),"int");
    } catch {
      return tag(float_cell(toFloat(t.value)),"float");
    }
  }
  if (tav(t,"binary","type_name")) {
//printf("##### type_name\n");
    return list_cell(tokens2cells(t.sub));
  }
  if (tav(t,"ternary","type_name_value")) {
//printf("##### type_name_value\n");
    return list_cell(tokens2cells(t.sub));
  }
  if (tav(t,"unary","{")) {
    assert(t.sub.length==1);
    assert(t.sub[0].arity=="array");
    Token[] sub=t.sub[0].sub;
    Cell[] lst=[symbol_cell("new_object")];
    for (int k;k<sub.length;++k) {
      lst~=[string_cell(sub[k].key),token2cell(sub[k])];
    }
    return list_cell(lst);
  }
  if (tav(t,"unary","[")) {
    assert(t.sub.length==1);
    assert(t.sub[0].arity=="array");
    return list_cell(symbol_cell("new_array")~as_list(token2cell(t.sub[0])));
  }
  if (tav(t,"unary","typeof")) {
    assert(t.sub.length==1);
    return list_cell([symbol_cell("typeof"),token2cell(t.sub[0])]);
  }
  if (tav(t,"parameter")) {
    Cell[] cs=tokens2cells(t.sub);
//    if (cs.length==3) cs=[cs[0],cs[1],symbol_cell("="),cs[2]];
    return list_cell(cs);
  }
  if (tav(t,"type")) {
    if (t.id=="(name)") return symbol_cell(t.value);
    if (t.id=="assoc") {
      return list_cell([symbol_cell("assoc")]~tokens2cells(t.sub));
    }
    if (t.id=="struct") {
      return list_cell([symbol_cell("struct")]~tokens2cells(t.sub));
    }
    if (t.id=="class") {
      return list_cell([symbol_cell("class")]~tokens2cells(t.sub));
    }
    if (t.id=="union") {
      return list_cell([symbol_cell("union")]~tokens2cells(t.sub));
    }
    if (t.id=="[") {
      return list_cell([symbol_cell("array")]~tokens2cells(t.sub));
    }
    if (t.id=="@") {
      return list_cell([symbol_cell("ref")]~tokens2cells(t.sub));
    }
    if (t.id==";") {
      assert(t.sub.length==1);
      return token2cell(t.sub[0]);
    }
  }
  if (tav(t,"statement","deftype")) {
    Cell type=token2cell(t.sub[0]);
    return list_cell([symbol_cell("deftype"),symbol_cell(t.name),type]);
  }
  if (tav(t,"statement","aliastype")) {
    Cell type=token2cell(t.sub[0]);
    return list_cell([symbol_cell("aliastype"),symbol_cell(t.name),type]);
  }
  if (tav(t,"statement","supertype")) {
    return list_cell([symbol_cell("supertype"),symbol_cell(t.name)]~tokens2cells(t.sub));
  }
  if (tav(t,"statement","defun")) {
    Cell pars=token2cell(t.sub[0]);
    Cell code=token2cell(t.sub[1]);
    if (t.sub[1].arity=="array") code.lst=symbol_cell("seq")~code.lst;
    return list_cell([symbol_cell("defun"),symbol_cell(t.name),pars,code]);
  }
  if (tav(t,"function","function")) {
    Cell pars=token2cell(t.sub[0]);
    Cell code=token2cell(t.sub[1]);
    if (t.sub[1].arity=="array") code.lst=symbol_cell("seq")~code.lst;
    return list_cell([symbol_cell("function"),pars,code]);
  }
  if (tav(t,"statement","def")) {
    if (t.sub.length==2) {
      return list_cell([symbol_cell("def")]~tokens2cells(t.sub));
    }
    if (t.sub.length==3) {
      return list_cell([symbol_cell("def")]~tokens2cells(t.sub));
    }
    assert(false);
  }
  if (tav(t,"statement","scope")) {
    if (t.sub.length==1) {
      if (t.sub[0].arity=="array") {
        Cell code=token2cell(t.sub[0]);
        code=list_cell(symbol_cell("seq")~as_list(code));
        return list_cell([symbol_cell("scope"),code]);
      }
      if (t.sub[0].arity=="statement") {
        Cell code=token2cell(t.sub[0]);
        return list_cell([symbol_cell("scope"),code]);
      }
    }
    if (t.sub.length==2) {
      //t.show();
      assert(t.sub[0].arity=="name");
      if (t.sub[1].arity=="array") {
        Cell code=token2cell(t.sub[1]);
        code=list_cell(symbol_cell("seq")~as_list(code));
        return list_cell([symbol_cell("scope"),symbol_cell(t.sub[0].value),code]);
      }
      if (t.sub[1].arity=="statement") {
        Cell code=token2cell(t.sub[1]);
        return list_cell([symbol_cell("scope"),symbol_cell(t.sub[0].value),code]);
      }
    }
    assert(false);
  }
  if (tav(t,"statement","if")) {
    if (t.sub.length==2) {
      Cell c=list_cell([symbol_cell("if")]~tokens2cells(t.sub));
      if (t.sub[1].arity=="array") c.lst[2].lst=symbol_cell("seq")~c.lst[2].lst;
      return c;
    }
    if (t.sub.length==3) {
      Cell c=list_cell([symbol_cell("if")]~tokens2cells(t.sub));
      if (t.sub[1].arity=="array") c.lst[2].lst=symbol_cell("seq")~c.lst[2].lst;
      if (t.sub[2].arity=="array") c.lst[3].lst=symbol_cell("seq")~c.lst[3].lst;
      return c;
    }
    assert(false);
  }
  if (tav(t,"statement","for")) {
    assert(t.sub.length==4);
    Cell c=list_cell([symbol_cell("for")]~tokens2cells(t.sub));
    //printf("%.*s\n",cells.str(c));
    if (t.sub[0].arity=="array") c.lst[1].lst=symbol_cell("seq")~c.lst[1].lst;
    if (t.sub[3].arity=="array") c.lst[4].lst=symbol_cell("seq")~c.lst[4].lst;
    //printf("%.*s\n",cells.str(c));
    return c;
  }
  if (tav(t,"statement","while")) {
    assert(t.sub.length==2);
    Cell c=list_cell([symbol_cell("while")]~tokens2cells(t.sub));
    if (t.sub[1].arity=="array") c.lst[2].lst=symbol_cell("seq")~c.lst[2].lst;
    return c;
  }
  if (tav(t,"statement","do")) {
    assert(t.sub.length==2);
    Cell c=list_cell([symbol_cell("dowhile")]~tokens2cells(t.sub));
    if (t.sub[0].arity=="array") c.lst[1].lst=symbol_cell("seq")~c.lst[1].lst;
    return c;
  }
  if (tav(t,"unary","!")) {
    assert(t.sub.length==1);
    return list_cell([symbol_cell("not"),token2cell(t.sub[0])]);
  }
  if (tav(t,"ternary","?")) {
    assert(t.sub.length==3);
    return list_cell([symbol_cell("if")]~tokens2cells(t.sub));
  }
  if (tav(t,"statement","switch")) {
    Cell[] lst=[symbol_cell("switch")]~tokens2cells(t.sub);
    for (int k=1;k<lst.length;k+=2) {
      if (isa(lst[k],TList)) lst[k].lst=symbol_cell("seq")~lst[k].lst;
    }
    return list_cell(lst);
  }
  if (tav(t,"statement","break")) {
    assert(!t.sub.length);
    return list_cell([symbol_cell("break")]);
  }
  if (tav(t,"statement","continue")) {
    assert(!t.sub.length);
    return list_cell([symbol_cell("continue")]);
  }
  if (tav(t,"statement","return")) {
    if (!t.sub.length) {
      return list_cell([symbol_cell("return")]);
    }
    if (t.sub.length==1) {
      return list_cell([symbol_cell("return"),token2cell(t.sub[0])]);
    }
    assert(false);
  }
  if (tav(t,"binary","(")) {
    Cell c=list_cell();
    c.lst~=token2cell(t.sub[0]);
    if (!tav(t.sub[1],"array")) assert(false);
    c.lst~=token2cell(t.sub[1]).lst;
    return c;
  }
  if (tav(t,"ternary","(")) {
    Cell c=list_cell();
    c.lst~=[symbol_cell("call"),token2cell(t.sub[0]),symbol_cell(t.sub[1].value)];
    if (!tav(t.sub[2],"array")) assert(false);
    c.lst~=token2cell(t.sub[2]).lst;
    return c;
  }
  if (tav(t,"binary",".")) {
    Cell c=list_cell();
    c.lst~=symbol_cell("dotget");
    c.lst~=token2cell(t.sub[0]);
    c.lst~=string_cell(t.sub[1].value);
    return c;
  }
  if (tav(t,"binary","[")) {
    Cell c=list_cell();
    c.lst~=symbol_cell("idxget");
    for (int k;k<t.sub.length;++k) {
      c.lst~=token2cell(t.sub[k]);
    }
    return c;
  }
/*  if (tav(t,"unary","preincrement")) {
    assert(t.sub.length==1);
    Cell id=token2cell(t.sub[0]);
    Cell sum=list_cell([symbol_cell("+"),id,int_cell(1)]);
    return list_cell([symbol_cell("="),id,sum]);
  }
  if (tav(t,"unary","predecrement")) {
    assert(t.sub.length==1);
    Cell id=token2cell(t.sub[0]);
    Cell sum=list_cell([symbol_cell("-"),id,int_cell(1)]);
    return list_cell([symbol_cell("="),id,sum]);
  }*/
  if (tav(t,"binary")) {
    if (string* op=(t.value in opname)) {
      //t.value=*op;
    }
    if (string* op=(t.value in opeq)) {
      // (?= a b) -> (= a (? a b))
      Token h=new Token(*op,"binary",*op);
      h.sub=t.sub;
      t.id="=";
      t.value="=";
      t.sub=[t.sub[0],h];
      return token2cell(t);
    }
  }
  if (tav(t,"binary","=")) {
    Cell c=list_cell();
    if (tav(t.sub[0],"binary",".")) {
      c.lst~=symbol_cell("dotset");
      c.lst~=token2cell(t.sub[0].sub[0]);
      //c.lst[$-1]=list_cell([symbol_cell("&")]~c.lst[$-1]);
      c.lst~=string_cell(t.sub[0].sub[1].value);
    } else if (tav(t.sub[0],"binary","[")) {
      c.lst~=symbol_cell("idxset");
      c.lst~=token2cell(t.sub[0].sub[0]);
      c.lst~=token2cell(t.sub[0].sub[1]);
    } else if (tav(t.sub[0],"unary","@")) {
      c.lst~=symbol_cell("refset");
      c.lst~=token2cell(t.sub[0].sub[0]);
    } else {
      c.lst~=symbol_cell("=");
      c.lst~=token2cell(t.sub[0]);
    }
    c.lst~=token2cell(t.sub[1]);
    return c;
  }
  if (tav(t,"unary")) {
    return list_cell([symbol_cell(t.value),token2cell(t.sub[0])]);
  }
  if (tav(t,"binary")) {
    return list_cell([symbol_cell(t.value),token2cell(t.sub[0]),token2cell(t.sub[1])]);
  }
  if (tav(t,"array")) {
    return list_cell(tokens2cells(t.sub));
  }
  t.error("js-to-lisp error");
}
Cell parse_string_to_cell(string source) {
  static if (debf) {debEnter("parse_string_to_cell()");scope (exit) debLeave();}
  Token t=parse_string_to_token(source);
//  t.show();
  Cell c=token2cell(t);
  assert(isa(c,TList),"list cell expected");
  c.lst=symbol_cell("seq")~c.lst;
  return c;
}
Cell parse_file_to_cell(string filename) {
  static if (debf) {debEnter("parse_file_to_cell()");scope (exit) debLeave();}
  return parse_string_to_cell(cast(string)std.file.read(filename));
}
