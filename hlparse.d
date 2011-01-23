module hlparse;

import debg;
import lexer;
import cells;
import types;
import llparse;
import environments;
import utils;
import std.conv;
import std.string;

string[string] opeq;
void init_hlparse() {
  opeq["+="]="+";
  opeq["-="]="-";
  opeq["*="]="*";
  opeq["/="]="/";
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
Cell token2cell(Token t) {
  if (tav(t,"name")) return sym_cell(t.value);
  if (tav(t,"string")) return str_cell(t.value);
  if (tav(t,"literal","true")) return int_cell(1);
  if (tav(t,"literal","false")) return int_cell(0);
  if (tav(t,"literal","null")) return null_cell();
  if (tav(t,"this")) return sym_cell(t.value);
  if (tav(t,"number")) {
    try {
      return int_cell(toInt(t.value));
    } catch {
      return float_cell(toFloat(t.value));
    }
  }
  if (tav(t,"binary","type_name")) {
    return list_cell(tokens2cells(t.sub));
  }
  if (tav(t,"ternary","type_name_value")) {
    return list_cell(tokens2cells(t.sub));
  }
  if (tav(t,"unary","{")) {
    assert(t.sub.length==1);
    assert(t.sub[0].arity=="array");
    Token[] sub=t.sub[0].sub;
    Cell[] lst=[sym_cell("new_object")];
    for (int k;k<sub.length;++k) {
      lst~=[str_cell(sub[k].key),token2cell(sub[k])];
    }
    return list_cell(lst);
  }
  if (tav(t,"unary","[")) {
    assert(t.sub.length==1);
    assert(t.sub[0].arity=="array");
    return list_cell(sym_cell("new_array")~as_list(token2cell(t.sub[0])));
  }
  if (tav(t,"unary","typeof")) {
    assert(t.sub.length==1);
    return list_cell([sym_cell("typeof"),token2cell(t.sub[0])]);
  }
  if (tav(t,"parameter")) {
    Cell[] cs=tokens2cells(t.sub);
    if (cs.length==3) cs=[cs[0],cs[1],sym_cell("="),cs[2]];
    return list_cell(cs);
  }
  if (tav(t,"type")) {
    if (t.id=="(name)") return sym_cell(t.value);
    if (t.id=="assoc") {
      return list_cell([sym_cell("assoc")]~tokens2cells(t.sub));
    }
    if (t.id=="struct") {
      return list_cell([sym_cell("struct")]~tokens2cells(t.sub));
    }
    if (t.id=="union") {
      return list_cell([sym_cell("union")]~tokens2cells(t.sub));
    }
    if (t.id=="[") {
      return list_cell([sym_cell("array")]~tokens2cells(t.sub));
    }
    if (t.id=="@") {
      return list_cell([sym_cell("ref")]~tokens2cells(t.sub));
    }
    if (t.id==";") {
      assert(t.sub.length==1);
      return token2cell(t.sub[0]);
    }
  }
  if (tav(t,"statement","deftype")) {
    Cell type=token2cell(t.sub[0]);
    return list_cell([sym_cell("deftype"),sym_cell(t.name),type]);
  }
  if (tav(t,"statement","aliastype")) {
    Cell type=token2cell(t.sub[0]);
    return list_cell([sym_cell("aliastype"),sym_cell(t.name),type]);
  }
  if (tav(t,"statement","supertype")) {
    return list_cell([sym_cell("supertype"),sym_cell(t.name)]~tokens2cells(t.sub));
  }
  if (tav(t,"statement","defun")) {
    Cell pars=token2cell(t.sub[0]);
    Cell code=token2cell(t.sub[1]);
    if (t.sub[1].arity=="array") code.lst=sym_cell("seq")~code.lst;
    return list_cell([sym_cell("defun"),sym_cell(t.name),pars,code]);
  }
  if (tav(t,"function","function")) {
    Cell pars=token2cell(t.sub[0]);
    Cell code=token2cell(t.sub[1]);
    if (t.sub[1].arity=="array") code.lst=sym_cell("seq")~code.lst;
    return list_cell([sym_cell("function"),pars,code]);
  }
  if (tav(t,"statement","def")) {
    if (t.sub.length==2) {
      return list_cell([sym_cell("def")]~tokens2cells(t.sub));
    }
    if (t.sub.length==3) {
      return list_cell([sym_cell("def")]~tokens2cells(t.sub));
    }
    assert(false);
  }
  if (tav(t,"statement","scope")) {
    if (t.sub.length==1) {
      assert(t.sub[0].arity=="array");
      return list_cell([sym_cell("scope"),token2cell(t.sub[0])]);
    }
    if (t.sub.length==2) {
      assert(t.sub[0].arity=="name");
      assert(t.sub[1].arity=="array");
      return list_cell([sym_cell("scope"),sym_cell(t.sub[0].value),token2cell(t.sub[1])]);
    }
    assert(false);
  }
  if (tav(t,"statement","if")) {
    if (t.sub.length==2) {
      Cell c=list_cell([sym_cell("if")]~tokens2cells(t.sub));
      if (t.sub[1].arity=="array") c.lst[2].lst=sym_cell("seq")~c.lst[2].lst;
      return c;
    }
    if (t.sub.length==3) {
      Cell c=list_cell([sym_cell("if")]~tokens2cells(t.sub));
      if (t.sub[1].arity=="array") c.lst[2].lst=sym_cell("seq")~c.lst[2].lst;
      if (t.sub[2].arity=="array") c.lst[3].lst=sym_cell("seq")~c.lst[3].lst;
      return c;
    }
    assert(false);
  }
  if (tav(t,"statement","for")) {
    assert(t.sub.length==4);
    Cell c=list_cell([sym_cell("for")]~tokens2cells(t.sub));
    //printf("%.*s\n",cells.str(c));
    if (t.sub[0].arity=="array") c.lst[1].lst=sym_cell("seq")~c.lst[1].lst;
    if (t.sub[3].arity=="array") c.lst[4].lst=sym_cell("seq")~c.lst[4].lst;
    //printf("%.*s\n",cells.str(c));
    return c;
  }
  if (tav(t,"statement","while")) {
    assert(t.sub.length==2);
    Cell c=list_cell([sym_cell("while")]~tokens2cells(t.sub));
    if (t.sub[1].arity=="array") c.lst[2].lst=sym_cell("seq")~c.lst[2].lst;
    return c;
  }
  if (tav(t,"statement","do")) {
    assert(t.sub.length==2);
    Cell c=list_cell([sym_cell("dowhile")]~tokens2cells(t.sub));
    if (t.sub[0].arity=="array") c.lst[1].lst=sym_cell("seq")~c.lst[1].lst;
    return c;
  }
  if (tav(t,"unary","!")) {
    assert(t.sub.length==1);
    return list_cell([sym_cell("not"),token2cell(t.sub[0])]);
  }
  if (tav(t,"ternary","?")) {
    assert(t.sub.length==3);
    return list_cell([sym_cell("if")]~tokens2cells(t.sub));
  }
  if (tav(t,"statement","switch")) {
    Cell[] lst=[sym_cell("switch")]~tokens2cells(t.sub);
    for (int k=1;k<lst.length;k+=2) {
      if (isa(lst[k],TList)) lst[k].lst=sym_cell("seq")~lst[k].lst;
    }
    return list_cell(lst);
  }
  if (tav(t,"statement","break")) {
    assert(!t.sub.length);
    return list_cell([sym_cell("break")]);
  }
  if (tav(t,"statement","continue")) {
    assert(!t.sub.length);
    return list_cell([sym_cell("continue")]);
  }
  if (tav(t,"statement","return")) {
    if (!t.sub.length) {
      return list_cell([sym_cell("return")]);
    }
    if (t.sub.length==1) {
      return list_cell([sym_cell("return"),token2cell(t.sub[0])]);
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
    c.lst~=[sym_cell("call"),token2cell(t.sub[0]),sym_cell(t.sub[1].value)];
    if (!tav(t.sub[2],"array")) assert(false);
    c.lst~=token2cell(t.sub[2]).lst;
    return c;
  }
  if (tav(t,"binary",".")) {
    Cell c=list_cell();
    c.lst~=sym_cell("get");
    c.lst~=token2cell(t.sub[0]);
    c.lst~=str_cell(t.sub[1].value);
    return c;
  }
  if (tav(t,"binary","[")) {
    Cell c=list_cell();
    c.lst~=sym_cell("get");
    c.lst~=token2cell(t.sub[0]);
    c.lst~=token2cell(t.sub[1]);
    return c;
  }
  if (tav(t,"binary")) {
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
      c.lst~=sym_cell("set");
      c.lst~=token2cell(t.sub[0].sub[0]);
      c.lst~=str_cell(t.sub[0].sub[1].value);
    } else if (tav(t.sub[0],"binary","[")) {
      c.lst~=sym_cell("set");
      c.lst~=token2cell(t.sub[0].sub[0]);
      c.lst~=token2cell(t.sub[0].sub[1]);
    } else if (tav(t.sub[0],"unary","@")) {
      c.lst~=sym_cell("set");
      c.lst~=token2cell(t.sub[0].sub[0]);
    } else {
      c.lst~=sym_cell("=");
      c.lst~=token2cell(t.sub[0]);
    }
    c.lst~=token2cell(t.sub[1]);
    return c;
  }
  if (tav(t,"unary")) {
    return list_cell([sym_cell(t.value),token2cell(t.sub[0])]);
  }
  if (tav(t,"binary")) {
    return list_cell([sym_cell(t.value),token2cell(t.sub[0]),token2cell(t.sub[1])]);
  }
  if (tav(t,"array")) {
    return list_cell(tokens2cells(t.sub));
  }
  t.error("js-to-lisp error");
}
