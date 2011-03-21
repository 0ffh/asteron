module lexer;

import debg;
import utils;
import std.file;
import std.string;
import std.regexp;

alias std.string.toStringz tsz;
alias std.regexp.search search;
alias string function(string m) LtFun;

int index_to_line(string txt,int idx) {
  int line=1;
  int pos;
  if (idx>txt.length) idx=txt.length;
  while (pos<idx) line+=(txt[pos++]=='\n');
  return line;
}
class Lexeme {
  string  type;
  string  val;
  string  src;
  int     idxs,idxe;
  int line() {
    return index_to_line(src,idxs);
  }
  string str() {
    string s="Lexeme\n";
    s~=cfrm("  type  = _%s_\n",tsz(type));
    s~=cfrm("  value = _%s_\n",tsz(val));
    s~=cfrm("  idx   = [%i..%i]\n",idxs,idxe);
    return s;
  }
  void show() {
    printf("%s",str());
  }
  string error_string(string s) {
    return str()~cfrm("Error around line %i: %.*s\n",line(),s);
  }
  void error(string s,string f="",long l=0) {
    s=error_string(s);
    if (f.length) {
      if (l) {
        s="["~f~":"~cfrm("%lu",l)~"] "~s;
      } else {
        s="["~f~"] "~s;
      }
    }
    printf("%.*s\n",s);
    assert(false,s);
  }
  this(string val,string type="") {
    this.type=type;
    this.val=val;
  }
  this() {
  }
};

struct LextabEntry {
  string  type;
  string  pat;
  LtFun   fun;
  RegExp  rex;
};
alias LextabEntry[] Lextab;

Lextab mkLispLextab() {
  static if (debf) {debEnter("mkLextab");scope (exit) debLeave();}
  LextabEntry le;
  Lextab lt;
  lt~=LextabEntry("ws",`\s+`);
  lt~=LextabEntry("remark",`//[^\n]*`,
    function string(string m) {
      return m[3..$];
    });
  lt~=LextabEntry("remark",`/[*](.|\s)*?[*]/`,
    function string(string m) {
      return m[3..$-3];
    });
  lt~=LextabEntry("string",`"([^\\"]|\\.)*"`,
    function string(string m) {
      return m[1..$-1];
    });
  lt~=LextabEntry("string",`'([^\\']|\\.)*'`,
    function string(string m) {
      return m[1..$-1];
    });
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*\.[_0-9]*([eE][+-]?[_0-9.]*)?`);
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*[eE][+-]?[_0-9.]+`);
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*`);
  lt~=LextabEntry("operator",`[()]`);
  lt~=LextabEntry("operator",`[^()\x09\x0a\x0b\x0c\x0d\x20]+`);
  foreach (ref e;lt) {
    e.rex=new RegExp("^"~e.pat);
  };
  return lt;
};
Lextab mkAstLextab() {
  static if (debf) {debEnter("mkLextab");scope (exit) debLeave();}
  LextabEntry le;
  Lextab lt;
  lt~=LextabEntry("ws",`\s+`);
  lt~=LextabEntry("remark",`//[^\n]*`,
    function string(string m) {
      //printf("[%.*s]\n",m);
      return m[2..$];
    });
  lt~=LextabEntry("remark",`/[*](.|\s)*?[*]/`,
    function string(string m) {
      return m[2..$-2];
    });
  lt~=LextabEntry("string",`"([^\\"]|\\.)*"`,
    function string(string m) {
      return m[1..$-1];
    });
  lt~=LextabEntry("string",`'([^\\']|\\.)*'`,
    function string(string m) {
      return m[1..$-1];
    });
  lt~=LextabEntry("operator",`(\+\+|--)`);
  lt~=LextabEntry("name",`(\.\.\.)`);
  lt~=LextabEntry("operator",`[!*/<>&|=~^+-]*[=]`);
  lt~=LextabEntry("operator",`[!*/<>&|=~^+-][<>&|=]*`);
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*\.[_0-9]*([eE][+-]?[_0-9.]*)?`);
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*[eE][+-]?[_0-9.]+`);
  lt~=LextabEntry("number",`[+-]?[0-9][_0-9]*`);
  lt~=LextabEntry("name",`[_a-zA-Z][_a-zA-Z0-9]*`);
  lt~=LextabEntry("operator",`[][(){},;.:?]`);
  lt~=LextabEntry("operator",`[%#@$?\\]`);
  foreach (ref e;lt) {
    e.rex=new RegExp("^"~e.pat);
  };
  return lt;
};
private Lexeme[] lex(string src,Lextab lt) {
  static if (debf) {debEnter("lex");scope (exit) debLeave();}
  if (!lt.length) {
    assert(false,"lex: No lexer table given!");
  }
  Lexeme[] tokens;
  int index=0;
  while (index<src.length) {
    //printf("search in '%.*s'\n",deCtrl(src[index..min($,index+20)]));
    int ok=0;
    foreach (e;lt) {
      Lexeme t=new Lexeme();
//      printf("test %i : %s\n",e.type,tsz(e.pat));
      foreach (me;e.rex.search(src[index..$])) {
        t.type=e.type;
        t.val=me.match(0);
        t.src=src;
        t.idxs=index;
        index+=t.val.length;
        t.idxe=index-1;
        if (e.fun) t.val=e.fun(t.val);
//        printf("match : %s\n",dsz(t.val));
        if ((t.type!="white")&&(t.type!="remark")) tokens~=t;
        ok=1;
      }
      if (ok) break;
    }
    if (!ok) {
      printf("stumped by '%.*s'\n",deCtrl(src[index..min($,index+20)]));
      assert(false,"lexing failed");
    }
  }
  return tokens;
};
Lextab lispLextab;
Lexeme[] llex(string src) {
  if (!lispLextab.length) lispLextab=mkLispLextab();
  return lex(src,lispLextab);
}
Lextab astLextab;
Lexeme[] astlex(string src) {
  if (!astLextab.length) astLextab=mkAstLextab();
  return lex(src,astLextab);
}
