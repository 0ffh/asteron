module front;

import std.file;
import std.string;
import std.regexp;

import debg;
import utils;
import lexer;
import cells;
import types;
import signatures;
import environments;

alias std.string.toStringz tsz;
alias std.regexp.search search;

//------------------------------------------------------------
//------------------------------------------------------------
//-------------------- tdop.d
//--------------------

int max(int a,int b){return (a>b)?a:b;}

alias Cell function(Token self) Nudfun;
alias Cell function(Token self,Cell left) Ledfun;

Cell null_led(Token self,Cell left) {
  printf("Led not implemented in ");
  self.show();
  assert(false,"LED: Not implemented");
  return null_cell();
}
Cell null_nud(Token self) {
  printf("Nud not implemented in ");
  self.show();
  assert(false,"NUD: Not implemented");
  return null_cell();
}
class TokenSrc {
  Token[] tokens;
  int     pos;
  Token   token;
  Token next() {
    ++pos;
    Token t;
    if (tokens.length>pos) {
      t=tokens[pos];
/*      printf("#%i ",pos);
      t.show();*/
    }
    token=t;
    return t;
  }
  void reset() {
    pos=0;
    token=tokens[0];
  }
  this(Token[] tokens) {
    this.tokens=tokens;
    foreach (ref t;tokens)
      t.ts=this;
    reset();
  }
}
class Token {
  string   tag;
  string   val;
  int      lbp;
  Ledfun   ledf;
  Nudfun   nudf;
  Lexem    lex;
  TokenSrc ts;
  static   int       count;
  static   Token[]   tokens;
  Cell led(Cell left) {
    return ledf(this,left);
  }
  Cell nud() {
    return nudf(this);
  }
  void show() {
    printf("Token\n");
    printf("  tag='%s'\n",tsz(tag));
    printf("  val='%s'\n",tsz(val));
    printf("  lbp=%i\n",lbp);
  }
  this(string tag,int lbp=0,string val="",Ledfun led=null,Nudfun nud=null) {
    if (!led) led=&null_led;
    if (!nud) nud=&null_nud;
    this.tag=tag;
    this.val=val;
    this.lbp=lbp;
    this.ledf=led;
    this.nudf=nud;
    ++count;
    tokens~=this;
  }
  Token clone() {
    Token t=new Token(tag,lbp,val,ledf,nudf);
    t.lex=lex;
    t.ts=ts;
    return t;
  }
};

//------------------------------------------------------------
//------------------------------------------------------------
//-------------------- parser
//--------------------

class Symbols {
  static Token[string] memo;
  Token token(string tag,string val="") {
    Token *t=(tag in memo);
    assert(t,format("unknown token tag '%s'",tag));
    if (val!="") {
      string tag_val=tag~" "~val;
      Token *u=(tag_val in memo);
      if (u)
        return *u;
      *t=t.clone();
      t.val=val;
      memo[tag_val]=*t;
    }
    return *t;
  }
  Token make(string tag,int lbp=0) {
    if (Token *t=(tag in memo)) {
      t.lbp=max(t.lbp,lbp);
      return *t;
    }
    Token t=new Token(tag,lbp);
    t.val=tag;
    memo[tag]=t;
    return t;
  }
}
Token mk_infix(Symbols sym,string tag,int lbp=0) {
  Token t=sym.make(tag,lbp);
  t.ledf=function Cell(Token self,Cell left) {
    static if (debf) {debEnter("infix.LED");scope (exit) debLeave();}
//      printf("LED ");self.show();
    Cell right=expression(self.ts,self.lbp);
    return list_cell([sym_cell(self.tag),left,right]);
  };
  return t;
}
Token mk_infixr(Symbols sym,string tag,int lbp=0) {
  Token t=sym.make(tag,lbp);
  t.ledf=function Cell(Token self,Cell left) {
    static if (debf) {debEnter("infixr.LED");scope (exit) debLeave();}
//      printf("LED ");self.show();
    Cell right=expression(self.ts,self.lbp-1);
    return list_cell([sym_cell(self.tag),left,right]);
  };
  return t;
}
void advance(TokenSrc ts,string val="") {
  if (val.length) {
    assert(ts.token.val==val,"expected "~val~" not "~ts.token.val);
  }
  ts.next();
}
int is_local_end_token(Token t) {
  int res=((t.tag=="[END]") || (t.tag=="}") || (t.tag=="]") || (t.tag==")"));
  //dprln("is_local_end_token ",t.tag,":",t.val," -> ",res)
  return res;
}
int is_local_end_semi_token(Token t) {
  int res=is_local_end_token(t) || (t.tag==";");
  //dprln("is_local_end_semi_token ",t.tag,":",t.val," -> ",res)
  return res;
}
int is_local_end_cons_token(Token t) {
  int res=is_local_end_token(t) || (t.tag==":") || (t.tag==",") || (t.tag==";");
  //dprln("is_local_end_semi_token ",t.tag,":",t.val," -> ",res)
  return res;
}
void init_symbols(Symbols sym) {
  Token t;
  //--- end token
  sym.make("[END]",-1);
  //--- semicolon, binds with 2
  t=mk_infixr(sym,";",2);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("semicolon.LED");scope (exit) debLeave();}
      if (is_local_end_token(self.ts.token)) {
        return left;
      }
      Cell right=expression(self.ts,self.lbp-1);
      return list_cell([sym_cell(";"),left,right]);
    };
  //--- colon, binds with 4
  t=mk_infixr(sym,":",85);
//  t=mk_infixr(sym,":",4);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("colon.LED");scope (exit) debLeave();}
      if (is_local_end_token(self.ts.token)) {
        return left;
      }
      Cell right=expression(self.ts,self.lbp-1);
      return list_cell([sym_cell(":"),left,right]);
    };
  //--- juxtaposition, binds with 6 (otherwhere)
  //--- comma, binds with 8
  t=mk_infixr(sym,",",8);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("comma.LED");scope (exit) debLeave();}
      if (is_local_end_token(self.ts.token)) {
        return left;
      }
      Cell right=expression(self.ts,self.lbp-1);
      return list_cell([sym_cell(","),left,right]);
    };
  //--- arithmetic
  mk_infixr(sym,"=",10);
  mk_infixr(sym,"+=",10);
  mk_infixr(sym,"-=",10);
  mk_infixr(sym,"*=",10);
  mk_infixr(sym,"/=",10);
  mk_infixr(sym,"%=",10);
  mk_infixr(sym,"&=",10);
  mk_infixr(sym,"|=",10);
  mk_infixr(sym,"^=",10);
  mk_infixr(sym,"<<=",10);
  mk_infixr(sym,">>=",10);
  mk_infixr(sym,"~=",10);
  mk_infix(sym,"||",20);
  mk_infix(sym,"&&",21);
  mk_infix(sym,"|",22);
  mk_infix(sym,"^",23);
  mk_infix(sym,"&",24);
  mk_infix(sym,"==",30);
  mk_infix(sym,"!=",30);
  mk_infix(sym,"<",40);
  mk_infix(sym,"<=",40);
  mk_infix(sym,">",40);
  mk_infix(sym,">=",40);
  mk_infix(sym,"<<",50);
  mk_infix(sym,">>",50);
  mk_infix(sym,"+",60);
  mk_infix(sym,"-",60);
  mk_infix(sym,"*",70);
  mk_infix(sym,"/",70);
  mk_infix(sym,"+",60);
  mk_infix(sym,"-",60);
  mk_infix(sym,"*",70);
  mk_infix(sym,"/",70);
  mk_infix(sym,"%",70);
  mk_infix(sym,"**",80);
  mk_infix(sym,"^",80);
  mk_infix(sym,".",120);
  //---
  t=sym.make("-");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("-.NUD");scope (exit) debLeave();}
      return list_cell([sym_cell("neg"),expression(self.ts,100)]);
    };
  //---
  t=sym.make("!");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("!.NUD");scope (exit) debLeave();}
      return list_cell([sym_cell("not"),expression(self.ts,100)]);
    };
  //---
  t=sym.make("$");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("$.NUD");scope (exit) debLeave();}
      return list_cell([sym_cell("$"),expression(self.ts,7)]);
    };
  //---
  t=sym.make("?");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("?.NUD");scope (exit) debLeave();}
      return list_cell([sym_cell("?"),expression(self.ts,95)]);
    };
  //---
  t=sym.make(r"\");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("\\.NUD");scope (exit) debLeave();}
      return list_cell([sym_cell(`\`),expression(self.ts,95)]);
    };
  //---
  t=sym.make("#",90);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("#.LED");scope (exit) debLeave();}
      return list_cell([sym_cell(`ref`),left]);
    };
  //---
  t=sym.make("@",90);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("@.LED");scope (exit) debLeave();}
      return list_cell([sym_cell(`deref`),left]);
    };
  //---
  sym.make("}");
  t=sym.make("{");
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("{.NUD");scope (exit) debLeave();}
      Token token=self.ts.token;
      if (token.tag=="}") {
        advance(self.ts,"}");
        return list_cell([sym_cell(`curly`)]);
      } else {
        Cell n=list_cell([sym_cell(`curly`),expression(self.ts,1)]);
        advance(self.ts,"}");
        return n;
      }
    };
  //---
  sym.make("]");
  t=mk_infix(sym,"[",90);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("[.LED");scope (exit) debLeave();}
      Token token=self.ts.token;
      if (token.tag=="]") {
        advance(self.ts,"]");
        return list_cell([sym_cell(`index`),left]);
      } else {
        Cell n=list_cell([sym_cell(`index`),left,expression(self.ts,1)]);
        advance(self.ts,"]");
        return n;
      }
    };
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("[.NUD");scope (exit) debLeave();}
      Token token=self.ts.token;
      if (token.tag=="]") {
        advance(self.ts,"]");
        return list_cell([sym_cell(`bracket`)]);
      } else {
        Cell n=list_cell([sym_cell(`bracket`),expression(self.ts,1)]);
        advance(self.ts,"]");
        return n;
      }
    };
  //---
  sym.make(")");
  t=mk_infix(sym,"(",90);
  t.ledf=
    function Cell(Token self,Cell left) {
      static if (debf) {debEnter("(.LED");scope (exit) debLeave();}
      Token token=self.ts.token;
      if (token.tag==")") {
        advance(self.ts,")");
        return list_cell([sym_cell(`brace`),left]);
      } else {
        Cell n=list_cell([sym_cell(`brace`),left,expression(self.ts,1)]);
        advance(self.ts,")");
        return n;
      }
    };
  t.nudf=
    function Cell(Token self) {
      static if (debf) {debEnter("(.NUD");scope (exit) debLeave();}
      Token token=self.ts.token;
      if (token.tag==")") {
        advance(self.ts,")");
        return list_cell([sym_cell(`brace`)]);
      } else {
        Cell n=list_cell([sym_cell(`brace`),expression(self.ts,1)]);
        advance(self.ts,")");
        return n;
      }
    };
  //--- integer
  t=sym.make("int");
  t.nudf=function Cell(Token self) {
    static if (debf) {debEnter("int.NUD");scope (exit) debLeave();}
//      printf("NUD ");self.show();
    return int_cell(cast(int)(atof(self.val)));
  };
  //--- float
  t=sym.make("flt");
  t.nudf=function Cell(Token self) {
    static if (debf) {debEnter("flt.NUD");scope (exit) debLeave();}
//      printf("NUD ");self.show();
    return float_cell(atof(self.val));
  };
  //--- string
  t=sym.make("str");
  t.nudf=function Cell(Token self) {
    static if (debf) {debEnter("str.NUD");scope (exit) debLeave();}
//      printf("NUD ");self.show();
    return str_cell(self.val);
  };
  //--- id
  t=sym.make("id");
  t.nudf=function Cell(Token self) {
    static if (debf) {debEnter("id.NUD");scope (exit) debLeave();}
//      printf("NUD ");self.show();
    return sym_cell(self.val);
  };
}
/*
Cell expression0(TokenSrc ts,int rbp=0) {
  Token t=ts.token;
  ts.next();
  Cell left=t.nud();
  while (rbp<ts.token.lbp) {
    t=ts.token;
    ts.next();
    left=t.led(left);
  }
  return left;
}
*/
Cell expression(TokenSrc ts,int rbp=0) {
  static if (debf) {debEnter("expression(%i)",rbp);scope (exit) debLeave();}
  Token t;
  Cell left=null_cell();
  for (;;) {
    //ts.token.show();
    //printf("left.type = %p\n",left.type);
    //printf("left.type = %.*s\n",types.str(left.type));
    if (left.type==TNull) {
      if (is_local_end_token(ts.token)) return null_cell();
      t=ts.token;
      ts.next();
      left=t.nud();
    } else if (rbp<ts.token.lbp) {
      t=ts.token;
      ts.next();
      left=t.led(left);
    } else if ((rbp<=6)&&(!is_local_end_cons_token(ts.token))) {
      left=list_cell([left,expression(ts,6)]);
    } else {
      break;
    }
  }
  return left;
}
Cell raw_parse(string source) {
//  static Cell[string] memo; // memoize -- later
  Lexem[] lexemes=lex(source);
  //-- init sym
  Symbols sym=new Symbols();
  init_symbols(sym);
//  if (sym) return null_cell();
  Token[] tokens;
  foreach (lexem;lexemes) {
//    printf("%s:%s\n",tsz(LTAGS[lexem.tag]),tsz(lexem.val));
    switch (lexem.tag) {
      case LTAG.INT   : tokens~=sym.token("int",lexem.val);break;
      case LTAG.FLT   : tokens~=sym.token("flt",lexem.val);break;
      case LTAG.STR   : tokens~=sym.token("str",lexem.val);break;
      case LTAG.SYM   : tokens~=sym.token("id",lexem.val);break;
      case LTAG.OP    : tokens~=sym.token(lexem.val);break;
      case LTAG.WS    : break;
      case LTAG.REM   : break;
      default         : printf("[%s:%s]\n",tsz(LTAGS[lexem.tag]),tsz(lexem.val));
    }
  }
  tokens~=sym.token("[END]");
  TokenSrc ts=new TokenSrc(tokens);
  //-- show tokens
  if (0) {
    foreach (t;tokens) {
      printf("%s_",tsz(t.val));
      t.show();
    }
    printf("\n");
  }
  printf("tokens generated : %i (%i)\n",Token.count,tokens.length);
  //--
  Cell n=expression(ts);
  return n;
};
Env* global_env;
void main() {
  global_env=mk_env();
  init_types(global_env);
  Cell h=raw_parse(cast(string)std.file.read("test.ast"));
  printf("%.*s\n",cells.str(h));
}
