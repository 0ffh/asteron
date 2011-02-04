module llparse;

import debg;
import lexer;
import cells;
import types;
import environments;
import utils;
import std.conv;
import std.string;

int max(int a,int b){return (a>b)?a:b;}

alias Token function(Token self) Nudfun;
alias Token function(Token self,Token left) Ledfun;

const bool debflag=debf && true;

//------------------------------------------------------------
//------------------------------------------------------------
//--------------------
//-------------------- global variables
//--------------------

Token token;
Token[string] symbol_table;
Lexeme[] lexemes;
int lexeme_nr=0;
Lexeme lexeme;
Scope skope;

//------------------------------------------------------------
//------------------------------------------------------------
//--------------------
//-------------------- class Token
//--------------------

Token itself(Token self) {
  return self;
}
Token null_nud(Token self) {
  static if (debflag) {debEnter("null_nud");scope (exit) debLeave();}
//  self.error("NUD: Not implemented");
  return self;
}
Token null_led(Token self,Token left) {
  static if (debflag) {debEnter("null_led");scope (exit) debLeave();}
  self.error("LED: Not implemented");
  return self;
}
class Token {
  string   id;
  string   value;
  string   arity;
  string   name;
  string   key;
  bool     reserved;
  bool     assignment;
  int      lbp;
  Nudfun   std;
  Nudfun   nud;
  Ledfun   led;
  Scope    skope;
  Token[]  sub;
  Lexeme   lex;
  void show() {
    show_short();
  }
  void show_long(int n=0) {
    indent(n);
    printf("Token {\n");
    indent(n);
    printf("  id    = '%s'\n",tsz(id));
    indent(n);
    printf("  value = '%s'\n",tsz(value));
    indent(n);
    printf("  arity = '%s'\n",tsz(arity));
    indent(n);
    printf("  lbp   = %i\n",lbp);
    for (int k;k<sub.length;++k) {
      indent(n);
      printf("  sub%i  = \n",k);
      sub[k].show_long(n+2);
    }
    indent(n);
    printf("}\n");
  }
  void show_short(int n=0) {
    printf("Token");
    printf(" id:'%.*s'",id);
    printf(" arity:'%.*s'",arity);
    if (value.length) printf(" value:'%.*s'",value);
    if (name.length) printf(" name:'%.*s'",name);
    if (key.length) printf(" key:'%.*s'",key);
    printf(" bp:%i\n",lbp);
    for (int k;k<sub.length;++k) {
      indent(n+1);
      printf("[%i] = ",k);
      sub[k].show_short(n+1);
    }
  }
  string[] k2name=["first","second","third"];
  void show_js(int n=0) {
    printf("%.*s\n",jstr());
  }
  string jstr(int n=0) {
    n+=2;
    string s;
    if (arity=="array") {
      if (sub.length>1) {
        s~="[";
        s~=sub[0].jstr(n);
        for (int k=1;k<sub.length;++k) {
          s~=",\n";
          s~=spaces(n);
          s~=sub[k].jstr(n);
        }
        s~="\n";
        s~=spaces(n-2);
        s~="]";
      } else if (sub.length==1) {
        s~="[";
        s~=sub[0].jstr(n);
        s~="\n";
        s~=spaces(n-2);
        s~="]";
      } else {
        s="[]";
      }
    } else if (arity=="(null)") {
      s~="null";
    } else if (arity=="literal") {
      s~="{\n";
      if (name.length)  s~=spaces(n)~"\"name\":\""~name~"\",\n";
      if (key.length)  s~=spaces(n)~"\"key\":\""~key~"\",\n";
      if (value.length) {
        if (lex.type=="number") {
          s~=spaces(n)~"\"value\":"~value~",\n";
        } else if (lex.type=="name") {
          if ((value=="true")||(value=="false")||(value=="null")) {
            s~=spaces(n)~"\"value\":"~value~",\n";
          } else {
            s~=spaces(n)~"\"value\":\""~value~"\",\n";
          }
        } else {
          s~=spaces(n)~"\"value\":\""~value~"\",\n";
        }
      }
      s~=spaces(n)~"\"arity\":\""~arity~"\"\n";
      s~=spaces(n-2);
      s~="}";
    } else {
      s~="{\n";
      if (name.length)  s~=spaces(n)~"\"name\":\""~name~"\",\n";
      if (key.length)  s~=spaces(n)~"\"key\":\""~key~"\",\n";
      if (value.length) s~=spaces(n)~"\"value\":\""~value~"\",\n";
      if (arity.length) s~=spaces(n)~"\"arity\":\""~arity~"\",\n";
      if (s[$-2]==',') s.length=s.length-2;
      for (int k;k<sub.length;++k) {
        s~=",\n";
        s~=spaces(n);
        s~="\""~k2name[k]~"\":";
        s~=sub[k].jstr(n);
      }
      s~="\n";
      s~=spaces(n-2);
      s~="}";
    }
    return s;
  }
  this(string id="",int lbp=0) {
    this.id=id;
    this.lbp=lbp;
    this.value="";
    this.arity="";
    this.std=null;
    this.nud=&null_nud;
    this.led=&null_led;
    this.reserved=false;
    this.skope=null;
  }
  this(string id,string ar,string va="",int lbp=0) {
    this.id=id;
    this.lbp=lbp;
    this.value=va;
    this.arity=ar;
    this.std=null;
    this.nud=&null_nud;
    this.led=&null_led;
    this.reserved=false;
    this.skope=null;
  }
  Token clone() {
    Token t=new Token(id,lbp);
    t.value=this.value;
    t.arity=this.arity;
    t.std=this.std;
    t.nud=this.nud;
    t.led=this.led;
    t.reserved=this.reserved;
    t.skope=this.skope;
    return t;
  }
  void error(string s) {
    this.show();
    if (lex) {
      lex.error(s);
    } else {
      printf("%.*s\n",s);
      assert(false,s);
    }
  }
};

//------------------------------------------------------------
//------------------------------------------------------------
//--------------------
//-------------------- class Scope
//--------------------

class Scope {
  Scope parent;
  Token[string] def;
  void pop() {
    static if (debflag) {debEnter("Scope.pop");scope (exit) debLeave();}
    skope=this.parent;
  }
  Token define(Token n) {
    static if (debflag) {debEnter("Scope.define");scope (exit) debLeave();}
    Token* t=(n.value in def);
    if (t) {
      if (t.reserved) {
        t.error("Already reserved '"~n.value~"'.");
      } else {
        t.error("Already defined '"~n.value~"'.");
      }
    }
    def[n.value]=n;
    n.reserved=false;
    n.nud=&itself;
    n.led=null;
    n.std=null;
    n.lbp=0;
    n.skope=skope;
    return n;
  }
  int exist(string n) {
    static if (debflag) {debEnter("Scope.exist");scope (exit) debLeave();}
    Scope e = this;
    Token* o;
    while (true) {
      o = (n in e.def);
      if (o) return 1;
      e = e.parent;
      if (!e) {
        o = (n in symbol_table);
        return o ? 1 : 0;
      }
    }
  }
  Token find(string n) {
    static if (debflag) {debEnter("Scope.find");scope (exit) debLeave();}
    Scope e = this;
    Token* o;
    while (true) {
      o = (n in e.def);
      if (o) return *o;
      e = e.parent;
      if (!e) {
        o = (n in symbol_table);
        return o ? *o : symbol_table["(name)"];
      }
    }
  }
  void reserve(Token n) {
    static if (debflag) {debEnter("Scope.reserve");scope (exit) debLeave();}
    if (n.arity != "name" || n.reserved) {
      return;
    }
    Token* t = (n.value in this.def);
    if (t) {
      if (t.reserved) {
        return;
      }
      if (t.arity == "name") {
        t.error("Already defined.");
      }
    }
    this.def[n.value] = n;
    n.reserved = true;
  }
}
Scope new_skope() {
  Scope s = skope;
  skope = new Scope();
  skope.parent = s;
  return skope;
};

//------------------------------------------------------------
//------------------------------------------------------------
//--------------------
//-------------------- helper stuff
//--------------------

Token type_token(string tn) {
  return new Token("(name)","type",tn);
}
Token symbol(string id,int bp=0) {
  static if (debflag) {debEnter("symbol");scope (exit) debLeave();}
  if (Token *s=(id in symbol_table)) {
    if (bp >= s.lbp) {
      s.lbp = bp;
    }
    return *s;
  } else {
    Token s = new Token();
    s.id = s.value = id;
    s.lbp = bp;
    symbol_table[id] = s;
    return s;
  }
}
Token advance(string id="") {
  static if (debflag) {debEnter("advance");scope (exit) debLeave();}
  if (lexeme_nr >= lexemes.length) {
    return token = symbol_table["(end)"];
  }
  if (id.length && (lexeme.val != id)) {
    lexeme.error("Expected '"~id~"'.");
  }
  Lexeme l = lexemes[lexeme_nr];
  lexeme_nr += 1;
  string v = l.val;
  string a = l.type;
  Token* o;
  if (a == "name") {
    o = cast(Token*)[skope.find(v)].ptr;
  } else if (a == "operator") {
    o = (v in symbol_table);
    if (!o) {
      l.error("Unknown operator.");
    }
  } else if ((a == "string") || (a ==  "number")) {
//    a = "literal";
    o = ("(literal)" in symbol_table);
  } else {
    l.error("Unexpected token.");
  }
  lexeme=l;
  token = o.clone();
  token.lex = l;
  token.value = v;
  token.arity = a;
  return token;
};
Token infix(string id,int bp,Ledfun led=null) {
  static if (debflag) {debEnter("infix");scope (exit) debLeave();}
  Token s = symbol(id, bp);
  if (led) {
    s.led = led;
  } else {
    s.led = function Token(Token self,Token left) {
    static if (debflag) {debEnter("infix.led");scope (exit) debLeave();}
      self.sub = [left,expression(self.lbp)];
      self.arity = "binary";
      return self;
    };
  }
  return s;
}
Token infixr(string id,int bp,Ledfun led=null) {
  static if (debflag) {debEnter("infixr");scope (exit) debLeave();}
  Token s = symbol(id, bp);
  if (led) {
    s.led = led;
  } else {
    s.led = function Token(Token self,Token left) {
      static if (debflag) {debEnter("infixr.led");scope (exit) debLeave();}
      self.sub = [left,expression(self.lbp-1)];
      self.arity = "binary";
      return self;
    };
  }
  return s;
}
Token prefix(string id,Nudfun nud=null) {
  static if (debflag) {debEnter("prefix");scope (exit) debLeave();}
  Token s = symbol(id);
  if (nud) {
    s.nud = nud;
  } else {
    s.nud = function Token(Token self) {
      static if (debflag) {debEnter("prefix.nud");scope (exit) debLeave();}
      skope.reserve(self);
      self.sub = [expression(70)];
      self.arity = "unary";
      return self;
    };
  }
  return s;
}
Token suffix(string id,Ledfun led=null) {
  static if (debflag) {debEnter("suffix");scope (exit) debLeave();}
  Token s = symbol(id);
  if (led) {
    s.led = led;
  } else {
    s.led = function Token(Token self,Token left) {
      static if (debflag) {debEnter("suffix.nud");scope (exit) debLeave();}
      skope.reserve(self);
      self.lbp = 75;
      self.sub = [left];
      self.arity = "unary";
      return self;
    };
  }
  return s;
}
Token assignment(string id) {
  static if (debflag) {debEnter("assignment");scope (exit) debLeave();}
  return infixr(id, 10, function Token(Token self,Token left) {
    static if (debflag) {debEnter("assignment.led");scope (exit) debLeave();}
    if ((left.id != ".") && (left.id != "[") && (left.id != "@") && (left.arity != "name")) {
      left.error("Bad lvalue.");
    }
    self.sub = [left,expression(9)];
    self.assignment = true;
    self.arity = "binary";
    return self;
  });
};
Token constant(string s,string v) {
  static if (debflag) {debEnter("constant");scope (exit) debLeave();}
  Token x = symbol(s);
  x.nud = function Token(Token self) {
    static if (debflag) {debEnter("constant.nud");scope (exit) debLeave();}
    skope.reserve(self);
    self.value = symbol_table[self.id].value;
    self.arity = "literal";
    return self;
  };
  x.value = v;
  return x;
};
Token statement() {
  static if (debflag) {debEnter("statement");scope (exit) debLeave();}
  Token n = token;
  Token v;
  if (n.std) {
    advance();
    skope.reserve(n);
    return n.std(n);
  }
  v = expression(0);
  if ((!v.assignment) && (v.id != "(") && (v.id != "++") && (v.id != "--")) {
    v.error("Bad expression statement.");
  }
  advance(";");
  return v;
};
Token[] statements() {
  static if (debflag) {debEnter("statements");scope (exit) debLeave();}
  Token[] a;
  Token s;
  while (true) {
    if ((token.id == "}") || (token.id == "(end)")) {
      break;
    }
    s = statement();
    if (s) {
      a ~= s;
    }
  }
  return a;
};
Token stmt(string s,Nudfun f) {
  static if (debflag) {debEnter("stmt");scope (exit) debLeave();}
  Token x = symbol(s);
  x.std = f;
  return x;
};
Token block() {
  static if (debflag) {debEnter("block");scope (exit) debLeave();}
  Token t = token;
  advance("{");
  if (!t.std) t.error("Std function expected");
  t=t.std(t);
  t=arraytoken_reduce(t);
  return t;
};
Token arraytoken_reduce(Token t) {
  if ((t.arity=="array") && (t.sub.length==1)) t=t.sub[0];
  return t;
}
Token arraytoken(Token[] ta,string arity="array") {
  static if (debflag) {debEnter("arraytoken");scope (exit) debLeave();}
  Token t=new Token();
  t.arity=arity;
  t.sub=[];
  foreach (a;ta) {
    if (a.arity==arity) {
      t.sub~=a.sub;
    } else {
      t.sub~=a;
    }
  }
  return t;
}
Token statement_or_block() {
  static if (debflag) {debEnter("statement_or_block");scope (exit) debLeave();}
  if (token.id == "{") {
    return block();
  } else {
    return statement();
  }
}
Token struct_type_constructor(string constructor) {
  static if (debflag) {debEnter("struct_type_constructor");scope (exit) debLeave();}
  advance(constructor);
  advance("{");
  Token[] a;
  Token t;
  new_skope();
  while (true) {
    t = type_name_value();
    a ~= t;
    if (token.id != ",") {
      break;
    }
    advance(",");
  }
  skope.pop();
  advance("}");
  t=arraytoken(a,"type");
  t.id = constructor;
  t.value = "";
  return t;
}
Token type_constructor() {
  static if (debflag) {debEnter("type_constructor");scope (exit) debLeave();}
  if (token.arity != "name") {
    token.error("Type expected to start with a name.");
  }
  if ((token.value=="struct")||(token.value=="union")) {
    return struct_type_constructor(token.value);
  }
  Token t=token;
  if (skope.find(t.value).arity!="type") t.error("Type expected to be based on another type");
  t=type_token(t.value);
  advance();
  if (token.id == ";") {
    Token n=token;
    n.arity = "type";
    n.sub = [t];
    t=n;
//printf("---A %.*s %.*s\n",t.value,token.value);
    return t;
  }
  while ((token.id == "[")||(token.id == "@")) {
    if (token.id == "[") {
      Token n=token;
      n.arity = "type";
      n.sub = [t];
      advance();
      if (token.id != "]") {
        n.sub ~= token;
        advance();
      }
      advance("]");
      t=n;
      continue;
    }
    if (token.id == "@") {
      Token n=token;
      n.arity = "type";
      n.sub = [t];
      advance();
      t=n;
      continue;
    }
    token.error("Illegal type constructor");
  }
  return t;
}
Token type_name_value() {
  static if (debflag) {debEnter("type_name_value");scope (exit) debLeave();}
  //-- check type
  Token t,n,typ;
  n = token;
  if (n.arity != "name") {
    n.error("Expected a new variable name or a type");
  }
  //printf("### name\n");
  //n.show();
  //skope.find(n.value).show();
  if (skope.find(n.value).arity=="type") {
    //printf("### type\n");
    typ=type_constructor();
    //typ.show();
    n = token;
    if (n.arity != "name") {
      n.error("Expected a new variable name");
    }
  } else {
    typ=skope.find("any");
  }
  //--
  skope.define(n);
  advance();
  if (token.id == "=") {
    t = token;
    advance("=");
    t = new Token();
    t.arity = "ternary";
    t.value = "type_name_value";
    t.sub = [typ,n,expression(0)];
  } else {
    t = new Token();
    t.arity = "binary";
    t.value = "type_name";
    t.sub = [typ,n];
  }
  return t;
}
void init_symbols() {
  Token t;
  //---
  symbol(":");
  symbol(";");
  symbol(",");
  symbol(")");
  symbol("]");
  symbol("}");
  symbol("else");
  symbol("...");
  symbol("(end)");
  symbol("(name)");
  symbol("(null)").arity="(null)";
  //---
  infix("+", 50);
  infix("-", 50);
  infix("*", 60);
  infix("/", 60);
  infix("===", 40);
  infix("!==", 40);
  infix("==", 40);
  infix("!=", 40);
  infix("<", 40);
  infix("<=", 40);
  infix(">", 40);
  infix(">=", 40);
  //---
  infix("?", 20, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'?'.led");scope (exit) debLeave();}
    self.sub = [left];
    self.sub ~= expression(0);
    advance(":");
    self.sub ~= expression(0);
    self.arity = "ternary";
    return self;
  });
  infix(".", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'.'.led");scope (exit) debLeave();}
    self.sub = [left];
    if (token.arity != "name") {
      token.error("Expected a property name.");
    }
    token.arity = "literal";
    self.sub ~= token;
    self.arity = "binary";
    advance();
    return self;
  });
  infix("[", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'['.led");scope (exit) debLeave();}
    self.sub = [left];
    Token[] a;
    if (token.id != "]") {
      while (true) {
        a ~= expression(0);
        if (token.id != ",") {
          break;
        }
        advance(",");
      }
    }
    advance("]");
    self.sub ~= a;
    self.arity = "binary";
    return self;
  });
  //---
  infixr("&&", 30);
  infixr("||", 30);
  //---
  infix("@", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'@'.led");scope (exit) debLeave();}
    self.sub = [left];
    self.arity = "unary";
    return self;
  });
  infix("++", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'++'.led");scope (exit) debLeave();}
    self.value = "postincrement";
    self.sub = [left];
    self.arity = "unary";
    return self;
  });
  infix("--", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'--'.led");scope (exit) debLeave();}
    self.value = "postdecrement";
    self.sub = [left];
    self.arity = "unary";
    return self;
  });
  //---
  prefix("-");
  prefix("+");
  prefix("--", function Token(Token self) {
    static if (debflag) {debEnter("'--'.nud");scope (exit) debLeave();}
    skope.reserve(self);
    self.value = "predecrement";
    self.sub = [expression(70)];
    self.arity = "unary";
    return self;
  });
  prefix("++", function Token(Token self) {
    static if (debflag) {debEnter("'++'.nud");scope (exit) debLeave();}
    skope.reserve(self);
    self.value = "preincrement";
    self.sub = [expression(70)];
    self.arity = "unary";
    return self;
  });
  prefix("!");
  prefix("&");
  prefix("typeof");
  prefix("(", function Token(Token self) {
    static if (debflag) {debEnter("'('.nud");scope (exit) debLeave();}
    Token e = expression(0);
    advance(")");
    return e;
  });
  //---
  assignment("=");
  assignment("+=");
  assignment("-=");
  assignment("*=");
  assignment("/=");
  //---
  constant("true", "true");
  constant("false", "false");
  constant("null", "null");
  constant("pi", "3.141592653589793");
  symbol("(literal)").nud = &itself;
  symbol("this").nud = function Token(Token self) {
    skope.reserve(self);
    self.arity = "this";
    return self;
  };
  //---
  stmt("{", function Token(Token self) {
    static if (debflag) {debEnter("'{'.std");scope (exit) debLeave();}
    new_skope();
    Token[] a = statements();
    advance("}");
    skope.pop();
    return arraytoken(a);
  });
  //---
  stmt("var", function Token(Token self) {
    static if (debflag) {debEnter("var.std");scope (exit) debLeave();}
    Token[] a;
    Token t;
    while (true) {
      t = type_name_value();
      t.arity = "statement";
      t.value = "def";
      a ~= t;
      if (token.id != ",") {
        break;
      }
      advance(",");
    }
    advance(";");
    return arraytoken(a);
  });
  stmt("for", function Token(Token self) {
    static if (debflag) {debEnter("for.std");scope (exit) debLeave();}
    new_skope();
    advance("(");
    self.sub = [];
    if (token.id==";") {
      self.sub ~= arraytoken([]);
    } else {
      self.sub ~= statement();//expression(0);
    }
    //advance(";");
    if (token.id==";") {
      self.sub ~= arraytoken([]);
    } else {
      self.sub ~= expression(0);
    }
    advance(";");
    if (token.id==")") {
      self.sub ~= arraytoken([]);
    } else {
      self.sub ~= expression(0);
    }
    advance(")");
    self.sub ~= statement_or_block();
    self.arity = "statement";
    skope.pop();
    return self;
  });
  stmt("do", function Token(Token self) {
    static if (debflag) {debEnter("do.std");scope (exit) debLeave();}
    self.sub = [statement_or_block()];
    advance("while");
    advance("(");
    self.sub ~= expression(0);
    advance(")");
    advance(";");
    self.arity = "statement";
    return self;
  });
  stmt("while", function Token(Token self) {
    static if (debflag) {debEnter("while.std");scope (exit) debLeave();}
    advance("(");
    self.sub = [expression(0)];
    advance(")");
    self.sub ~= statement_or_block();
    self.arity = "statement";
    return self;
  });
  symbol("case");
  stmt("switch", function Token(Token self) {
    static if (debflag) {debEnter("switch.std");scope (exit) debLeave();}
    advance("(");
    self.sub = [expression(0)];
    advance(")");
    advance("{");
    while (token.id == "case") {
      advance("case");
      self.sub ~= expression(0);
      //token.show();
      advance(":");
      Token[] a;
      while ((token.id != "case") && (token.id != "}")) a ~= statement();
      self.sub ~= arraytoken(a);
    }
    advance("}");
    self.arity = "statement";
    return self;
  });
  stmt("if", function Token(Token self) {
    static if (debflag) {debEnter("if.std");scope (exit) debLeave();}
    advance("(");
    self.sub = [expression(0)];
    advance(")");
    self.sub ~= statement_or_block();
    if (token.id == "else") {
      skope.reserve(token);
      advance("else");
//      self.sub ~= (token.id == "if") ? statement() : block();
      self.sub ~= statement_or_block();
    }
    self.arity = "statement";
    return self;
  });
  stmt("break", function Token(Token self) {
    static if (debflag) {debEnter("break.std");scope (exit) debLeave();}
    advance(";");
    if ((token.id != "}") && (token.id != "case")) {
      token.error("Unreachable statement.");
    }
    self.arity = "statement";
    return self;
  });
  stmt("continue", function Token(Token self) {
    static if (debflag) {debEnter("continue.std");scope (exit) debLeave();}
    advance(";");
    self.arity = "statement";
    return self;
  });
  stmt("return", function Token(Token self) {
    static if (debflag) {debEnter("return.std");scope (exit) debLeave();}
    if (token.id != ";") {
      self.sub = [expression(0)];
    }
    advance(";");
    /*
    // test fails when "if" takes statement instead of block
    if ((token.id != "}") && (token.id != "case")) {
      token.error("Unreachable statement.");
    }
    */
    self.arity = "statement";
    return self;
  });
  stmt("scope", function Token(Token self) {
    static if (debflag) {debEnter("scope.std");scope (exit) debLeave();}
    if (token.id!="{") {
      if (token.arity != "name") {
        token.error("Expected name of scope.");
      }
      self.sub ~= token;
      skope.define(token);
      advance();
    }
    new_skope();
    self.sub ~= block();
    self.arity = "statement";
    advance(";");
    skope.pop();
    return self;
  });
  stmt("deftype", function Token(Token self) {
    static if (debflag) {debEnter("deftype.std");scope (exit) debLeave();}
    if (token.arity != "name") {
      token.error("Expected name of type to define.");
    }
    self.name = token.value;
    self.arity = "statement";
    advance();
    Token type=type_constructor();
    type.value=self.name;
    //printf("constructed type\n  ");type.show_short(1);
    skope.define(type);
    self.sub=[type];
    advance(";");
    return self;
  });
  stmt("aliastype", function Token(Token self) {
    static if (debflag) {debEnter("aliastype.std");scope (exit) debLeave();}
    if (token.arity != "name") {
      token.error("Expected name of type to define.");
    }
    self.name = token.value;
    self.arity = "statement";
    advance();
    Token type=type_constructor();
    type.value=self.name;
    //printf("constructed type\n  ");type.show_short(1);
    skope.define(type);
    self.sub=[type];
    advance(";");
    return self;
  });
  stmt("supertype", function Token(Token self) {
    static if (debflag) {debEnter("supertype.std");scope (exit) debLeave();}
    if (token.arity != "name") {
      token.error("Expected name of type to define.");
    }
    self.name = token.value;
    self.value = "supertype";
    self.arity = "statement";
    if (skope.exist(token.value)) {
      if (skope.find(token.value).arity!="type") token.error("Supertype name is already used");
    } else {
      skope.define(type_token(token.value));
    }
    advance();
    while (true) {
      Token type=type_constructor();
      self.sub~=type;
      if (token.value==";") break;
      advance(",");
    }
    advance(";");
    return self;
  });
  stmt("defun", function Token(Token self) {
    static if (debflag) {debEnter("defun.std");scope (exit) debLeave();}
    Token[] a = [];
    new_skope();
    if (token.arity == "name") {
      skope.define(token);
      self.name = token.value;
      advance();
    }
    advance("(");
    if (token.id != ")") {
      while (true) {
        Token t = type_name_value();
        t.arity = "parameter";
        a ~= t;
        while (token.id == ",") {
          advance(",");
          t = type_name_value();
          t.arity = "parameter";
          a ~= t;
        }
        if (token.id != ";") break;
        advance(";");
      }
    }
    self.sub = [arraytoken(a)];
    advance(")");
    /*advance("{");
    self.sub ~= arraytoken_reduce(arraytoken(statements()));
    advance("}");*/
    self.sub ~= statement_or_block();
    self.arity = "statement";
    skope.pop();
    return self;
  });
  prefix("function", function Token(Token self) {
    static if (debflag) {debEnter("function.nud");scope (exit) debLeave();}
    Token[] a = [];
    new_skope();
    if (token.arity == "name") {
      skope.define(token);
      self.name = token.value;
      advance();
    }
    advance("(");
    if (token.id != ")") {
      while (true) {
        if (token.arity != "name") {
          token.error("Expected a parameter name.");
        }
        skope.define(token);
        a ~= token;
        advance();
        if (token.id != ",") {
          break;
        }
        advance(",");
      }
    }
    self.sub = [arraytoken(a)];
    advance(")");
    advance("{");
    self.sub ~= arraytoken_reduce(arraytoken(statements()));
    advance("}");
    self.arity = "function";
    skope.pop();
    return self;
  });
  infix("(", 80, function Token(Token self,Token left) {
    static if (debflag) {debEnter("'('.led");scope (exit) debLeave();}
    Token[] a;
    if ((left.id == ".") || (left.id == "[")) {
      self.arity = "ternary";
      assert(left.sub.length==2);
      self.sub = [left.sub[0],left.sub[1]];
    } else {
      self.arity = "binary";
      self.sub = [left];
      if (((left.arity != "unary") || (left.id != "function")) &&
           (left.arity != "name") && (left.id != "(") &&
           (left.id != "&&") && (left.id != "||") && (left.id != "?")) {
        left.error("Expected a variable name.");
      }
    }
    if (token.id != ")") {
      while (true)  {
        a ~= expression(0);
        if (token.id != ",") {
          break;
        }
        advance(",");
      }
    }
    self.sub~=arraytoken(a);
    advance(")");
    return self;
  });
  symbol("this").nud = function Token(Token self) {
    static if (debflag) {debEnter("this.nud");scope (exit) debLeave();}
    skope.reserve(self);
    self.arity = "this";
    return self;
  };
  prefix("[", function Token(Token self) {
    static if (debflag) {debEnter("'['.nud");scope (exit) debLeave();}
    Token[] a;
    if (token.id != "]") {
      while (true) {
        a ~= expression(0);
        if (token.id != ",") {
          break;
        }
        advance(",");
      }
    }
    advance("]");
    self.sub = [arraytoken(a)];
    self.arity = "unary";
    return self;
  });
  prefix("{", function Token(Token self) {
    static if (debflag) {debEnter("'{'.nud");scope (exit) debLeave();}
    Token[] a;
    if (token.id != "}") {
      while (true) {
        Token n = token;
        if ((n.arity != "name") && (n.arity != "literal") && (n.arity != "string")) {
          token.error("Bad key.");
        }
        advance();
        advance(":");
        Token v = expression(0);
        v.key = n.value;
        a ~= v;
        if (token.id != ",") {
          break;
        }
        advance(",");
      }
    }
    advance("}");
    self.sub = [arraytoken(a)];
    self.arity = "unary";
    return self;
  });
  //---
  //---
  //---
  //---
}

Token expression(int rbp) {
  static if (debflag) {debEnter("expression");scope (exit) debLeave();}
  Token left;
  Token t = token;
  advance();
  left = t.nud(t);
  while (rbp < token.lbp) {
    t = token;
    advance();
    left = t.led(t,left);
  }
  return left;
}

//------------------------------------------------------------
//------------------------------------------------------------
//--------------------
//-------------------- main functions
//--------------------

Lexeme[] rm_whitespaces(Lexeme[] lexemes) {
  int s,d;
  while (s<lexemes.length) {
    if ((lexemes[s].type=="ws")||(lexemes[s].type=="remark")) {
      ++s;
    } else {
      lexemes[d++]=lexemes[s++];
    }
  }
  lexemes.length=d;
  return lexemes;
}
void show(Lexeme[] lexemes) {
  int line=0;
  foreach (lexeme;lexemes) {
    int ll=lexeme.line();
    if (ll!=line) {
      printf("\n%4i ",line=ll);
    }
    printf("%.*s:'%.*s' ",lexeme.type,lexeme.val);
  }
  printf("\n");
}
void init_skope() {
  skope=new Scope();
  //- add types
  string[] tnames=["type","any","int","float","string","array","struct","union","assoc"];
  foreach (tn;tnames) skope.define(type_token(tn));
}
void init_tokens(string src) {
  static if (debflag) {debEnter("init_tokens");scope (exit) debLeave();}
  lexemes=rm_whitespaces(astlex(src));
  lexeme_nr=0;
  if (lexemes.length) lexeme=lexemes[lexeme_nr];
  init_skope();
  advance();
}
Token parse(string source) {
  static if (debflag) {debEnter("parse");scope (exit) debLeave();}
  init_symbols();
  init_tokens(source);
  Token t=arraytoken(statements());
  skope.pop();
  return t;
};

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- lisp parser
//----------------

Cell atom(Lexeme token) {
  static if (debflag) {debEnter("atom");scope (exit) debLeave();}
  if (token.type=="operator") return sym_cell(token.val);
  if (token.type=="name") return sym_cell(token.val);
  if (token.type=="string") return str_cell(token.val);
  if (token.type=="number") {
    try {
      return int_cell(toInt(token.val));
    } catch {
      return float_cell(toFloat(token.val));
    }
  }
  printf("*** [%.*s] ***\n",token.val);
  assert(false);
}
Cell lparse(Lexeme[] tokens,ref int pos) {
  static if (debflag) {debEnter("read_from(Lexeme[],int)");scope (exit) debLeave();}
  assert(tokens.length>pos,"unexpected EOF while reading");
  if (!pos) tokens=rm_whitespaces(tokens);
  Lexeme token=tokens[pos++];
  if (token.val=="(") {
    Cell c;
    c.type=TList;
    c.lst=[];
    while (tokens[pos].val!=")") c.lst~=lparse(tokens,pos);
    ++pos; // pop off ')'
    return c;
  }
  if (token.val==")") assert(false,"unexpected )");
  return atom(token);
}
Cell lparse(Lexeme[] tokens) {
  int pos=0;
  return lparse(rm_whitespaces(tokens),pos);
}
Cell lparse(string text) {
  return lparse(llex(text));
}
