module cells;

import debg;
import utils;
import types;
import environments;
import std.stdio;
import std.string;
import std.c.string;

int clothedStringDefault=0;

const bool debf=debflag && 0;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Lamb
//----------------

struct Lamb {
  Cell   expr;
  Cell[] pars;
  Env*   env;
}
Lamb* mk_lamb(Cell exp,Cell[] par,Env* en) {
  Lamb l;
  l.expr=exp;
  l.pars=par;
  l.env=en;
  return cast(Lamb*)[l].ptr;
}
Lamb* clone(Lamb* s) {
  Lamb d;
  d.expr=clone_cell(s.expr);
  d.pars.length=s.pars.length;
  for (int k;k<d.pars.length;++k) d.pars[k]=clone_cell(s.pars[k]);
  d.env=s.env;
  return cast(Lamb*)[d].ptr;
}
string[] lambda_parameter_names(Lamb* lam) {
  string[] par;
  for (int k;k<lam.pars.length;++k) {
    Cell[] cs=as_list(lam.pars[k]);
    par~=as_symbol(cs[1]);
  }
  return par;
}
string[] lambda_parameter_names(Cell lam) {
  return lambda_parameter_names(as_lambda(lam));
}
Cell[] lambda_parameter_defaults(Lamb* lam) {
  Cell[] par;
  for (int k;k<lam.pars.length;++k) {
//     writef("[%i:%s]",k,cells.str(lam.pars[k]));
    Cell[] cs=as_list(lam.pars[k]);
    if (cs.length>2) {
      par~=cs[2];
    } else {
      par~=null_cell();
    }
  }
//   writef("\n");
  return par;
}
Cell[] lambda_parameter_defaults(Cell lam) {
  return lambda_parameter_defaults(as_lambda(lam));
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Cell
//----------------

alias Cell function(Cell[]) lfn_type;
alias Cell function(Cell[]) fun_type;

struct TypeTable {
  Type[string] str2typ;
  string[Type] typ2str;
}
struct Assoc {
  Cell[string] inner;
}
struct Array {
  Cell[] inner;
}
struct Struct {
  string[] key;
  Cell[] val;
  Type[] typ;
}
struct Ref {
  string id;
  Env* env;
}
Type struct_get_fieldtype(Struct* s,string key) {
  for (int k;k<s.key.length;++k) {
    if (key==s.key[k]) return s.typ[k];
  }
  assert(false,"struct has not field "~key);
  return TNull;
}
Cell struct_get_field(Struct* s,string key) {
  for (int k;k<s.key.length;++k) {
    if (key==s.key[k]) return s.val[k];
  }
  assert(false,"struct has not field "~key);
  return null_cell();
}
Cell struct_set_field(Struct* s,string key,Cell val) {
  for (int k;k<s.key.length;++k) {
    if (key==s.key[k]) return s.val[k]=val;
  }
  assert(false,"struct has not field "~key);
}
struct Union {
  string[] key;
  Type[] typ;
  Cell val;
  int tag=-1;
}
Cell union_get(Union* u,string key) {
  if ((u.tag>=0) && (u.key[u.tag]==key)) return u.val;
  for (int k;k<u.key.length;++k) {
    if (key==u.key[k]) {
      assert(false,"trying to get union field "~key~", but last set was "~u.key[u.tag]);
    }
  }
  assert(false,"union has not field "~key);
  return null_cell();
}
Cell union_set(Union* u,string key,Cell val) {
  for (int k;k<u.key.length;++k) {
    if (key==u.key[k]) {
      u.tag=k;
      return u.val=val;
    }
  }
  assert(false,"union has not field "~key);
}
class Cell {
  Type type;
  union {
    Cell cel;
    Cell typ;
    string sym;
    string str;
    Cell[] lst;
    Array* arr;
    Ref* ptr;
    Struct* stc;
    Union* uni;
    Assoc* asc;
    float flt;
    int fix;
    FTab* ftab;
    fun_type fun;
    lfn_type lfn;
    Lamb* lam;
    Env* env;
    TypeTable* tyt;
  }
  Cell[string] ann;
  void show(int style=0) {
    writef("%s\n",cells.str(this,style));
  }
  static Cell opCall() {
    return new Cell();
  }
  Cell clone() {
    return clone_cell(this);
  }
  Cell set(Cell src) {
    src=src.clone();
    this.type=src.type;
    this.lst=src.lst;
    this.ann=src.ann;
    return this;
//    return copy_cell(this,c);
  }
}
Cell copy_cell(Cell dst,Cell src) {
  src=src.clone();
  dst.type=src.type;
  dst.lst=src.lst;
  dst.ann=src.ann;
  return dst;
}
Cell clone_cell(Cell self) {
  Cell c=Cell();
  c.ann=self.ann;
  if (self.type==TList) {
    c.type=TList;
    c.lst.length=self.lst.length;
    for (int k=self.lst.length;k--;) c.lst[k]=clone_cell(self.lst[k]);
    return c;
  }
  if (self.type==TLambda) {
    c.type=TLambda;
    c.lam=clone(self.lam);
    return c;
  }
//   memcpy(cast(void*)self,cast(void*)c,self.sizeof);
  c.type=self.type;
  c.lst=self.lst;
  return c;
}
Cell any_cell() {
  static if (debf) {debEnter("any_cell()");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TAny;
  return c;
}
Cell null_cell() {
  static if (debf) {debEnter("null_cell()");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TNull;
  return c;
}
Cell shell_cell(Cell v) {
  static if (debf) {debEnter("shell_cell(Cell)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TShell;
  c.cel=v;
  return c;
}
Cell symbol_cell(string val) {
  static if (debf) {debEnter("symbol_cell(string)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TSymbol;
  c.sym=val;
  return c;
}
Cell string_cell(string val) {
  static if (debf) {debEnter("string_cell(string)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TString;
  c.str=val;
  return c;
}
Cell float_cell(float val) {
  static if (debf) {debEnter("float_cell(float)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TFloat;
  c.flt=val;
  return c;
}
Cell int_cell(int val) {
  static if (debf) {debEnter("int_cell(int)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TInt;
  c.fix=val;
  return c;
}
Cell float_cell(string val) {
  static if (debf) {debEnter("float_cell(string)");scope (exit) debLeave();}
  return float_cell(atof(val));
}
Cell int_cell(string val) {
  static if (debf) {debEnter("int_cell(string)");scope (exit) debLeave();}
  return int_cell(atoi(val));
}
Cell list_cell(Cell[] val=[]) {
  static if (debf) {debEnter("list_cell(Cell[])");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TList;
  c.lst=val;
  return c;
}
Cell typetable_cell(TypeTable* val) {
  static if (debf) {debEnter("typetable_cell(TypeTable*)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TTypeTable;
  c.tyt=val;
  return c;
}
Cell assoc_cell(Cell[string] inner) {
  static if (debf) {debEnter("assoc_cell(Cell[])");scope (exit) debLeave();}
  Cell c=assoc_cell_from_subtype(TAny);
  c.asc.inner=inner;
  return c;
}
Cell assoc_cell_from_subtype(Type typ) {
  static if (debf) {debEnter("assoc_cell_from_subtype(Type)");scope (exit) debLeave();}
  return cell_from_assoc_type(assoc_type_from_subtype(typ));
}
Cell cell_from_assoc_type(Type typ) {
  static if (debf) {debEnter("cell_from_assoc_type(Type)");scope (exit) debLeave();}
  Cell c=Cell();
  Assoc val;
  c.type=typ;
  c.asc=cast(Assoc*)([val].ptr);
  return c;
}
Cell array_cell(Cell[] inner=[]) {
  static if (debf) {debEnter("array_cell(Cell[])");scope (exit) debLeave();}
  Cell c=cell_from_array_type(array_type_from_subtype(TAny));
  c.arr.inner=inner;
  return c;
}
Cell cell_from_array_type(Type typ) {
  static if (debf) {debEnter("cell_from_array_type(Type,Cell[])");scope (exit) debLeave();}
  Array a;
  if (is_static_array_type(typ)) {
    Type subtype=get_array_subtype(typ);
    int len=get_static_array_length(typ);
    a.inner.length=len;
    for (int k;k<len;++k) a.inner[k]=new_cell(subtype);
  }
  Cell c=Cell();
  c.type=typ;
  //writef("*** array_cell(%s)\n",types.str(c.type));
  c.arr=cast(Array*)([a].ptr);
  return c;
}
Cell cell_from_struct_type(Type t) {
  static if (debf) {debEnter("cell_from_struct_type(Type)");scope (exit) debLeave();}
  assert(is_struct_type(t));
  Struct s;
  Cell[] fields=get_compound_fields(t);
  for (int k;k<fields.length;++k) {
//    field.show();
    Cell[] lst=as_list(fields[k]);
    Type ftype=type(lst[0]);
    string fname=as_symbol(lst[1]);
    s.key~=fname;
    s.typ~=ftype;
    s.val~=new_cell(ftype);
  }
  Cell c=Cell();
  c.type=t;
  c.stc=cast(Struct*)([s].ptr);
  return c;
}
Cell cell_from_union_type(Type t) {
  static if (debf) {debEnter("cell_from_union_type(Type)");scope (exit) debLeave();}
  assert(is_union_type(t));
  Union u;
  Cell[] fields=get_compound_fields(t);
  for (int k;k<fields.length;++k) {
//    field.show();
    Cell[] lst=as_list(fields[k]);
    Type ftype=type(lst[0]);
    string fname=as_symbol(lst[1]);
    u.key~=fname;
    u.typ~=ftype;
  }
  u.val=null_cell();
  u.tag=-1;
  Cell c=Cell();
  c.type=t;
  c.uni=cast(Union*)([u].ptr);
  return c;
}
Cell cell_from_def_type(Type typ) {
  static if (debf) {debEnter("cell_from_def_type(Type)");scope (exit) debLeave();}
  Cell c=new_cell(get_def_subtype(typ));
  c.type=typ;
  return c;
}
Cell cell_from_alias_type(Type typ) {
  static if (debf) {debEnter("cell_from_alias_type(Type)");scope (exit) debLeave();}
  Cell c=new_cell(get_alias_subtype(typ));
  c.type=typ;
  return c;
//  return new_cell(get_alias_subtype(typ));
}
Cell cell_from_ref_type(Type typ) {
  static if (debf) {debEnter("cell_from_ref_type(Type,Cell[])");scope (exit) debLeave();}
  Ref r;
  Cell c=Cell();
  c.type=typ;
  //writef("%s\n",types.str(c.type));
  c.ptr=cast(Ref*)([r].ptr);
  return c;
}
Cell ref_cell(Env* env,string id) {
  static if (debf) {debEnter("ref_cell(Env*,string)");scope (exit) debLeave();}
  Ref r;
  r.env=env;
  r.id=id;
  Cell c=Cell();
  Type t=env_get(env,id).type;
  c.type=ref_type_from_subtype(t);
  c.ptr=cast(Ref*)([r].ptr);
  return c;
}
Cell ref_cell_on_heap(Cell v) {
  static if (debf) {debEnter("ref_cell(Env*,string)");scope (exit) debLeave();}
  Type t=ref_type_from_subtype(v.type);
  Cell c=cell_from_ref_type(t);
  Ref* r=c.ptr;
  r.env=mk_env();
  r.id="id";
  env_put(r.env,r.id,v);
  return c;
}
Cell ftab_cell(FTab* ft) {
  static if (debf) {debEnter("ftab_cell(Ftab)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TFtab;
  c.ftab=ft;
  return c;
}
Cell lambda_cell(Lamb* val) {
  static if (debf) {debEnter("lambda_cell(Lamb)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TLambda;
  c.lam=val;
  return c;
}
Cell fun_cell(fun_type val) {
  static if (debf) {debEnter("fun_cell(fun_type)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TFun;
  c.fun=val;
  return c;
}
Cell lfun_cell(lfn_type val) {
  static if (debf) {debEnter("lfun_cell(lfn_type)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TLfun;
  c.lfn=val;
  return c;
}
Cell env_cell(Env* val) {
  static if (debf) {debEnter("env_cell(Env*)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TEnv;
  c.env=val;
  return c;
  return c;
}
Cell type_cell(Type t) {
  static if (debf) {debEnter("type_cell(Type)");scope (exit) debLeave();}
  Cell c=Cell();
  c.type=TType;
  c.typ=t.cell;
  return c;
}
void as_null(Cell c) {
  assert(c.type==TNull,"as_null: Type error.");
}
string as_symbol(Cell c) {
  assert(c.type==TSymbol,"as_symbol: Type error.");
  return c.sym;
}
string as_str(Cell c) {
  assert(c.type==TString,"as_str: Type error.");
  return c.str;
}
Cell[] as_list(Cell c) {
  assert(c.type==TList,"as_list: Type error.");
  return c.lst;
}
float as_float(Cell c) {
  assert(c.type==TFloat,"as_float: Type error.");
  return c.flt;
}
int as_int(Cell c) {
  assert(c.type==TInt,"as_int: Type error.");
  return c.fix;
}
float as_number(Cell c) {
  if (c.type==TFloat) return c.flt;
  if (c.type==TInt) return c.fix;
  //writef("cell type = %i\n",c.type);
  assert(false,"as_number: Type error.");
}
Lamb* as_lambda(Cell c) {
  assert(c.type==TLambda,"as_lambda: Type error.");
  return c.lam;
}
fun_type as_func(Cell c) {
  assert(c.type==TFun,"as_function: Type error.");
  return c.fun;
}
lfn_type as_lfun(Cell c) {
  assert(c.type==TLfun,"as_lfun: Type error.");
  return c.lfn;
}
FTab* as_ftab(Cell c) {
  assert(c.type==TFtab,"as_ftab: Type error.");
  return c.ftab;
}
Assoc* as_assoc(Cell c) {
  assert(is_assoc_type(c.type),"as_assoc: Type error.");
  return c.asc;
}
Array* as_array(Cell c) {
  assert(is_array_type(c.type),"as_array: Type error.");
  return c.arr;
}
Struct* as_struct(Cell c) {
  assert(is_struct_type(c.type),"as_struct: Type error.");
  return c.stc;
}
Union* as_union(Cell c) {
  assert(is_union_type(c.type),"as_union: Type error.");
  return c.uni;
}
Ref* as_ref(Cell c) {
  assert(is_ref_type(c.type),"as_ref: Type error.");
  return c.ptr;
}
Env* as_env(Cell c) {
  assert(c.type==TEnv,"as_env: Type error.");
  return c.env;
}
TypeTable* as_typetable(Cell c) {
  assert(c.type==TTypeTable,"as_typetable: Type error.");
  return c.tyt;
}
Type as_type(Cell c) {
  assert(c.type==TType,"as_type: Type error.");
  return Type(c.typ);
}
Cell as_shell(Cell c) {
  assert(c.type==TShell,"as_shell: Type error.");
  return c.cel;
}
int istrue(Cell c) {
  if (c.type==TInt)    return c.fix;
  if (c.type==TFloat)  return c.flt!=0;
  if (c.type==TList)   return c.lst.length;
  if (c.type==TSymbol) return c.sym!="#f";
  if (c.type==TNull)   return false;
  return true;
}
bool isa(Cell c,Type t) {
  return (c.type==t);
}
bool is_sym(Cell c,string s) {
  return ((c.type==TSymbol)&&(c.sym==s));
}
void pr(Cell self) {
  writef("%s",str(self));
}
void prln(Cell self) {
  writef("%s\n",str(self));
}
Cell new_cell(string t) {
  static if (debf) {debEnter("new_cell(string)");scope (exit) debLeave();}
  return new_cell(type(t));
}
Cell new_cell(Type t) {
  static if (debf) {debEnter("new_cell(Type)");scope (exit) debLeave();}
  //writef("new called with parameter: %s\n",types.str(t));
  if (t==TAny) return any_cell();
//  if (t==TAny) return null_cell();
  if (t==TNull) return null_cell();
  if (t==TSymbol) return symbol_cell("");
  if (t==TNull) return null_cell();
  if (t==TString) return string_cell("");
  if (t==TInt) return int_cell(0);
  if (t==TFloat) return float_cell(0.0);
  if (t==TList) return list_cell([]);
  if (t==TType) return type_cell(TAny);
  //-- compound type
  if (is_compound_type(t)) {
    string constructor=get_compound_type_constructor(t);
    if (constructor=="array") return cell_from_array_type(t);
    if (constructor=="struct") return cell_from_struct_type(t);
    if (constructor=="union") return cell_from_union_type(t);
    if (constructor=="assoc") return cell_from_assoc_type(t);
    if (constructor=="ref") return cell_from_ref_type(t);
    if (constructor=="deftype") return cell_from_def_type(t);
    if (constructor=="aliastype") return cell_from_alias_type(t);
    assert(false,"unhandled compund type in new_cell");
  }
  writef("new_cell can't handle parameter %s\n",types.str(t));
  assert(false,"new_cell failed");
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- str
//--------------------
string str(Cell c,int clothedString=clothedStringDefault,int rec=1) {
  static if (debf) {debEnter("cells.str(Cell)");scope (exit) debLeave();}
//writefln("*** %s",types.str(c.type));
  c=c.clone();
  if (!types_initialised) {
    writef("Base types must be initialised before using cells.str!\n");
    assert(false);
  }
  if (c.type==TInt) {
    string s=frm("%d",c.fix);
    return s;
  }
  if (c.type==TFloat) {
    return frm("%g",cast(double)c.flt);
  }
  if (c.type==TList) {
    string s;
    s="(";
    for (int k;k<c.lst.length;++k) s~=str(c.lst[k],clothedString)~" ";
    if (c.lst.length) s.length=s.length-1;
    s~=")";
    return s;
  }
  if (is_array_type(c.type)) {
    string s;
    s="[";
    for (int k;k<c.arr.inner.length;++k) s~=str(c.arr.inner[k],clothedString)~" ";
    if (s.length>1) s.length=s.length-1;
    s~="]";
    return s;
  }
  if (c.type==TSymbol) {
    return c.sym;
  }
  if (c.type==TString) {
    if (clothedString) {
      return "'"~c.str~"'";
    } else {
      return c.str;
    }
  }
  if (c.type==TAny) return "any";
  if (c.type==TNull) return "null";
  if (is_struct_type(c.type)) {
    Struct struc=*as_struct(c);
    string s="{";
    for (int k;k<struc.key.length;++k) {
//      s~=types.str(struc.typ[k])~" ";
      string key=struc.key[k];
      Cell val=struc.val[k];
      s~=key~"="~str(val,1)~",";
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (is_union_type(c.type)) {
    Union uni=*as_union(c);
    string s="{";
    for (int k;k<uni.key.length;++k) {
//      s~=types.str(uni.typ[k])~" ";
      string key=uni.key[k];
      if (k==uni.tag) {
        s~=key~"="~str(uni.val,1)~",";
      } else {
        s~=key~",";
      }
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (is_assoc_type(c.type)) {
    string s="{";
    foreach (key;c.asc.inner.keys) {
      if (is_assoc_type(c.asc.inner[key].type)) {
        s~=key~":[TAssoc],";
      } else {
        s~=key~":"~str(c.asc.inner[key])~",";
      }
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (c.type==TFtab) return "[TFtab "~environments.str(as_ftab(c))~"]";
  if (c.type==TFun) return "[TFun]";
  if (c.type==TLfun) return "[TLfun]";
  if (c.type==TEnv) return str(assoc_cell(c.env.inner));
  if (c.type==TLambda) {
    if (clothedString||1) {
      string s="lambda(";
      foreach (p;c.lam.pars) s~=str(p)~" ";
      if (s[$-1]==' ') s.length=s.length-1;
      s~=")"~str(c.lam.expr,1);
      return s;
    } else {
      return "[TLambda]";
    }
  }
  if (c.type==TType) {
    Type t=as_type(c);
    return types.str(t);
  }
  //
  if (is_def_type(c.type)) {
    c=c.clone();
    c.type=get_def_subtype(c.type);
    return str(c);
  }
  return "["~types.str(c.type)~"]";
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- pretty_str
//--------------------
string pretty_str(Cell c,int ind) {
  int clothedString=1;
  int rec=1;
  if (!types_initialised) {
    writef("Base types must be initialised before using cells.str!\n");
    assert(false);
  }
  if (c.type==TInt) {
    return frm("%d",c.fix);
  }
  if (c.type==TFloat) {
    return frm("%g",cast(double)c.flt);
  }
  if (c.type==TList) {
    string s;
    if ((c.lst.length) && (is_sym(c.lst[0],"seq"))) {
      static if (0) {
        s~="\n"~spaces(ind+1);
        s~="(";
        for (int k=0;k<c.lst.length;++k) {
          s~=pretty_str(c.lst[k],ind+2);
          if (k+1<c.lst.length) s~="\n"~spaces(ind+2);
        }
        s~=")";
      } else {
        s~="\n"~spaces(ind+2);
        for (int k=1;k<c.lst.length;++k) {
          s~=pretty_str(c.lst[k],ind+2);
          if (k+1<c.lst.length) s~="\n"~spaces(ind+2);
        }
      }
    } else if ((c.lst.length) && (is_sym(c.lst[0],"switch"))) {
        s~="(";
        for (int k=0;k<c.lst.length;++k) {
          s~=pretty_str(c.lst[k],ind+2);
          if (k+1<c.lst.length) {
            if (k&1) {
              s~="\n"~spaces(ind+2);
            } else {
              s~=" ";
            }
          }
        }
        s~=")";
    } else {
      s="(";
      for (int k;k<c.lst.length;++k) s~=pretty_str(c.lst[k],ind)~" ";
      if (c.lst.length) s.length=s.length-1;
      s~=")";
    }
    return s;
  }
  if (is_array_type(c.type)) {
    string s;
    s="[";
    for (int k;k<c.arr.inner.length;++k) s~=pretty_str(c.arr.inner[k],ind)~" ";
    if (s.length>1) s.length=s.length-1;
    s~="]";
    return s;
  }
  if (c.type==TSymbol) {
    return c.sym;
  }
  if (c.type==TString) {
    if (clothedString) {
      return "'"~c.str~"'";
    } else {
      return c.str;
    }
  }
  if (c.type==TAny) return "any";
  if (c.type==TNull) return "null";
  if (is_struct_type(c.type)) {
    Struct struc=*as_struct(c);
    string s="{";
    for (int k;k<struc.key.length;++k) {
//      s~=types.str(struc.typ[k])~" ";
      string key=struc.key[k];
      Cell val=struc.val[k];
      s~=key~"="~pretty_str(val,ind)~",";
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (is_union_type(c.type)) {
    Union uni=*as_union(c);
    string s="{";
    for (int k;k<uni.key.length;++k) {
//      s~=types.str(uni.typ[k])~" ";
      string key=uni.key[k];
      if (k==uni.tag) {
        s~=key~"="~pretty_str(uni.val,ind)~",";
      } else {
        s~=key~",";
      }
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (is_assoc_type(c.type)) {
    string s="{";
    foreach (key;c.asc.inner.keys) {
      if (is_assoc_type(c.asc.inner[key].type)) {
        s~=key~":[TAssoc],";
      } else {
        s~=key~":"~pretty_str(c.asc.inner[key],ind)~",";
      }
    }
    if (s[$-1]==',') {
      s[$-1]='}';
    } else {
      s~="}";
    }
    return s;
  }
  if (c.type==TFtab) return "[TFtab "~environments.str(as_ftab(c))~"]";
  if (c.type==TFun) return "[TFun]";
  if (c.type==TLfun) return "[TLfun]";
  if (c.type==TEnv) return pretty_str(assoc_cell(c.env.inner),ind);
  if (c.type==TLambda) {
    if (clothedString||1) {
      string s="lambda(";
      foreach (p;c.lam.pars) s~=cells.str(p)~" ";
      if (s[$-1]==' ') s.length=s.length-1;
      s~=")"~cells.str(c.lam.expr,1);
      return s;
    } else {
      return "[TLambda]";
    }
  }
  if (c.type==TType) {
    Type t=as_type(c);
    return types.str(t);
  }
  //
  if (is_def_type(c.type)) {
    c.type=get_def_subtype(c.type);
    return cells.str(c);
  }
  return "["~types.str(c.type)~"]";
}
