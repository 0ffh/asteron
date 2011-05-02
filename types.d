module types;

import debg;
import utils;
import cells;
import llparse;
import environments;
import std.stdio;

const bool debf=debflag;

bool types_initialised=false;

Type TSymbol;
Type TType;
Type TAny;
Type TShell;
Type TNull;
Type TString;
Type TInt;
Type TFloat;
Type TList;
Type TEnv;
Type TFtab;
Type TFun;
Type TLfun;
Type TLambda;
Type TTypeTable;

const string id_sym="symbol";
const string id_type="type";
const string id_any="any";
const string id_shell="shell";
const string id_null="null";
const string id_str="string";
const string id_int="int";
const string id_flt="float";
const string id_list="list";
const string id_env="env";
const string id_funtab="funtab";
const string id_fun="function";
const string id_lfun="lfun";
const string id_lambda="lambda";
const string id_typetable="typetable";
const string[] type_ids=[
  id_sym,id_type,id_any,id_shell,id_null,id_str,id_int,id_flt,id_env,
  id_list,id_funtab,id_fun,id_lfun,id_lambda,id_typetable
];

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Type
//----------------

// all types are interned so type pointers can be compared

struct Type {
  Cell cell;
  void show() {
    writef("%s\n",types.str(*this));
  }
}
void prln(Type t) {
  cells.prln(t.cell);
}
Type prim_type(string typestring) {
  static if (debf) {debEnter("prim_type(string '"~typestring~"')");scope (exit) debLeave();}
  TypeTable* tyt=as_typetable(env_get(environment,"type_table"));
  if (typestring in tyt.str2typ) return tyt.str2typ[typestring];
  Type t;
  t.cell=symbol_cell(typestring);
  tyt.str2typ[typestring]=t;
  tyt.typ2str[t]=typestring;
  return t;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- compound types
//--------------------
bool is_basic_type(Type t) {
  return !is_compound_type(t);
}
bool is_compound_type(Type t) {
  return isa(t.cell,TList);
}
string get_compound_type_constructor(Type t) {
  if (t.cell.type!=TList) return "";
  if (!t.cell.lst.length) return "";
  return as_symbol(t.cell.lst[0]);
}
Cell[] get_compound_fields(Type t,string ctr) {
  assert(t.cell.type==TList);
  if (t.cell.lst.length<2) return [];
  assert(isa(t.cell.lst[0],TSymbol));
  assert(t.cell.lst[0].sym==ctr);
  return t.cell.lst[1..$];
}
Cell[] get_compound_fields(Type t) {
  assert(t.cell.type==TList);
  if (t.cell.lst.length<2) return [];
  assert(isa(t.cell.lst[0],TSymbol));
  return t.cell.lst[1..$];
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- add type to type table
void add_type_to_table(string name,Type type) {
  TypeTable* tyt=as_typetable(env_get(environment,"type_table"));
  if (name in tyt.str2typ) assert(false,"type "~name~" is already defined");
  type.cell.ann["name"]=symbol_cell(name);
  tyt.str2typ[name]=type;
  tyt.typ2str[type]=name;
}
//--------------------
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- deftype
//--------------------
bool is_def_type(Type t) {
  return (get_compound_type_constructor(t)=="deftype");
}
Type get_def_subtype(Type t) {
//   writef("%s\n",str(t));
  assert(is_def_type(t));
  assert(t.cell.lst.length>1);
  return type(t.cell.lst[1]);
}
Type def_type_from_subtype(Type subtyp) {
  static if (debf) {debEnter("def_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(deftype "~str(subtyp)~")");
}
Type type_deftype(string name,Type t) {
  static if (debf) {debEnter("type_deftype(string,Cell)");scope (exit) debLeave();}
  //writef("*** defining type '%s'\n",name);
  //writef("*** typestring = %s\n",str(t));
  t=def_type_from_subtype(t);
  add_type_to_table(name,t);
  return t;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- aliastype
//--------------------
bool is_alias_type(Type t) {
  return (get_compound_type_constructor(t)=="aliastype");
}
Type get_alias_subtype(Type t) {
  assert(is_alias_type(t));
  assert(t.cell.lst.length>1);
  return type(t.cell.lst[1]);
}
Type alias_type_from_subtype(Type subtyp) {
  static if (debf) {debEnter("alias_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(aliastype "~str(subtyp)~")");
}
Type type_aliastype(string name,Type t) {
  static if (debf) {debEnter("type_aliastype(string,Cell)");scope (exit) debLeave();}
  //writef("*** defining type '%s'\n",name);
  //writef("*** typestring = %s\n",str(t));
  t=alias_type_from_subtype(t);
  add_type_to_table(name,t);
  return t;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- super type
//--------------------
bool is_super_type(Type t) {
  return (get_compound_type_constructor(t)=="supertype");
}
Type[] get_super_subtypes(Type t) {
  static if (debf) {debEnter("get_super_subtypes(Type)");scope (exit) debLeave();}
  assert(is_super_type(t));
  assert(t.cell.lst.length>1);
  Type[] st;
  for (int k=1;k<t.cell.lst.length;++k) st~=type(t.cell.lst[k]);
  return st;
}
Type super_type_from_subtypes(Type[] subtypes) {
  static if (debf) {debEnter("super_type_from_subtype(Type[])");scope (exit) debLeave();}
  string ts="(supertype";
  for (int k;k<subtypes.length;++k) ts~=" "~str(subtypes[k]);
  ts~=")";
  return type(ts);
}
void super_type_extend_to_subtypes(Type t,Type[] subtypes) {
  static if (debf) {debEnter("super_type_extend_to_subtypes(Type[])");scope (exit) debLeave();}
  assert(is_super_type(t));
  for (int k=0;k<subtypes.length;++k) t.cell.lst~=type_cell(subtypes[k]);
}
Type type_supertype(string name,Type[] st) {
  static if (debf) {debEnter("type_supertype(string,Cell)");scope (exit) debLeave();}
  //writef("*** defining type '%s'\n",name);
  //writef("*** typestring = %s\n",str(t));
  TypeTable* tyt=as_typetable(env_get(environment,"type_table"));
  Type t;
  if (name in tyt.str2typ) {
    t=tyt.str2typ[name];
    assert(is_super_type(t),"type "~name~" is already defined");
    super_type_extend_to_subtypes(t,st);
    return t;
  }
  t=super_type_from_subtypes(st);
  static if (0) {
    writef("supertype %s",name);
    foreach (ste;st) writef(" %s",str(ste));
    writef("\n");
  }
  tyt.str2typ[name]=t;
  tyt.typ2str[t]=name;
  return t;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- assoc type
//--------------------
bool is_assoc_type(Type t) {
  return (get_compound_type_constructor(t)=="assoc");
}
Type get_assoc_domain(Type t) {
  assert(t.cell.type==TList);
  assert(t.cell.lst.length==3);
  assert(isa(t.cell.lst[0],TSymbol));
  assert(t.cell.lst[0].sym=="assoc");
  return type(t.cell.lst[1]);
}
Type get_assoc_codomain(Type t) {
  assert(t.cell.type==TList);
  assert(t.cell.lst.length==3);
  assert(isa(t.cell.lst[0],TSymbol));
  assert(t.cell.lst[0].sym=="assoc");
  return type(t.cell.lst[2]);
}
Type assoc_type_from_subtype(Type subtyp) {
  static if (debf) {debEnter("assoc_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(assoc "~str(subtyp)~")");
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- array type
//--------------------
bool is_array_type(Type t) {
  return (get_compound_type_constructor(t)=="array");
}
bool is_static_array_type(Type t) {
  return (is_array_type(t) && (get_compound_fields(t).length==2));
}
bool is_dynamic_array_type(Type t) {
  return (is_array_type(t) && (get_compound_fields(t).length==1));
}
int get_static_array_length(Type t) {
  assert(is_static_array_type(t));
  /*Cell c=get_compound_fields(t)[1];
  cells.prln(c);
  types.prln(c.type);*/
  return as_int(get_compound_fields(t)[1]);
}
Type get_array_subtype(Type t) {
  assert(is_array_type(t));
  assert(t.cell.lst.length>1);
  return type(t.cell.lst[1]);
}
Type array_type_from_subtype(Type subtyp) {
  static if (debf) {debEnter("array_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(array "~str(subtyp)~")");
}
Type array_type_from_subtype_and_length(Type subtyp,int len) {
  static if (debf) {debEnter("array_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(array "~str(subtyp)~" "~utils.str(len)~")");
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- struct type
//--------------------
bool is_struct_type(Type t) {
  return (get_compound_type_constructor(t)=="struct");
}
Type struct_type_from_fields(Cell[] fields) {
  static if (debf) {debEnter("struct_type_from_fields(Cell[])");scope (exit) debLeave();}
  return type(cells.str(list_cell(symbol_cell("struct")~fields)));
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- union type
//--------------------
bool is_union_type(Type t) {
  return (get_compound_type_constructor(t)=="union");
}
Type union_type_from_fields(Cell[] fields) {
  static if (debf) {debEnter("union_type_from_fields(Cell[])");scope (exit) debLeave();}
  return type(cells.str(list_cell(symbol_cell("union")~fields)));
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- reference type
//--------------------
bool is_ref_type(Type t) {
  return (get_compound_type_constructor(t)=="ref");
}
Type get_ref_subtype(Type t) {
  assert(is_ref_type(t));
  assert(t.cell.lst.length>1);
  return type(t.cell.lst[1]);
}
Type ref_type_from_subtype(Type subtyp) {
  static if (debf) {debEnter("ref_type_from_subtype(Type)");scope (exit) debLeave();}
  return type("(ref "~str(subtyp)~")");
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//--------------------
//--------------------
Type type(string typestring) {
  static if (debf) {debEnter("type(string '"~typestring~"')");scope (exit) debLeave();}
  return type(lparse(typestring));
}
Type type(Cell val) {
  static if (debf) {debEnter("type(Cell)");scope (exit) debLeave();}
  //val=val.clone();
  string typestring=cells.str(val);
  TypeTable* tyt=as_typetable(env_get(environment,"type_table"));
  if (typestring in tyt.str2typ) return tyt.str2typ[typestring];
  Type t;
  t.cell=val;
  tyt.str2typ[typestring]=t;
  tyt.typ2str[t]=typestring;
  return t;
}
Type type_of(Cell c) {
  return c.type;
}
string str(Type t) {
  TypeTable* tyt=as_typetable(env_get(environment,"type_table"));
  string* ps=(t in tyt.typ2str);
  if (ps) return *ps;
//   assert(false); // temporary test
  return cells.str(t.cell);
}
string str(Type[] ts) {
  if (!ts.length) return "()";
  string s="(";
  for (int k;k<ts.length;++k) s~=str(ts[k])~" ";
  s[$-1]=')';
  return s;
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- initialisation
//--------------------
TypeTable* mk_typetable() {
  TypeTable tyt;
  return cast(TypeTable*)([tyt].ptr);
}
void init_types() {
  static if (debf) {debEnter("init_types");scope (exit) debLeave();}
  TypeTable* tyt=mk_typetable();
  // make TSymbol and TType
  TSymbol.cell=Cell();
  TType.cell=Cell();
  TSymbol.cell.type=TType;
  TType.cell.type=TType;
  tyt.str2typ[id_sym]=TSymbol;
  tyt.str2typ[id_type]=TType;
  tyt.typ2str[TSymbol]=id_sym;
  tyt.typ2str[TType]=id_type;
  TSymbol.cell.typ=symbol_cell(id_sym);
  TType.cell.typ=symbol_cell(id_type);
  //
  TTypeTable.cell=Cell();
  TTypeTable.cell.type=TType;
  tyt.str2typ[id_typetable]=TTypeTable;
  tyt.typ2str[TTypeTable]=id_typetable;
  TType.cell.typ=symbol_cell(id_typetable);
  //
  env_put(environment,"type_table",typetable_cell(tyt));
  // make other prim_types
  TAny=prim_type(id_any);
  TShell=prim_type(id_shell);
  TNull=prim_type(id_null);
  TString=prim_type(id_str);
  TInt=prim_type(id_int);
  TFloat=prim_type(id_flt);
  TList=prim_type(id_list);
  TEnv=prim_type(id_env);
  TFtab=prim_type(id_funtab);
  TFun=prim_type(id_fun);
  TLfun=prim_type(id_lfun);
  TLambda=prim_type(id_lambda);
  //
  types_initialised=true;
  // test type interning
  assert(TType==type(id_type),"Type interning failure");
  assert(TSymbol==type(id_sym),"Type interning failure");
  assert(TAny==type(id_any),"Type interning failure");
  assert(TNull==type(id_null),"Type interning failure");
  assert(TShell==type(id_shell),"Type interning failure");
  assert(TString==type(id_str),"Type interning failure");
  assert(TInt==type(id_int),"Type interning failure");
  assert(TFloat==type(id_flt),"Type interning failure");
  assert(TList==type(id_list),"Type interning failure");
  assert(TEnv==type(id_env),"Type interning failure");
  assert(TFtab==type(id_funtab),"Type interning failure");
  assert(TFun==type(id_fun),"Type interning failure");
  assert(TLfun==type(id_lfun),"Type interning failure");
  assert(TLambda==type(id_lambda),"Type interning failure");
  assert(TTypeTable==type(id_typetable),"Type interning failure");
  //
  foreach (tid;type_ids) env_put(environment,tid,type_cell(type(tid)));
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//--------------------
//-------------------- anonymous types
//--------------------
string[string] type_names;
void add_type_name(Type typ,string name) {
  writef("*** add_type_name %s %s\n",types.str(typ),name);
  type_names[str(typ)]=name;
}
string get_type_name(Type typ) {
  string name;
  string *pname=str(typ) in type_names;
  if (pname is null) name=""; else name=*pname;
  writef("*** get_type_name %s %s\n",types.str(typ),name);
  return name;
}
