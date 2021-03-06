module trafo;

import debg;
import cells;
import types;
import utils;
import signatures;
import environments;
import std.stdio;

const bool debf=debflag && 0;

bool operator_in_tree(Cell c,string op) {
  if (!isa(c,TList)) return false;
  Cell[] cl=c.lst;
  if (!cl.length) return false;
  if (isa(cl[0],TList)) {
    if (operator_in_tree(cl[0],op)) return true;
  }
  if (isa(cl[0],TSymbol)) {
    if (cl[0].sym==op) return true;
  }
  for (int k=1;k<cl.length;++k) {
    if (operator_in_tree(cl[k],op)) return true;
  }
  return false;
}
bool is_list_with_operator(Cell c,string op="") {
  if (!isa(c,TList)) return false;
  if (!c.lst.length) return false;
  if (!isa(c.lst[0],TSymbol)) return false;
  if (!op.length) return true;
  return c.lst[0].sym==op;
}
void operator_to_front(Cell c,string op) {
  if (!isa(c,TList)) return;
  if (is_list_with_operator(c,"seq")) {
    Cell[] match,nomatch;
    for (int k=1;k<c.lst.length;++k) {
      if (is_list_with_operator(c.lst[k],op)) {
        match~=c.lst[k];
      } else {
        nomatch~=c.lst[k];
      }
    }
    c.lst.length=1;
    c.lst~=match~nomatch;
  }
  for (int k=0;k<c.lst.length;++k) {
    operator_to_front(c.lst[k],op);
  }
}
void operators_to_front(Cell c,string[] ops) {
  bool[string] ops_hash;
  foreach (op;ops) ops_hash[op]=true;
  operators_to_front(c,ops_hash);
}
void operators_to_front(Cell c,bool[string] ops) {
  if (!isa(c,TList)) return;
  if (is_list_with_operator(c,"seq")) {
    Cell[] match,nomatch;
    for (int k=1;k<c.lst.length;++k) {
      if (is_list_with_operator(c.lst[k]) && (c.lst[k].lst[0].sym in ops)) {
        match~=c.lst[k];
      } else {
        nomatch~=c.lst[k];
      }
    }
    c.lst.length=1;
    c.lst~=match~nomatch;
  }
  for (int k=0;k<c.lst.length;++k) {
    operators_to_front(c.lst[k],ops);
  }
}
void reduce_seq_of_one(Cell c) {
  if (!isa(c,TList)) return;
  for (int k=0;k<c.lst.length;++k) {
    reduce_seq_of_one(c.lst[k]);
  }
  if (is_list_with_operator(c,"seq") && (c.lst.length==2) && (isa(c.lst[1],TList))) {
    c.lst=c.lst[1].lst;
  }
}
Cell[] cells_with_operator(Cell c,string op) {
  static if (debf) {debEnter("cells_with_operator(...)");scope (exit) debLeave();}
  Cell[] res;
  if (!isa(c,TList)) return res;
  Cell[] cl=c.lst;
  if (!cl.length) return res;
  if (isa(cl[0],TSymbol) && (cl[0].sym==op)) res~=c;
  for (int k=0;k<cl.length;++k) res~=cells_with_operator(cl[k],op);
  return res;
}
Cell first_with_operator(Cell c,string op) {
  static if (debf) {debEnter("first_with_operator(...)");scope (exit) debLeave();}
  if (!isa(c,TList)) return null;
  Cell[] cl=c.lst;
  if (!cl.length) return null;
  if (isa(cl[0],TSymbol) && (cl[0].sym==op)) return c;
  for (int k=0;k<cl.length;++k) {
    Cell res=first_with_operator(cl[k],op);
    if (res) return res;
  }
  return null;
}
Cell deftype_cell(string name,Cell def) {
  return list_cell([symbol_cell("deftype"),symbol_cell(name),def.clone()]);
}
Cell anontype_cell(string name,Cell def) {
  return list_cell([symbol_cell("anontype"),symbol_cell(name),def.clone()]);
}
Cell aliastype_cell(string name,Cell def) {
  return list_cell([symbol_cell("aliastype"),symbol_cell(name),def.clone()]);
}
void replace_alias_types(Cell root) {
  static if (debf) {debEnter("find_anonymous_structs_and_unions(...)");scope (exit) debLeave();}
  root=first_with_operator(root,"seq");
  if (!root) return;
  Cell[string] aliases;
  Cell[] list=root.lst;
  //writef("%s\n",cells.pretty_str(root));
  //assert(false,"ok");
  foreach (cell;list) {
    replace_alias_types(cell);
  }
  foreach (cell;list) {
    if (is_list_with_operator(cell,"aliastype")) {
      if (!isa(cell.lst[1],TSymbol)) {
        writef("%s\n",cells.pretty_str(cell));
      }
      aliases[as_symbol(cell.lst[1])]=cell.lst[2];
      cell.lst.length=0;
    }
  }
  foreach (key;aliases.keys) {
    replace_symbol(root,key,aliases[key]);
  }
}
// enforce root typedefs in laguage spec!
void move_typedefs_to_root(Cell root) {
  static if (debf) {debEnter("find_anonymous_structs(...)");scope (exit) debLeave();}
  root=first_with_operator(root,"seq");
  if (!root) return;
  Cell[] defs=cells_with_operator(root,"deftype")~cells_with_operator(root,"supertype");
  Cell[] rdefs;
  foreach (ref def;defs) {
    rdefs~=def.clone();
    def.lst.length=0;
  }
  root.lst=root.lst[0]~rdefs~root.lst[1..$];
}
void replace_symbol(Cell c,string id,Cell r) {
  if (isa(c,TList)) {
    foreach (e;c.lst) replace_symbol(e,id,r);
  } else {
    if (isa(c,TSymbol)) {
      if (c.sym==id) c.set(r);
    }
  }
}
FTabEntry* specialise_dotget(FTabEntry* org_fte,string fieldname) {
  FTabEntry fte;
  //-- create specialised signature and retain index name
  Signature org_sig=org_fte.sig;
  Signature sig;
  string indexname;
  sig.open=org_sig.open;
  for (int k;k<org_sig.length;++k) {
    if (k==1) {
      indexname=org_sig.ses[k].name;
    } else {
      sig.ses~=org_sig.ses[k];
    }
  }
  //--
  Lamb* lam=clone(as_lambda(org_fte.fun));
  remove_element(lam.pars,1);
  replace_symbol(lam.expr,indexname,string_cell(fieldname));
  // todo: currently replacing ALL symbols of matching id, without further checking
  Cell fun=lambda_cell(lam);
  //--
  fte.sig=sig;
  fte.ret=TAny;//org_fte.ret;
  fte.fun=fun;
  return [fte].ptr;
}
FTabEntry* specialise_dotset(FTabEntry* org_fte,string fieldname) {
  FTabEntry fte;
  //-- create specialised signature and retain index name
  Signature org_sig=org_fte.sig;
  Signature sig;
  string indexname;
  sig.open=org_sig.open;
  for (int k;k<org_sig.length;++k) {
    if (k==1) {
      indexname=org_sig.ses[k].name;
    } else {
      sig.ses~=org_sig.ses[k];
    }
  }
  //sig.ses[0].type=ref_type_from_subtype(sig.ses[0].type);
  //--
  Lamb* lam=clone(as_lambda(org_fte.fun));
  remove_element(lam.pars,1);
  assert(isa(lam.pars[0],TList));
  //lam.pars[0].lst[0]=list_cell([symbol_cell("ref")]~lam.pars[0].lst[0]);
  replace_symbol(lam.expr,indexname,string_cell(fieldname));
  string objname=org_sig.ses[0].name;
  //replace_symbol(lam.expr,objname,list_cell([symbol_cell("@")]~symbol_cell(objname)));
  // todo: currently replacing ALL symbols of matching id, without further checking
  Cell fun=lambda_cell(lam);
  //--
  fte.sig=sig;
  fte.ret=TAny;//org_fte.ret;
  fte.fun=fun;
  return [fte].ptr;
}
