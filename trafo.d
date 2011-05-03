module trafo;

import debg;
import cells;
import types;
import utils;
import std.stdio;

const bool debf=debflag;

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
void find_anonymous_structs(Cell root) {
  static if (debf) {debEnter("find_anonymous_structs(...)");scope (exit) debLeave();}
  root=first_with_operator(root,"seq");
  //root=root.lst[1];
  //writef("%s\n",cells.str(root));
  Cell[] cs=cells_with_operator(root,"def");
  int anon_count;
  string anon_name;
  foreach (c;cs) {
    Cell[] anon=cells_with_operator(c,"struct");
    if (anon.length) {
      writef("def with anonymous struct: %s\n",cells.str(c));
      anon_name=frm("anon_type_%d",anon_count++);
//      root.lst=[root.lst[0],anontype_cell(anon_name,anon[0])]~root.lst[1..$];
      root.lst=[root.lst[0],aliastype_cell(anon_name,anon[0])]~root.lst[1..$];
      anon[0].set(symbol_cell(anon_name));
      writef("  -->  %s\n",cells.str(c));
    }
  }
}
/*void insert_outer_seq_in_defuns(Cell root) {
  static if (debf) {debEnter("insert_outer_seq_in_lambdas(...)");scope (exit) debLeave();}
  root=first_with_operator(root,"seq");
  //root=root.lst[1];
  //writef("%s\n",cells.str(root));
  Cell[] cs=cells_with_operator(root,"defun");
  foreach (c;cs) {
    assert(isa(c,TList));
    assert(c.lst.length==4);
    Cell d=c.lst[3];
    if (!(is_list_with_operator(d,"seq"))) {
      d=list_cell([symbol_cell("seq"),d]);
    }
    //writefln("lambda %s\n",cells.str(d));
  }
}*/

