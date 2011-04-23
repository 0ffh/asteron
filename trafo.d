module trafo;

import debg;
import cells;
import types;
import utils;

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

