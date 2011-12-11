
//--  (w) Frank F. Hirsch (2011)

// todo: more than you can shake a stick at

module main;

import debg;
import lexer;
import cells;
import types;
import trafo;
import utils;
import llparse;
import hlparse;
import environments;
import std.file;
import std.stdio;
import std.string;
import std.format;

const bool debf=debflag && 01;

const bool require_declaration_before_use=true;

Env* base_env;

Env* mk_base_env() {
  Env* e=mk_env();
  push_env(e);
  init_hlparse();
  init_types();
  return e;
}
void ast2l(string base_filename) {
  bool showflag=!true;
  bool reorder=true;
  base_env=mk_base_env();
  Cell c=parse_file_to_cell(base_filename~".ast");
  reduce_seq_of_one(c);
  if (reorder) {
    operators_to_front(c,["defun","def"]);
    operator_to_front(c,"supertype");
    operator_to_front(c,"aliastype");
    operator_to_front(c,"deftype");
    if (showflag) writef("%s\n",pretty_str(c,0));
  }
  writef("%s\n",pretty_str(c,0));
  std.file.write(base_filename~".l",cast(void[])bondage_str(c,0)~"\n");
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- main
//----------------

void main(string[] args) {
  string base_filename;
  if (args.length>1) base_filename=args[1];
  else base_filename="test";
  ast2l(base_filename);
}
