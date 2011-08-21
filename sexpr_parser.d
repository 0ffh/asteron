module sexpr_parser;

import debg;
import cells;
import types;
import environments;
import utils;
import lexer;
import std.conv;
import std.stdio;
import std.string;

const bool debf=debflag && 0;

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
Cell atom(Lexeme token) {
  static if (debf) {debEnter("atom");scope (exit) debLeave();}
  if (token.type=="operator") return symbol_cell(token.val);
  if (token.type=="name") return symbol_cell(token.val);
  if (token.type=="string") return string_cell(token.val);
  if (token.type=="number") {
    try {
      return int_cell(toInt(token.val));
    } catch {
      return float_cell(toFloat(token.val));
    }
  }
  writef("*** [%s] ***\n",token.val);
  assert(false);
}
Cell parse_sexpr(Lexeme[] tokens,ref int pos) {
  static if (debf) {debEnter("read_from(Lexeme[],int)");scope (exit) debLeave();}
  assert(tokens.length>pos,"unexpected EOF while reading");
  if (!pos) tokens=rm_whitespaces(tokens);
  Lexeme token=tokens[pos++];
  if (token.val=="(") {
    Cell c=list_cell([]);
    while (tokens[pos].val!=")") c.lst~=parse_sexpr(tokens,pos);
    ++pos; // pop off ')'
    return c;
  }
  if (token.val==")") assert(false,"unexpected )");
  return atom(token);
}
Cell parse_sexpr(Lexeme[] tokens) {
  if (!types_initialised) {
    writef("Base types must be initialised before parsing!\n");
    assert(false);
  }
  int pos=0;
  return parse_sexpr(rm_whitespaces(tokens),pos);
}
Cell parse_sexpr(string text) {
  return parse_sexpr(llex(text));
}
Cell parse_sexpr_file(string filename) {
  return parse_sexpr(cast(string)std.file.read(filename));
}
