module parser;

import debg;
import lexer;
import types;
import cells;
import signatures;
import environments;
import utils;
import std.string;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- parser
//----------------

Cell atom(Lexem token) {
  static if (debf) {debEnter("atom");scope (exit) debLeave();}
//  printf("%.*s ",token.val);
  if (token.tag==LTAG.OP ) return sym_cell(token.val);
  if (token.tag==LTAG.SYM) return sym_cell(token.val);
  if (token.tag==LTAG.STR) return str_cell(token.val[1..$-1]);
  if (token.tag==LTAG.INT) return int_cell(cast(int)(atof(token.val)));
  if (token.tag==LTAG.FLT) return float_cell(atof(token.val));
  printf("*** [%.*s] ***\n",token.val);
  assert(false);
}
Cell parse(Lexem[] tokens,ref int pos) {
  static if (debf) {debEnter("read_from(Lexem[],int)");scope (exit) debLeave();}
  assert(tokens.length>pos,"unexpected EOF while reading");
  Lexem token=tokens[pos++];
  if (token.val=="(") {
    Cell c;
    c.type=TList;
    c.lst=[];
    while (tokens[pos].val!=")") c.lst~=parse(tokens,pos);
    ++pos; // pop off ')'
    return c;
  }
  if (token.val==")") assert(false,"unexpected )");
  return atom(token);
}
Cell parse(Lexem[] tokens) {
  int pos=0;
  return parse(tokens,pos);
}
Cell parse(string text) {
  int pos=0;
  return parse(lex(text),pos);
}
