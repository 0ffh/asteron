module eval_helpers;

import debg;
import cells;
import types;
import utils;
import signatures;
import environments;
import std.file;
import std.stdio;
import std.string;
import std.format;

const bool debf=debflag && 01;

FTabEntry* resolve_name_as_ftab_entry(string name,ref Cell[] args,ref Env* e) {
  static if (debf) {debEnter("resolve_name_as_ftab_entry('%s')",name);scope (exit) debLeave();}
  FTabEntry* candidate_entry;
  Cell candidate;
  e=environment;
  for (;;) {
    //writef("looking up Function '%s' in environment %s\n",name,e);
    if (e) e=env_find(e,name);
    if (!e) {
//      writef("*** Error: Function '%s' lookup failed!\n",name);
      return null;
    }
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) continue;
    candidate_entry=ftab_resolve(candidate.ftab,args,name);
    if (candidate_entry) break;
    e=e.outer;
  }
//  writef("******* candidate_entry %s\n",candidate_entry.fun);
  return candidate_entry;
}
FTabEntry* resolve_name_as_ftab_entry(string name,ref Cell[] args) {
  Env* e;
  return resolve_name_as_ftab_entry(name,args,e);
}
Cell resolve_symbol_except_ftabs(Cell sym) {
  static if (debf) {debEnter("resolve_symbol_except_ftabs");scope (exit) debLeave();}
  Cell candidate;
  string name=as_symbol(sym);
  Env* e=environment;
  while (e) {
    e=env_find(e,name);
    if (!e) break;
    candidate=env_get(e,name);
    if (!isa(candidate,TFtab)) return candidate;
    e=e.outer;
  }
  return null_cell();
}
