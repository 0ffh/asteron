module signatures;

import debg;
import utils;
import cells;
import types;
import sexpr_parser;
import environments;
import std.stdio;

const bool debf=debflag && 0;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Signature
//----------------

struct SigElement {
  string name; // parameter names
  Type   type; // parameter types
  Cell   defv; // parameter default values
}
struct Signature {
  SigElement[] ses;
  Type         open;
  Signature clone() {
    Signature n;
    n.ses.length=ses.length;
    for (int k;k<ses.length;++k) {
      n.ses[k]=ses[k];
    }
    n.open=open;
    return n;
  }
  int length() {
    return ses.length;
  }
  SigElement opIndex(int idx) {
    assert(ses.length>idx,"Index out of bounds");
    return ses[idx];
  }
  SigElement[] opCatAssign(SigElement se) {
    return ses~=se;
  }
  bool is_open() {
    return (open.cell !is null);
  }
  string toString() {
    return signatures.str(*this);
  }
  bool opEquals(Signature sig) {
    if (ses.length!=sig.ses.length) return false;
    for (int k;k<ses.length;++k) if (ses[k].type!=sig.ses[k].type) return false;
    return true;
  }
}
string str(Signature sig) {
  string s="(";
  for (int k;k<sig.length;++k) {
    s~=types.str(sig[k].type)~" ";
    if (sig[k].defv.type!=TNull) s~="[="~cells.str(sig[k].defv)~"] ";
  }
  if (sig.open.cell) {
    s~="(open "~types.str(sig.open)~")";
  } else {
    if (sig.length) s.length=s.length-1;
  }
  return s~")";
}
/*Signature argument_string2signature(string argstr) {
  static if (debf) {debEnter("argument_string2signature(string)");scope (exit) debLeave();}
  return parameter_cell2signature(parse_sexpr(argstr));
}*/
Signature signature_string2signature(string sigstr) {
  static if (debf) {debEnter("signature_string2signature(string)");scope (exit) debLeave();}
//  writef("x ");
  return signature_cell2signature(parse_sexpr(sigstr));
}
Signature parameter_cell2signature(Cell arg) {
  static if (debf) {debEnter("parameter_cell2signature(Cell)");scope (exit) debLeave();}
  if (!isa(arg,TList)) assert(false);
  Signature sig;
  for (int k;k<arg.lst.length;++k) {
    Cell[] lst;
    // for each entry lst is either of
    //   [name]
    //   [type name]
    //   [type name default]
    if (isa(arg.lst[k],TSymbol)) {
      lst=[arg.lst[k]];
    } else {
      if (!isa(arg.lst[k],TList)) assert(false);
      lst=arg.lst[k].lst;
    }
    if (!lst.length) assert(false);
    SigElement se;
    if (lst.length==3) {
      // type name default
      se.defv=lst[2];
      se.name=as_symbol(lst[1]);
      se.type=type(lst[0]);
    } else if (lst.length==2) {
      // type name
      se.defv=null_cell();
      se.name=as_symbol(lst[1]);
      se.type=type(lst[0]);
    } else if (lst.length==1) {
      // name
      se.defv=null_cell();
      se.name=as_symbol(lst[0]);
      se.type=TAny;
    } else {
      assert(false);
    }
    if (se.name=="...") {
      // open
      sig.open=se.type;
      break;
    } else {
      sig~=se;
    }
  }
//  writef("pc2s %s -> %s\n",cells.str(arg),str(sig));
  return sig;
}
Signature signature_cell2signature(Cell arg) {
  static if (debf) {debEnter("signature_cell2signature(Cell)");scope (exit) debLeave();}
  const int verbose=false;
  if (!isa(arg,TList)) assert(false);
  Signature sig;
  static if (verbose) writef("signature_cell2signature");
  for (int k;k<arg.lst.length;++k) {
    // options for each entry:
    //   type
    SigElement se;
    se.name=""; // there's never a parameter name
    Cell a=arg.lst[k];
    if (isa(a,TSymbol)) {
      if (a.sym=="=") {
        a=arg.lst[++k];
        sig[sig.length-1].defv=a;
        continue;
      }
      if (a.sym=="...") {
        sig.open=TAny;
        break;
      }
    }
    if (isa(a,TList)) {
      Cell[] al=a.lst;
      if ((al.length) && (isa(al[0],TSymbol)) && (al[0].sym=="...")) {
        if ((al.length>1)) {
          sig.open=type(al[1]);
        } else {
          sig.open=TAny;
        }
        break;
      }
    }
    //static if (verbose) writef(" %s",cells.str(a));
    se.type=type(a);
    static if (verbose) writef(" %s",types.str(se.type));
    se.defv=null_cell();
    sig~=se;
  }
  static if (verbose) writef("\n");
//  writef("sc2s %s -> %s\n",cells.str(arg),str(sig));
  return sig;
}
Signature types2signature(Type[] args,Type* open=null) {
  static if (debf) {debEnter("types2signature(Cell)");scope (exit) debLeave();}
  const int verbose=false;
  Signature sig;
  static if (verbose) writef("types2signature");
  for (int k;k<args.length;++k) {
    SigElement se;
    se.name=""; // there's never a parameter name
    static if (verbose) writef(" %s",types.str(args[k]));
    se.type=args[k];
    se.defv=null_cell();
    sig~=se;
  }
  if (open) sig.open=*open;
  static if (verbose) writef("\n");
  return sig;
}
int signature_matches(Signature sig,Type[] targ) {
  static if (debf) {debEnter("signature_matches(Signature,Type[])");scope (exit) debLeave();}
  const int verbose=!true;
  int p=exact_score;
  if ((targ.length>sig.length) && (!sig.is_open())) return fail_score;
  static if (verbose) writef("-- sig= %s\n",str(sig));
  static if (verbose) writef("-- arg= %s\n",str(types2signature(targ)));
  Type tp=TNull,ta=TNull;
  int k=0;
  for (;k<targ.length;++k) {
    if (k>=sig.length) break;
    tp=sig[k].type;
    ta=targ[k];
    static if (verbose) writef("-- %d : par= %s   arg= %s\n",k,types.str(tp),types.str(ta));
    int m=type_matches(tp,ta);
    if (m) {
      p=(p<<score_shift)+m;
      continue;
    }
    static if (verbose) writef("fail\n");
    return fail_score;
  }
  if (sig.is_open()) {
    tp=sig.open;
    for (;k<targ.length;++k) {
      ta=targ[k];
      static if (verbose) writef("-- %d : par= %s   arg= %s\n",k,types.str(tp),types.str(ta));
      int m=type_matches(tp,ta);
      if (m) {
        p=(p<<score_shift)+m;
        continue;
      }
      static if (verbose) writef("fail\n");
      return fail_score;
    }
    return p-1;
  }
  for (;k<sig.length;++k) {
//    writef("default %s\n",cells.str(sig[k].defv));
//    if (sig.is_open()) return p-1; // empty ellipse
    if (sig[k].defv.type==TNull) return fail_score;
  }
  return p;
}
bool signature_matches_perfectly(Signature sig,Type[] targ) {
  static if (debf) {debEnter("signature_matches_perfectly(Signature,Type[])");scope (exit) debLeave();}
  const int verbose=!true;
  if ((targ.length>sig.length) && (!sig.is_open())) return false;
  static if (verbose) writefln("----- signature_matches_perfectly?");
  static if (verbose) writefln("-- sig= %s",sig);
  static if (verbose) writefln("-- arg= %s",types2signature(targ));
  Type tp=TNull,ta=TNull;
  int k=0;
  for (;k<targ.length;++k) {
    if (k>=sig.length) break;
    tp=sig[k].type;
    ta=targ[k];
    static if (verbose) writef("-- %d : par= %s   arg= %s\n",k,types.str(tp),types.str(ta));
    if (type_matches(tp,ta)==exact_score) {
      continue;
    }
    static if (verbose) writef("fail\n");
    return false;
  }
  if (sig.is_open()) {
    tp=sig.open;
    for (;k<targ.length;++k) {
      ta=targ[k];
      static if (verbose) writef("par= %s   arg= %s\n",types.str(tp),types.str(ta));
      if (type_matches(tp,ta)==exact_score) {
        continue;
      }
      static if (verbose) writef("fail\n");
      return false;
    }
    return true;
  }
  for (;k<sig.length;++k) {
//    writef("default %s\n",cells.str(sig[k].defv));
    if (sig[k].defv.type==TNull) return false;
  }
  return true;
}
bool signature_matches_perfectly(Signature sig,Cell[] arg) {
  Type[] targ;
  targ.length=arg.length;
  for (int k;k<arg.length;++k) targ[k]=arg[k].type;
  return signature_matches_perfectly(sig,targ);
}

//------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------
//--------------------
//-------------------- type matching functions
//--------------------

const int score_shift=3;
const int exact_score=6;
const int super_score=4;
const int any_score=2;
const int fail_score=0;

int fields_match_unordered(Cell[] pfs,Cell[] afs) {
  // okay this is slow, but simple & works!
  if (pfs.length!=afs.length) return fail_score;
  Type[string] pfts,afts;
  for (int k;k<pfs.length;++k) {
    Cell pf=pfs[k];
    pfts[as_symbol(as_list(pf)[1])]=type(as_list(pf)[0]);
    Cell af=afs[k];
    afts[as_symbol(as_list(af)[1])]=type(as_list(af)[0]);
  }
  int worst_match=exact_score;
  foreach (key;pfts.keys) {
    if (!(key in afts)) return fail_score; // fail on missing field
    int match=type_matches(pfts[key],afts[key]);
    if (!match) return fail_score; // fail on submatch fail
    if (match<worst_match) worst_match=match;
  }
  return worst_match;
}
int fields_match_ordered(Cell[] pfs,Cell[] afs) {
  if (pfs.length!=afs.length) return fail_score;
  int worst_match=exact_score;
  for (int k;k<pfs.length;++k) {
    Cell pf=pfs[k];
    Cell af=afs[k];
    if (as_symbol(as_list(pf)[1])!=as_symbol(as_list(af)[0])) return fail_score; // fail on name mismatch
    int match=type_matches(type(as_list(pf)[1]),type(as_list(af)[0])); // check types
    if (!match) return fail_score; // fail on type mismatch
    if (match<worst_match) worst_match=match;
  }
  return worst_match;
}
int types_match_ordered(Cell[] pfs,Cell[] afs) {
  if (pfs.length!=afs.length) return fail_score;
  int worst_match=exact_score;
  for (int k;k<pfs.length;++k) {
    Cell pf=pfs[k];
    Cell af=afs[k];
    int match=type_matches(type(pf),type(af));
    if (!match) return fail_score; // fail on type mismatch
    if (match<worst_match) worst_match=match;
  }
  return worst_match;
}
int struct_class_or_union_type_matches(Type tp,Type ta) {
  Cell[] pfs=get_compound_fields(tp);
  if (!pfs.length) return super_score; // any struct accepted
  // we probably don't need to go down there:
  // if the structs are really equivalent, type interning solved this
  Cell[] afs=get_compound_fields(ta);
  return fields_match_ordered(pfs,afs);
}
int assoc_type_matches(Type tp,Type ta) {
  Cell[] pfs=get_compound_fields(tp);
  if (!pfs.length) return super_score; // any union accepted
  // we probably don't need to go down there:
  // if the assocs are really equivalent, type interning solved this
  Cell[] afs=get_compound_fields(ta);
  return types_match_ordered(pfs,afs);
}
int ref_type_matches(Type tp,Type ta) {
  Cell[] pfs=get_compound_fields(tp);
  if (!pfs.length) return super_score; // any ref accepted
  // we probably don't need to go down there:
  // if the assocs are really equivalent, type interning solved this
  Cell[] afs=get_compound_fields(ta);
  return types_match_ordered(pfs,afs);
}
int type_equal(Type tp,Type ta) {
  if (ta==TAny) return any_score;
  return type_matches(tp,ta);
}
int type_matches(Type tp,Type ta) {
  static if (0) {
    //writef(" s : %d : %d\n",is_struct_type(tp),is_struct_type(ta));
    writef(" 0 : %s : %s\n",types.str(tp),types.str(ta));
    writef(" 1 : %s : %s\n",types.str(tp.cell.type),types.str(ta.cell.type));
  }
  if (tp==TAny) return any_score;
  if (tp==ta) return exact_score;
  while (is_alias_type(tp)) tp=get_alias_subtype(tp);
  while (is_alias_type(ta)) ta=get_alias_subtype(ta);
  if (tp==ta) return exact_score;
  if (is_super_type(tp)) {
    Type[] tps=get_super_subtypes(tp);
    int bm;
    foreach (tpse;tps) {
      int m=type_matches(tpse,ta);
      if (m>bm) bm=m;
    }
    if (bm) --bm;
    return bm;
  }
  if (is_struct_type(tp) && is_struct_type(ta)) return struct_class_or_union_type_matches(tp,ta);
  if (is_class_type(tp) && is_class_type(ta)) return struct_class_or_union_type_matches(tp,ta);
  if (is_union_type(tp) && is_union_type(ta)) return struct_class_or_union_type_matches(tp,ta);
  if (is_assoc_type(tp) && is_assoc_type(ta)) return assoc_type_matches(tp,ta);
  if (is_ref_type(tp) && is_ref_type(ta)) return ref_type_matches(tp,ta);
  Cell cp=tp.cell;
  Cell ca=ta.cell;
  if (cp.type!=ca.type) return fail_score;
  if (cp.type!=TList) return fail_score;
  assert(cp.lst.length && ca.lst.length);
  assert(isa(cp.lst[0],TSymbol)&&isa(ca.lst[0],TSymbol));
  if (cp.lst[0].sym!=ca.lst[0].sym) return fail_score;
  if (cp.lst.length<2) return super_score;
  //assert((cp.lst.length==2) && (ca.lst.length==2));
  return type_matches(type(cp.lst[1]),type(ca.lst[1]))-1;
}
