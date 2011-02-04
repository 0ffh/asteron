module signatures;

import debg;
import utils;
import cells;
import types;
import llparse;
import environments;

const int exact_score=3;
const int super_score=2;
const int any_score=1;
const int fail_score=0;

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
typedef SigElement[] Signature;

int is_open_signature(Signature sig) {
  if (!sig.length) return 0;
  return sig[$-1].name=="...";
}
string str(Signature sig) {
  string s="(";
  for (int k;k<sig.length;++k) {
    s~=types.str(sig[k].type)~" ";
    if (sig[k].defv.type!=TNull) s~="[="~cells.str(sig[k].defv)~"] ";
  }
  if (sig.length) s.length=s.length-1;
  return s~")";
}
bool is_sym(Cell c,string s) {
  return ((c.type==TSymbol)&&(c.sym==s));
}
/*Signature argument_string2signature(string argstr) {
  static if (debf) {debEnter("argument_string2signature(string)");scope (exit) debLeave();}
  return parameter_cell2signature(lparse(argstr));
}*/
Signature signature_string2signature(string sigstr) {
  static if (debf) {debEnter("signature_string2signature(string)");scope (exit) debLeave();}
  return signature_cell2signature(lparse(sigstr));
}
Signature parameter_cell2signature(Cell arg) {
  static if (debf) {debEnter("parameter_cell2signature(Cell)");scope (exit) debLeave();}
  if (!isa(arg,TList)) assert(false);
  Signature sig;
  for (int k;k<arg.lst.length;++k) {
    // options for each entry:
    //   name
    //   (name)
    //   (name = default)
    //   (type name)
    //   (type name = default)
    Cell a=arg.lst[k];
    if (isa(a,TSymbol)) {
      sig~=SigElement(a.sym,TAny,null_cell());
      continue;
    }
    if (!isa(a,TList)) assert(false);
    if (!a.lst.length) assert(false);
    SigElement se;
    if ((a.lst.length>2) && (is_sym(a.lst[$-2],"="))) {
      se.defv=a.lst[$-1];
      a.lst.length=a.lst.length-2;
    } else {
      se.defv=null_cell();
    }
    if (a.lst.length==2) {
      se.name=as_symbol(a.lst[1]);
      se.type=type(a.lst[0]);
    } else {
      se.name=as_symbol(a.lst[0]);
      se.type=TAny;
    }
    sig~=se;
  }
  //printf("%.*s -> %.*s\n",cells.str(arg),str(sig));
  return sig;
}
Signature signature_cell2signature(Cell arg) {
  static if (debf) {debEnter("signature_cell2signature(Cell)");scope (exit) debLeave();}
  const int verbose=false;
  if (!isa(arg,TList)) assert(false);
  Signature sig;
  static if (verbose) printf("signature_cell2signature");
  for (int k;k<arg.lst.length;++k) {
    // options for each entry:
    //   type
    SigElement se;
    se.name=""; // there's never a parameter name
    Cell a=arg.lst[k];
    if ((isa(a,TSymbol)) && (a.sym=="=")) {
      a=arg.lst[++k];
      sig[$-1].defv=a;
      continue;
    }
    static if (verbose) printf(" %.*s",cells.str(a));
    se.type=type(a);
    se.defv=null_cell();
    sig~=se;
  }
  static if (verbose) printf("\n");
  return sig;
}
/*Signature types2signature(Type[] args) {
  static if (debf) {debEnter("signature_cell2signature(Cell)");scope (exit) debLeave();}
  const int verbose=false;
  Signature sig;
  static if (verbose) printf("signature_cell2signature");
  for (int k;k<args.length;++k) {
    SigElement se;
    se.name=""; // there's never a parameter name
    static if (verbose) printf(" %.*s",types.str(args[k]));
    se.type=args[k];
    se.defv=null_cell();
    sig~=se;
  }
  static if (verbose) printf("\n");
  return sig;
}*/
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
int struct_type_matches(Type tp,Type ta) {
  Cell[] pfs=get_compound_fields(tp);
  if (!pfs.length) return super_score; // any struct accepted
  // we probably don't need to go down there:
  // if the structs are really equivalent, type interning solved this
  Cell[] afs=get_compound_fields(ta);
  return fields_match_ordered(pfs,afs);
}
int union_type_matches(Type tp,Type ta) {
  Cell[] pfs=get_compound_fields(tp);
  if (!pfs.length) return super_score; // any union accepted
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
    //printf(" s : %i : %i\n",is_struct_type(tp),is_struct_type(ta));
    printf(" 0 : %.*s : %.*s\n",types.str(tp),types.str(ta));
    printf(" 1 : %.*s : %.*s\n",types.str(tp.cell.type),types.str(ta.cell.type));
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
  if (is_struct_type(tp) && is_struct_type(ta)) return struct_type_matches(tp,ta);
  if (is_union_type(tp) && is_union_type(ta)) return union_type_matches(tp,ta);
  if (is_assoc_type(tp) && is_assoc_type(ta)) return assoc_type_matches(tp,ta);
  if (is_ref_type(tp) && is_ref_type(ta)) return ref_type_matches(tp,ta);
  Cell cp=*tp.cell;
  Cell ca=*ta.cell;
  if (cp.type!=ca.type) return fail_score;
  if (cp.type!=TList) return fail_score;
  assert(isa(cp.lst[0],TSymbol)&&isa(ca.lst[0],TSymbol));
  if (cp.lst[0].sym!=ca.lst[0].sym) return fail_score;
  return type_matches(type(cp.lst[1]),type(ca.lst[1]));
}
int signature_matches(Signature sig,Type[] targ) {
  static if (debf) {debEnter("signature_matches(Signature,Type[])");scope (exit) debLeave();}
  const int verbose=!true;
  int p=1;
  if ((targ.length>sig.length) && (!is_open_signature(sig))) return fail_score;
  static if (verbose) printf("-- sig= %.*s\n",str(sig));
  static if (verbose) printf("-- arg= %.*s\n",str(types2signature(targ)));
  for (int k;k<targ.length;++k) {
    if (sig[k].name=="...") return (p<<2)-1;
    Type tp=sig[k].type;
    Type ta=targ[k];
    p<<=2;
    static if (verbose) printf("par= %.*s   arg= %.*s\n",types.str(tp),types.str(ta));
    int m=type_matches(tp,ta);
    if (m) {
      p+=m;
      continue;
    }
    static if (verbose) printf("fail\n");
    return fail_score;
  }
  for (int k=targ.length;k<sig.length;++k) {
//    printf("default %.*s\n",cells.str(sig[k].defv));
    if (sig[k].name=="...") return p-1;
    if (sig[k].defv.type==TNull) return fail_score;
  }
  return p;
}


