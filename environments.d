module environments;

import debg;
import utils;
import cells;
import types;
import signatures;
import std.stdio;

Env* environment;
Env*[] envstack;

const bool debf=debflag && 0;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Env
//----------------
struct Env {
  Env* outer;
  Cell[string] inner;
  Env* clone() {
    Env* e=[Env(outer,inner)].ptr;
    foreach (k;e.inner.keys) e.inner[k]=e.inner[k].clone();
    return e;
  }
  string toString() {
    return assoc_cell(this.inner).toString();
  }
  void show() {
    assoc_cell(this.inner).show();
  }
}
void pop_env() {
  assert(envstack.length);
  environment=envstack[$-1];
  envstack.length=envstack.length-1;
}
void push_env(Env* env=null,bool copy_tt=false) {
  envstack~=environment;
  if (!env) {
    env=mk_env(environment);
    // copy typetable
    if (copy_tt) {
      Cell tytc=env_get(environment,"type_table");
      TypeTable* oldtyt=as_typetable(tytc);
      TypeTable* tyt=cast(TypeTable*)([TypeTable()].ptr);
      foreach (string key;oldtyt.str2typ.keys) {
        Type val=oldtyt.str2typ[key];
        tyt.str2typ[key]=val;
        tyt.typ2str[val]=key;
      }
      tytc=typetable_cell(tyt);
      env_put(env,"type_table",tytc);
    }
  }
  environment=env;
}
void set_env(Env* env) {
  environment=env;
}
Env* mk_env(Env* outer=null) {
  static if (debf) {debEnter("mk_env()");scope (exit) debLeave();}
  Env e;
  e.outer=outer;
  e.inner=e.inner.init;
  return cast(Env*)([e].ptr);
}
Cell env_put(Env* e,string key,Cell value) {
  static if (debf) {debEnter("env_put('"~key~"')");scope (exit) debLeave();}
//   if (types_initialised && !(key=="type_table")) {
//     writef("env_put %s = %s [%s]\n",key,cells.str(value),types.str(value.type));
//   }
  //if (key=="foo") writefln("env_put %s %s\n",key,value);
  e.inner[key]=value;
  if (types_initialised && !(key=="type_table")) {
    value=e.inner[key];
  }
//   env_get(e,key);
  return value;
}
Cell env_get(Env* e,string key) {
  static if (debf) {debEnter("env_get('"~key~"')");scope (exit) debLeave();}
//  env_pr(e);
  Cell* c=key in e.inner;
  if (c !is null) {
//     if (types_initialised && !(key=="type_table")) {
//       writef("env_get %s = %s [%s]\n", key, cells.str(*c),types.str(c.type));
//     }
    //if (key=="foo") writefln("env_get %s %s\n",key,*c);
    return *c;
//     return c.clone();
  }
  if (e.outer !is null) {
//    writef("trying outer -> ");
    return env_get(e.outer,key);
  }
  assert(false,"env_get: '"~key~"' not found!");
}
Env* env_find(Env* e,string key) {
  static if (debf) {debEnter("env_find(Env*,'"~key~"')");scope (exit) debLeave();}
  if ((key in e.inner) !is null) {
    return e;
  }
  if (e.outer !is null) {
    return env_find(e.outer,key);
  }
  return null;
}
Env* env_clone(Env* self) {
  static if (debf) {debEnter("env_clone(Env*)");scope (exit) debLeave();}
  Env* e=mk_env(self.outer);
  foreach (key;self.inner.keys) env_put(e,key,self.inner[key]);
  return e;
}
void env_pr(Env* env) {
  foreach (key;env.inner.keys) {
    writef("  %s -> %s\n",key,cells.str(env.inner[key]));
  }
}
Cell env_putfun(Env* e,string key,Cell fun,Signature sig,Type ret) {
  return env_putfun(e,key,[FTabEntry(sig,ret,fun,false,null,"")].ptr);
}
Cell env_putfun(Env* e,string key,FTabEntry* fte) {
  static if (debf) {debEnter("env_putfun(Env*,string,Cell,Type[])");scope (exit) debLeave();}
  //-- read or generate function table
  FTab* ft;
  Cell* c=(key in e.inner);
  if (c) {
    if (!isa(*c,TFtab)) assert(false,"Trying to defun '"~key~"' over existing symbol.");
    ft=c.ftab;
  } else {
    ft=mk_ftab();
    c=cast(Cell*)([ftab_cell(ft)].ptr);
    e.inner[key]=*c;
  }
  //--
  //writef("env_putfun %s %s\n",key,lambda_cell(fte.fun.lam));
  ftab_add(ft,fte);
  //if (isa(fte.fun,TLambda)) writef("env_putfun %s %s\n",key,lambda_cell(fte.fun.lam));
  //
  return *c;
}
Cell env_putfun_sigstr(Env* e,string key,Cell fun,string sigstr,string retstr) {
  static if (debf) {debEnter("env_putfun_sigstr(Env*,string,Cell,string,string)");scope (exit) debLeave();}
  return env_putfun(e,key,fun,signature_string2signature(sigstr),type(retstr));
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- FTab
//----------------

struct FTabEntry {
  Signature sig;
  Type      ret;
  Cell      fun;
  bool      abt; // aborted
  Env*      env;
  string    nam;
  FTabEntry* clone() {
    FTabEntry* n=[FTabEntry(sig,ret,fun,abt,env,nam)].ptr;
    n.fun=n.fun.clone();
    n.sig=n.sig.clone();
    n.ret=TAny;
    return n;
  }
}
struct FTab {
  Env*         env;
  FTabEntry*[] dat;
}
FTab* mk_ftab(Env* e=null) {
  if (!e) e=environment;
  FTab l;
  l.env=e;
  return cast(FTab*)[l].ptr;
}
string str(FTab* ft) {
  string s;
  foreach (FTabEntry* e;ft.dat) {
    s~="("~signatures.str(e.sig)~" -> "~types.str(e.ret)~" "~cells.str(e.fun)~") ";
  }
  if (s.length) {
    s.length=s.length-1;
  } else {
    s="()";
  }
  return s;
}
bool ftab_add(FTab* ft,FTabEntry* fte) {
  static if (debf) {debEnter("ftab_add(FTab*,FTabEntry)");scope (exit) debLeave();}
//  writef("*** ftab_add %s\n",fte.fun);
  fte.env=ft.env;
  ft.dat~=fte;
  return true;
}
FTabEntry* ftab_resolve(FTab *ft,Cell[] args,string id="") {
  //static if (debf) {debEnter("ftab_resolve('"~id~")'");scope (exit) debLeave();}
  // parameters vs. arguments
  //   in definition: parameter
  //   at call site: argument
  Type[] targs;
  targs.length=args.length;
  for (int k;k<targs.length;++k) targs[k]=args[k].type;
  return ftab_resolve(ft,targs,id);
}
FTabEntry* ftab_resolve(FTab* ft,Type[] targs,string id="") {
  static if (debf) {debEnter("ftab_resolve('"~id~"')");scope (exit) debLeave();}
  // parameters vs. arguments
  //   in definition: parameter
  //   at call site: argument
//  writefln("resolving %s%s",id,targs);
  const bool show=true;
  bool trace=true;
  //--
  static if (show) {
    if (trace) {
      writef("--- ftab_resolve %s%s\n",id,targs);
/*      writef("call arguments:\n ");
      foreach (ta;targs) writef(" %s",types.str(ta));
      writef("\navailable parameters:\n");*/
    }
  }
  int bestp=0,bestk=0,ambiguous=0;
  for (int k=0;k<ft.dat.length;++k) {
    Signature sig=ft.dat[k].sig;
    int p=signature_matches(sig,targs);
    static if (show) {
      if (trace) {
        writef(" ");
        writef(" %s",sig);
        writef(" -> %d\n",p);
      }
    }
    if (p==bestp) ambiguous=1;
    if (p>bestp) {
      ambiguous=0;
      bestp=p;
      bestk=k;
    }
  }
//  writef("best match for %s%s -> %d\n",id,types.str(targs),bestp);
  if (!bestp) {
//    writef("No match found for function signature %s!\n",types.str(targs));
//    assert(false);
    return null;
  }
  if (ambiguous) {
    writef("No unambiguous match found for function signature %s!\n",types.str(targs));
    assert(false);
//    return null;
  }
  writef("best match for %s%s -> %s\n",id,targs,ft.dat[bestk].fun);
  return ft.dat[bestk];
}

