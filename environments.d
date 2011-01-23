module environments;

import debg;
import utils;
import cells;
import types;
import signatures;

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- FTab
//----------------

struct FTabEntry {
  Signature sig;
  Type      ret;
  Cell      fun;
}
typedef FTabEntry[] FTab;
FTab* mk_ftab() {
  FTab l;
  return cast(FTab*)[l].ptr;
}
string str(FTab* ft) {
  string s;
  foreach (FTabEntry e;*ft) {
    s~="("~signatures.str(e.sig)~" -> "~types.str(e.ret)~" "~cells.str(e.fun)~") ";
  }
  if (s.length) {
    s.length=s.length-1;
  } else {
    s="()";
  }
  return s;
}
bool ftab_add(FTab* ft,Cell fun,Signature sig,Type ret) {
  static if (debf) {debEnter("ftab_add(FTab*,Cell,Type[])");scope (exit) debLeave();}
//  printf("*** %.*s\n",str(tpar));
  Cell* now;// =ftab_find(ft,par);
  if (now !is null) return false;
  (*ft)~=FTabEntry(sig,ret,fun);
  return true;
}
FTabEntry* ftab_resolve(FTab *ft,Cell[] args,string id="") {
  static if (debf) {debEnter("ftab_resolve("~id~")");scope (exit) debLeave();}
  // parameters vs. arguments
  //   in definition: parameter
  //   at call site: argument
  const bool show=!true;
  bool trace=true;
  //--
  Type[] targs;
  targs.length=args.length;
  for (int k;k<targs.length;++k) {
    targs[k]=args[k].type;
  }
  //--
  static if (show) {
    if (trace) {
      printf("--- ftab_resolve %.*s\n",id);
      printf("call arguments:\n ");
      foreach (ta;targs) printf(" %.*s",types.str(ta));
      printf("\navailable parameters:\n");
    }
  }
  int bestp=0,bestk=0,ambiguous=0;
  for (int k=0;k<ft.length;++k) {
    Signature sig=(*ft)[k].sig;
    int p=signature_matches(sig,targs);
    static if (show) {
      if (trace) {
        printf(" ");
        foreach (se;sig) printf(" %.*s",types.str(se.type));
        printf(" -> %i\n",p);
      }
    }
    if (p==bestp) ambiguous=1;
    if (p>bestp) {
      ambiguous=0;
      bestp=p;
      bestk=k;
    }
  }
  if (!bestp) {
    //printf("No match found for function signature %.*s!\n",types.str(targs));
    return null;
  }
  if (ambiguous) {
    printf("No unambiguous match found for function signature %.*s!\n",types.str(targs));
    assert(false);
  }
  //assert(false);
  return &((*ft)[bestk]);
}

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------
//---------------- Env
//----------------

struct Env {
  Env* outer;
  Cell[string] inner;
  void show() {
    assoc_cell(this.inner).show();
  }
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
  return e.inner[key]=value;
}
Cell env_get(Env* e,string key) {
  static if (debf) {debEnter("env_get('"~key~"')");scope (exit) debLeave();}
  Cell* c=key in e.inner;
//  printf("env_get %.*s -> %p\n",key,c);
//  env_pr(e);
  if (c !is null) return *c;
  if (e.outer !is null) {
//    printf("trying outer -> ");
    return env_get(e.outer,key);
  }
  assert(false,"env_get: '"~key~"' not found!");
}
Env* env_find(Env* e,string key) {
  static if (debf) {debEnter("env_find(Env*,"~key~")");scope (exit) debLeave();}
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
  foreach (key;self.inner.keys) env_put(e,key,env_get(self,key));
  return e;
}
void env_pr(Env* env) {
  foreach (key;env.inner.keys) {
    printf("  %.*s -> %.*s\n",key,cells.str(env.inner[key]));
  }
}
Cell env_putfun(Env* e,string key,Cell fun,Signature sig,Type ret) {
  static if (debf) {debEnter("env_putfun(Env*,string,Cell,Type[])");scope (exit) debLeave();}
  //-- read or generate function table
  FTab* ft;
  Cell* c=(key in e.inner);
  if (c) {
    if (!isa(*c,TFtab)) assert(false,"Trying to defun '"~key~"' over existing symbol.");
    ft=c.ftab;
  } else {
    ft=mk_ftab();
  }
  //--
  //printf("putfun %.*s%.*s\n",key,str(par));
  ftab_add(ft,fun,sig,ret);
  //
  return e.inner[key]=ftab_cell(ft);
}
Cell env_putfun_sigstr(Env* e,string key,Cell fun,string sigstr,string retstr) {
  static if (debf) {debEnter("env_putfun_sigstr(Env*,string,Cell,string,string)");scope (exit) debLeave();}
  return env_putfun(e,key,fun,signature_string2signature(sigstr),type(retstr));
}
