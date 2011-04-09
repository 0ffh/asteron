module debg;

import utils;
import std.c.string;

bool trace=false;
const bool debflag=true;

void delegate() testfun;
const bool debEnable=debflag;
const bool debVerbose=debflag;
string[] debStringStack;

void debStack() {
  for (int k=0;k<debStringStack.length;++k) {
    indent(k*2);
    printf("%.*s\n",debStringStack[k]);
  }
}
void debLog(string fs,...) {
  static if (debEnable) {
    // generate debug string
    string s;
    s.length=0x800;
    fs~='\0';
    std.c.stdio.vsprintf(s.ptr,fs.ptr,_argptr);
    s.length=strlen(s.ptr);
    // output debug string
    static if (debVerbose) {
      indent(debStringStack.length);
      printf("%s",tsz(s));
      flush();
    }
    //
    if (testfun !is null) testfun();
  }
}
void debEnter(string fs,...) {
  static if (debEnable) {
    // generate debug string
    string s;
    s.length=0x800;
    fs~='\0';
    std.c.stdio.vsprintf(s.ptr,fs.ptr,_argptr);
    s.length=strlen(s.ptr);
    // push and output debug string
    static if (debVerbose) {
      indent(debStringStack.length);
      printf("%s {\n",tsz(s));
      flush();
    }
    debStringStack~=s;
    //
    if (testfun !is null) testfun();
  }
}
void debLeave(String lmsg="") {
  static if (debEnable) {
    // ensure stack is nonempty
    assert(debStringStack.length>0,"debug stack empty!");
    // pop and output debug string
    string s=debStringStack[$-1];
    if (testfun !is null) testfun(); // test before removal
    debStringStack.length=debStringStack.length-1;
    static if (debVerbose) {
      indent(debStringStack.length);
      if (lmsg.length) {
        printf("} [%.*s]",lmsg);
      } else {
        printf("}\n");
      }
      flush();
    }
  }
}
void my_ass(T)(T p,lazy char[] msg="Fail!") {
  if (!p) {
    string m=msg();
//    printf("My ass in %.*s line %.*s: %.*s\n",__FILE__,__LINE__,m);
    printf("My ass: %.*s\n",m);
    assert(false,m);
  }
}
