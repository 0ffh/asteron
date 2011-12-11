module debg;

import utils;
import std.stdio;
import std.format;

bool trace=false;
const bool debflag=!true;

void delegate() testfun;
const bool debEnable=debflag;
const bool debVerbose=debflag;
string[] debStringStack;

void debStack() {
  for (int k=0;k<debStringStack.length;++k) {
    indent(k*2);
    writef("%s\n",debStringStack[k]);
  }
}
void debLog(...) {
  static if (debEnable) {
    // generate debug string
    string s;
    void putc(dchar c) {s~=c;}
    std.format.doFormat(&putc,_arguments,_argptr);
    // output debug string
    static if (debVerbose) {
      indent(debStringStack.length);
      writef("%s",s);
      flush();
    }
    //
    if (testfun !is null) testfun();
  }
}
void debEnter(...) {
  static if (debEnable) {
    // generate debug string
    string s;
    void putc(dchar c) {s~=c;}
    std.format.doFormat(&putc,_arguments,_argptr);
    // push and output debug string
    static if (debVerbose) {
      indent(debStringStack.length);
      writef("%s {\n",s);
      flush();
    }
    debStringStack~=s;
    //
    if (testfun !is null) testfun();
  }
}
void debLeave(string lmsg="") {
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
        writef("} [%s]\n",lmsg);
      } else {
        writef("}\n");
      }
      flush();
    }
  }
}
void my_ass(T)(T p,lazy char[] msg="Fail!") {
  if (!p) {
    string m=msg();
//    writef("My ass in %s line %s: %s\n",__FILE__,__LINE__,m);
    writef("My ass: %s\n",m);
    assert(false,m);
  }
}
