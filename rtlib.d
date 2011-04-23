module rtlib;

import std.date;
import std.stdio;

int length(T)(T v) {
  return v.length;
}
string dofmt(TypeInfo[] arguments,void* argptr) {
  string s;
  void putc(dchar c) {s~=c;}
  std.format.doFormat(&putc,arguments,argptr);
  return s;
}
string tostr(...) {
  foreach (arg;_arguments) {
    return dofmt((&arg)[0..1],_argptr);
    auto size = arg.tsize();
    _argptr += ((size + size_t.sizeof - 1) & ~(size_t.sizeof - 1));
  }
  return "";
}
void pr(...) {
  foreach (arg;_arguments) {
    printf("%.*s ",dofmt((&arg)[0..1],_argptr));
    auto size = arg.tsize();
    _argptr += ((size + size_t.sizeof - 1) & ~(size_t.sizeof - 1));
  }
}
void prln(...) {
  foreach (arg;_arguments) {
    printf("%.*s ",dofmt((&arg)[0..1],_argptr));
    auto size = arg.tsize();
    _argptr += ((size + size_t.sizeof - 1) & ~(size_t.sizeof - 1));
  }
  printf("\n");
}
d_time tictoctime;
void tic() {
  tictoctime=getUTCtime();
}
float toc() {
  double dt=(cast(double)(getUTCtime()-tictoctime))/TicksPerSecond;
  writefln(dt);
  return dt;
}

