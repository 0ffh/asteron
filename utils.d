module utils;

import std.date;
import std.math;
import std.stdio;
import std.string;
import std.format;
import std.random;
import std.c.stdio;
import std.c.string;
import std.c.stdlib;

alias std.string.toStringz tsz;

const bool initSelected=false;

d_time tictoctime;
void tic() {
  tictoctime=getUTCtime();
}
float toc() {
  return (cast(double)(getUTCtime()-tictoctime))/TicksPerSecond;
}
void exit(int code=0) {
  std.c.stdlib.exit(code);
}
int rand(int n) {
  return std.random.rand()%n;
}
void flush() {
  fflush(stdout);
}
string doformat(TypeInfo[] arguments,void* argptr) {
  string s;
  void putc(dchar c) {s~=c;}
  std.format.doFormat(&putc,arguments,argptr);
  return s;
}
string frm(...) {
  string s;
  void putc(dchar c) {s~=c;}
  std.format.doFormat(&putc,_arguments,_argptr);
  return s;
}
/*string cfrm(string fs,...) {
  string buffer;
  buffer.length=0x800;
  fs~='\0';
  std.c.stdio.vsprintf(buffer.ptr,fs.ptr,_argptr);
  buffer.length=strlen(buffer.ptr);
  return buffer;
}
void pr(string fs,...) {
  string buffer;
  buffer.length=0x800;
  fs~='\0';
  std.c.stdio.vsprintf(buffer.ptr,fs.ptr,_argptr);
  buffer.length=strlen(buffer.ptr);
  writef("%s",buffer);
}
void prln(string fs,...) {
  string buffer;
  buffer.length=0x800;
  fs~='\0';
  std.c.stdio.vsprintf(buffer.ptr,fs.ptr,_argptr);
  buffer.length=strlen(buffer.ptr);
  writef("%s\n",buffer);
}*/
string spaces(int n) {
  string s;
  s.length=n;
  while (n) s[--n]=' ';
  return s;
}
void indent(int n) {
  while (n-->0) writef("  ");
}
int sign(int i) {
  if (i>0) return +1;
  if (i<0) return -1;
  return 0;
}
int min(int a,int b) {
  return (a<b)?a:b;
}
int max(int a,int b) {
  return (a>b)?a:b;
}
int abs(int a) {
  return (a>=0)?a:-a;
}
string deCtrl(string s) {
  string hex="0123456789abcdef";
  string r="";
  for (int k=0;k<s.length;++k) {
    if (s[k]<0x20) {
      r~=`\`~hex[s[k]>>4]~hex[s[k]&15];
    } else {
      r~=s[k];
    }
  }
  return r;
}
/*char* dsz(string s) {
  return tsz(deCtrl(s));
}*/
string str(int n) {
  return std.string.toString(n);
}
void swap_elements(T)(T[] list,int i0,int i1) {
  T help=list[i0];
  list[i0]=list[i1];
  list[i1]=help;
}
void insert_element(T)(ref T[] list,int idx,T elem) {
  if (!idx) {
    list=elem~list;
    return;
  }
  if (idx>=list.length) {
    list~=elem;
    return;
  }
  int l=list.length;
  T[] tail=list[idx..$];
  list.length=idx;
  list~=elem~tail;
  assert((l+1)==list.length,"boohoo");
}
