module mk_libmath;

import std.c.stdio;

FILE* outfile;

void emit(string s) {
  fprintf(outfile,(s~"\0").ptr);
}

void mk_op(string opname,string op,string t0,string t1,string t2) {
  emit(`
Cell op_`~opname~`_`~t0~`_`~t1~`(Cell[] args) {
  static if (debf) {debEnter("[`~op~`]");scope (exit) debLeave();}
  assert(args.length==2);
  return `~t2~`Cell(as_`~t0~`(args[0])`~op~`as_`~t1~`(args[1]));
}`);
}
void mk_ops(string opname,string op) {
  mk_op(opname,op,"int","int","int");
  mk_op(opname,op,"int","float","float");
  mk_op(opname,op,"float","int","float");
  mk_op(opname,op,"float","float","float");
}
void main() {
  string newline="\n";
  outfile=fopen("libmath.d","w");
  string[][] oplist=[
    ["add","+"],
    ["sub","-"],
    ["mul","*"],
    ["div","/"]
  ];
  foreach (op;oplist) mk_ops(op[0],op[1]);
  emit("\n");
  foreach (op;oplist) {
    emit(`  env_putfun_sigstr(env,"`~op[1]~`",fun_cell(&op_`~op[0]~`_int_int),"(int int)","int");`~newline);
    emit(`  env_putfun_sigstr(env,"`~op[1]~`",fun_cell(&op_`~op[0]~`_int_float),"(int float)","float");`~newline);
    emit(`  env_putfun_sigstr(env,"`~op[1]~`",fun_cell(&op_`~op[0]~`_float_int),"(float int)","float");`~newline);
    emit(`  env_putfun_sigstr(env,"`~op[1]~`",fun_cell(&op_`~op[0]~`_float_float),"(float float)","float");`~newline);
  }
  fclose(outfile);
}
