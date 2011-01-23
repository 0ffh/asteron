
Cell op_add_int_int(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  assert(args.length==2);
  return intCell(as_int(args[0])+as_int(args[1]));
}
Cell op_add_int_float(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_int(args[0])+as_float(args[1]));
}
Cell op_add_float_int(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])+as_int(args[1]));
}
Cell op_add_float_float(Cell[] args) {
  static if (debf) {debEnter("[+]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])+as_float(args[1]));
}
Cell op_sub_int_int(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  assert(args.length==2);
  return intCell(as_int(args[0])-as_int(args[1]));
}
Cell op_sub_int_float(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_int(args[0])-as_float(args[1]));
}
Cell op_sub_float_int(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])-as_int(args[1]));
}
Cell op_sub_float_float(Cell[] args) {
  static if (debf) {debEnter("[-]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])-as_float(args[1]));
}
Cell op_mul_int_int(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  assert(args.length==2);
  return intCell(as_int(args[0])*as_int(args[1]));
}
Cell op_mul_int_float(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_int(args[0])*as_float(args[1]));
}
Cell op_mul_float_int(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])*as_int(args[1]));
}
Cell op_mul_float_float(Cell[] args) {
  static if (debf) {debEnter("[*]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])*as_float(args[1]));
}
Cell op_div_int_int(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  assert(args.length==2);
  return intCell(as_int(args[0])/as_int(args[1]));
}
Cell op_div_int_float(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_int(args[0])/as_float(args[1]));
}
Cell op_div_float_int(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])/as_int(args[1]));
}
Cell op_div_float_float(Cell[] args) {
  static if (debf) {debEnter("[/]");scope (exit) debLeave();}
  assert(args.length==2);
  return floatCell(as_float(args[0])/as_float(args[1]));
}
  env_putfun_sigstr(env,"+",fun_cell(&op_add_int_int),"(int int)","int");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_int_float),"(int float)","float");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_float_int),"(float int)","float");
  env_putfun_sigstr(env,"+",fun_cell(&op_add_float_float),"(float float)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_int_int),"(int int)","int");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_int_float),"(int float)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_float_int),"(float int)","float");
  env_putfun_sigstr(env,"-",fun_cell(&op_sub_float_float),"(float float)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_int_int),"(int int)","int");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_int_float),"(int float)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_float_int),"(float int)","float");
  env_putfun_sigstr(env,"*",fun_cell(&op_mul_float_float),"(float float)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_int_int),"(int int)","int");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_int_float),"(int float)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_float_int),"(float int)","float");
  env_putfun_sigstr(env,"/",fun_cell(&op_div_float_float),"(float float)","float");
