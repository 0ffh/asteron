#!/usr/bin/lua
-- options
optimise=0
dmd_not_gdc=0
-- files
files={"ac","emit_d","ablibs",
       "eval_helpers",
       "cells","types","trafo",
       "environments","signatures",
       "sexpr_parser","lexer",
       "utils","debg"}
--
cstr=""
for _,f in ipairs(files) do
  cstr=cstr.." "..f..".d"
end
if dmd_not_gdc then
  if (optimise>0) then
    cstr="dmd -O -inline"..cstr
  else
    cstr="dmd "..cstr
  end
else
  if (optimise>0) then
    cstr="gdc -O3"..cstr
  else
    cstr="gdc -O0"..cstr
  end
  cstr=cstr.." -o "..files[1]
end
res=os.execute(cstr)
if res==0 then
  print("compiled okay, executing...")
  if arg[1] then
    os.execute("./"..files[1].." "..arg[1])
  else
    os.execute("./"..files[1])
  end
else
  print("build error ["..tostring(res).."]")
end
