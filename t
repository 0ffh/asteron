#!/usr/bin/lua
-- options
optimise=0
dmd_not_gdc=0
-- files
files={"main","emit_d",
       "cells","types","trafo",
       "environments","signatures",
       "libs","ablibs",
       "llparse","hlparse",
       "lexer","utils","debg"}
--
cstr=""
for _,f in ipairs(files) do
  cstr=cstr.." "..f..".d"
end
if dmd_not_gdc then
  if (optimise>0) then
    cstr="dmd -O -inline"..cstr
  else
    cstr="dmd"..cstr
  end
else
  if (optimise>0) then
    cstr="gdc -O3"..cstr
  else
    cstr="gdc -O0"..cstr
  end
  cstr=cstr.." -o main"
end
res=os.execute(cstr)
if res==0 then
  print("compiled okay, executing...")
  if arg[1] then
    os.execute("./main "..arg[1])
  else
    os.execute("./main")
  end
else
  print("build error ["..tostring(res).."]")
end
