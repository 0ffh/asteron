#!/usr/bin/lua
--res=os.execute("gdc -O3 main.d environments.d types.d signatures.d libs.d llparse.d hlparse.d lexer.d cells.d utils.d debg.d -o main")
--res=os.execute("dmd -O -inline main.d environments.d types.d signatures.d libs.d llparse.d hlparse.d lexer.d cells.d utils.d debg.d")
res=os.execute("gdc main.d environments.d types.d signatures.d libs.d llparse.d hlparse.d lexer.d cells.d utils.d debg.d -o main")
--res=os.execute("dmd main.d environments.d types.d signatures.d libs.d llparse.d hlparse.d lexer.d cells.d utils.d debg.d")
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
