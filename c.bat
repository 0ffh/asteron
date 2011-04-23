@del main.exe > null
@set oldpath=%path%
@set path=c:\frank\work\d\dm\bin;c:\frank\work\d\dmd\windows\bin;%path%
@dmd main.d emit_d.d cells.d types.d trafo.d environments.d signatures.d libs.d ablibs.d llparse.d hlparse.d lexer.d utils.d debg.d
@set path=%oldpath%
