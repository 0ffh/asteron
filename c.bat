@del main.exe > null
@set oldpath=%path%
@set path=c:\d\dm\bin;c:\d\dmd\windows\bin;%path%
@dmd main.d environments.d types.d signatures.d libs.d llparse.d hlparse.d lexer.d cells.d utils.d debg.d
@set path=%oldpath%
