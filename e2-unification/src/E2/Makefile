# Makefile generated by BNFC.

GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

# List of goals not corresponding to file names.

.PHONY : all clean distclean

# Default goal.

all : RSTT/Syntax/Test

# Rules for building the parser.

RSTT/Syntax/Abs.hs RSTT/Syntax/Lex.x RSTT/Syntax/Par.y RSTT/Syntax/Print.hs RSTT/Syntax/Test.hs : RSTT/Syntax.cf
	bnfc --haskell -p RSTT -d RSTT/Syntax.cf

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

RSTT/Syntax/Test : RSTT/Syntax/Abs.hs RSTT/Syntax/Lex.hs RSTT/Syntax/Par.hs RSTT/Syntax/Print.hs RSTT/Syntax/Test.hs
	${GHC} ${GHC_OPTS} $@

# Rules for cleaning generated files.

clean :
	-rm -f RSTT/Syntax/*.hi RSTT/Syntax/*.o RSTT/Syntax/*.log RSTT/Syntax/*.aux RSTT/Syntax/*.dvi

distclean : clean
	-rm -f RSTT/Syntax/Abs.hs RSTT/Syntax/Abs.hs.bak RSTT/Syntax/ComposOp.hs RSTT/Syntax/ComposOp.hs.bak RSTT/Syntax/Doc.txt RSTT/Syntax/Doc.txt.bak RSTT/Syntax/ErrM.hs RSTT/Syntax/ErrM.hs.bak RSTT/Syntax/Layout.hs RSTT/Syntax/Layout.hs.bak RSTT/Syntax/Lex.x RSTT/Syntax/Lex.x.bak RSTT/Syntax/Par.y RSTT/Syntax/Par.y.bak RSTT/Syntax/Print.hs RSTT/Syntax/Print.hs.bak RSTT/Syntax/Skel.hs RSTT/Syntax/Skel.hs.bak RSTT/Syntax/Test.hs RSTT/Syntax/Test.hs.bak RSTT/Syntax/XML.hs RSTT/Syntax/XML.hs.bak RSTT/Syntax/AST.agda RSTT/Syntax/AST.agda.bak RSTT/Syntax/Parser.agda RSTT/Syntax/Parser.agda.bak RSTT/Syntax/IOLib.agda RSTT/Syntax/IOLib.agda.bak RSTT/Syntax/Main.agda RSTT/Syntax/Main.agda.bak RSTT/Syntax/Syntax.dtd RSTT/Syntax/Syntax.dtd.bak RSTT/Syntax/Test RSTT/Syntax/Lex.hs RSTT/Syntax/Par.hs RSTT/Syntax/Par.info RSTT/Syntax/ParData.hs RSTT/Makefile
	-rmdir -p RSTT/Syntax/

# EOF
