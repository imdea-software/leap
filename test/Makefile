include ../Makefile.defs

PROJNAME=test

PARSER=../trsparser.mly 
LEXER=../trslexer.mll 
PARSER_ML=${PARSER:.mly=.ml}
PARSER_MLI=${PARSER:.mly=.mli}
LEXER_ML=${LEXER:.mll=.ml}


AUX_SOURCES=../debug.ml ../debug.mli \
	../aux.ml ../aux.mli \
	../interface.ml ../interface.mli \
	../expression.ml ../expression.mli \
	../global.ml ../global.mli \
	../statement.ml ../statement.mli \
	../system.ml ../system.mli \
	../vcgen.ml ../vcgen.mli \
	../diagrams.ml ../diagrams.mli \
	${PARSER} ${PARSER_ML} \
	${LEXER} ${LEXER_ML} \
	../numexpression.ml ../numexpression.mli \
	../yices.ml ../yices.mli

AUX_SOURCES_ML=$(filter %.ml, $(AUX_SOURCES))
AUX_SOURCES_MLI=$(filter %.mli, $(AUX_SOURCES))

WIDENING=test_widening

ALL=${WIDENING}

SOURCES=$(WIDENING).ml ${AUX_SOURCES}

DIRS = . ..

AUX_OBJS=$(AUX_SOURCES_ML:.ml=.cmx)

WIDENING_OBJS=${AUX_OBJS} test_widening.cmx

all:.depend.input .depend $(WIDENING)

$(WIDENING): ${WIDENING_OBJS}
	$(OCAMLOPT) -o $(WIDENING) $(OCAMLFLAGS) $(LIBS) $(WIDENING_OBJS)

INCLUDES = $(addprefix -I , ${DIRS})

include ../Makefile.common
