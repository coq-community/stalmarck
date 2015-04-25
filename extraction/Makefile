CC= $(CAMLBIN)ocamlopt
FLAGS = -cclib -lunix
LIB= unix.cmxa

LEX= $(CAMLBIN)ocamllex
YACC= $(CAMLBIN)ocamlyacc

OBJ_I = stal.cmx \
	parser.cmi

OBJ= 	stal.cmx \
	lexer.cmx \
	parser.cmx \
	main.cmx \

PROG= stalmarck


all : 	$(PROG)

$(PROG) : $(OBJ_I) $(OBJ)
	$(CC) $(FLAGS) -o $(PROG) $(LIB) $(OBJ)

stal.ml :
	cp ../run.ml stal.ml

stal.mli :
	cp ../run.mli stal.mli

parser.ml : parser.mly
	$(YACC) parser.mly

parser.mli : parser.ml

parser.cmi : stal.cmi

lexer.ml : lexer.mll
	$(LEX) lexer.mll

%.cmi : %.mli
	$(CC) -c $<

%.cmx : %.ml
	$(CC) -c $<

%.ml.d : %.ml | lexer.ml parser.ml
	$(CAMLBIN)ocamldep $< > $@

clean :
	rm -f *.o *.cmx *.cmi \
	$(PROG) \
	stal.ml \
	lexer.ml \
	parser.ml \
	parser.mli

ifneq ($(MAKECMDGOALS),clean)
include $(OBJ:.cmx=.ml.d)
endif
