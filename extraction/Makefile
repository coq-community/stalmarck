CC= ocamlopt
FLAGS = -cclib -lunix
LIB= unix.cmxa

LEX= ocamllex
YACC= ocamlyacc

OBJ_I = stal.cmx \
	parser.cmi

OBJ= 	stal.cmx \
 	lexer.cmx \
	parser.cmx \
	main.cmx \
 
PROG= stalmarck


all : 	$(PROG)

$(PROG) :  $(OBJ_I) $(OBJ)	
	$(CC) $(FLAGS) -o $(PROG) $(LIB) $(OBJ) 

stal.ml : 
	cp ../run.ml stal.ml

parser.ml parser.mli : parser.mly
	$(YACC) parser.mly

lexer.ml : lexer.mll
	$(LEX) lexer.mll

%.cmi : %.mli
	$(CC) -c $<

%.cmx : %.ml
	$(CC) -c $<	 


clean : 	
	rm -f *.o *.cmx *.cmi \
	$(PROG) \
	stal.ml \
	lexer.ml \
	parser.ml \
	parser.mli

