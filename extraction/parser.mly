%{
open Stal

let rec i2p = function 
  1 -> XH 
| n -> let n' = i2p (n/2) in 
       if (n mod 2)=0 then XO n' else XI n';;

%}

%token <int> VAR
%token AND OR NOT EQ IMPL TRUE FALSE
%token LPAREN RPAREN
%token EOF

%right EQ IMPL
%left OR
%left AND  
%nonassoc NOT 


%start main      
%type <Stal.expr> main

%%

main:
    expression EOF              {  $1 }
;
expression :
    VAR                  	{ V (i2p ($1+2))  }
  | TRUE 		  	{ V XH }
  | FALSE		    	{ N (V XH) }
  | LPAREN expression RPAREN    { $2 }
  | expression AND expression 	{ Node (ANd,$1,$3) }
  | expression OR expression    { Node (Or,$1,$3) }
  | expression IMPL expression  { Node (Impl,$1,$3) }
  | expression EQ expression	{ Node (eqOp,$1,$3) }
  | NOT expression              { N $2 }
;


