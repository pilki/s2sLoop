/* to parse each line */


%token <BinInt.coq_Z> INT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE SEMICOL
%token EQUAL LT LEQ GT GEQ
%token FOR
%token EOF

%{
  open OCamlInterface
  open Conversions
%}

%%

main list_of_name:
| lst = statement_list list_of_name
