%token <string> FOR_LINE
%token <string> NORMAL_LINE
%token OPEN_FOR_BLOCK CLOSE_FOR_BLOCK
%token END_OF_FILE

%start <naked_statement list> naked_statement_list

%{
open OCamlInterface
open Conversions
open LineParser
open ParsingHelp
%}

%%

naked_statement_list:
| END_OF_FILE
{ [] }
| ns = naked_statement nsl = naked_statement_list
{ ns :: nsl}

naked_statement:
| s = FOR_LINE
