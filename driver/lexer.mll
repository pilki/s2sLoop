(**************************************************************************)
(*                                                                        *)
(*  Menhir                                                                *)
(*                                                                        *)
(*  François Pottier, INRIA Rocquencourt                                  *)
(*  Yann Régis-Gianas, PPS, Université Paris Diderot                      *)
(*                                                                        *)
(*  Copyright 2005-2008 Institut National de Recherche en Informatique    *)
(*  et en Automatique. All rights reserved. This file is distributed      *)
(*  under the terms of the Q Public License version 1.0, with the change  *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(**************************************************************************)

{
  open Parser
  
  exception Error of string

}

let comment = ("/*" ([^'*']* ('*' [^'/'])?)*  "*/") | ("//" [^'\n']* '\n')  
let spaces = 
  ([' ' '\t' '\n'] | comment)+
let spaces_opt = spaces?

rule prefix = 
| _ * "#pragma" ' '+ "scop" ' '* '\n' spaces_opt
    { () }
and line (b: Buffer.t) = parse
| ([^' ' '\t' '\n' '/' ';']+ as s) spaces_opt
    { Buffer.add_string b s;
      line b lexbuf}
| '/' spaces_opt
    { Buffer.add_char b '/';
      line b lexbuf}
| ';' spaces_opt
    { Buffer.add_char b ';';
      Buffer.contents b}

(* produce lines *)
and linearize = parse
| ("for" spaces_opt '(' [^';']* ';'[^';']* ';' [^')']*')' spaces_opt) as s
    {FOR_LINE s}
| '{' spaces_opt
    { OPEN_FOR_BLOCK }
| '}' spaces_opt
    { CLOSE_FOR_BLOCK}
| "#pragma endscop\n" _ *
| eof
    { END_OF_FILE}
| { let b = Buffer.create 100 in NORMAL_LINE (line b lexbuf)}


and token = parse
| spaces_opt
    { token lexbuf }
| ['0'-'9']+ as i
    { INT (z_of_string i) }
| '+'
    { PLUS }
| '-'
    { MINUS }
| '*'
    { TIMES }
| '/'
    { DIV }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| '{'
    { LBRACE }
| '}'
    { RBRACE }
| '['
    { LBRACKET }
| ']'
    { RBRACKET }
| ';'
    { SEMICOL }
| "<="
    { LEQ }
| '<'
    { LT }
| ">="
    { GEQ }
| '>'
    { GT }
| "for"
    { FOR }
| eof
    { EOF }
| 
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

