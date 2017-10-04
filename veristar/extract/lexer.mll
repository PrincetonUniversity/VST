{ (* header *)

open Lexing
open Parser

(* association list of keywords *)
let keyword_al = [
  ("dispose",DISPOSE);
  ("else",ELSE);
  ("emp",EMPTY);
  ("if",IF);
  ("local",LOCAL);
  ("new",NEW);
  ("resource",RESOURCE);
  ("then",THEN);
  ("when",WHEN);
  ("while",WHILE);
  ("with", WITH);
  ("dlseg",DLSEG);
  ("list" ,LIST);
  ("lseg",LISTSEG);
  ("tree" ,TREE);
  ("xlseg",XLSEG);
  ("true" ,TT);
  ("false",FF);
  ("NULL",NAT(0))]

(* To store the position of the beginning of a string and comment *)
let string_start_loc = ref Location.none;;
let comment_start_loc = ref [];;
let in_comment () = !comment_start_loc <> [];;

(* Update the current location with file name and line number. *)
let update_loc lexbuf line absolute chars =
  let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with
	  pos_lnum = if absolute then line else pos.pos_lnum + line;
	  pos_bol = pos.pos_cnum - chars; }

(* Initialize file name and starting position *)
let init lexbuf file =
  Location.lexbuf := Some lexbuf;
  update_loc lexbuf 1 true 0;
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file; };
  lexbuf.lex_start_p <- lexbuf.lex_curr_p

}
(* regular expressions *)

let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let letter = ['A'-'Z' '_' 'a'-'z']
let digit = ['0'-'9']
let alphanum = digit | letter
let ident = letter alphanum*
let qident = '_' ident
let num = digit+

(* entry points *)

rule token = parse
  | newline { update_loc lexbuf 1 false 0;
              token lexbuf }
  | blank+ { token lexbuf }
  | "/*" { comment_start_loc := [lexbuf.lex_curr_p];
           comment lexbuf;
           token lexbuf }
  | "|->" { POINTSTO }
  | ","  { COMMA }
  | "{"  { LBRACE }
  | "["  { LBRACKET }
  | "("  { LPAREN }
  | "->" { MINUSGREATER }
  | "}"  { RBRACE }
  | "]"  { RBRACKET }
  | ")"  { RPAREN }
  | ";"  { SEMI }
  | "&&" { AMPERAMPER }
  | "||" { BARBAR }
  | ":"  { COLON }
  | "="  { EQUAL }
  | "==" { EQUALEQUAL }
  | "!=" { BANGEQUAL }
  | "<" | "<=" | ">" | ">=" { INFIXOP1(Lexing.lexeme lexbuf) }
  | "+" | "-"               { INFIXOP2(Lexing.lexeme lexbuf) }
  | "/" | "%"               { INFIXOP3(Lexing.lexeme lexbuf) }
  | "*"     { STAR }
  | "^"     { XOR }
  | num { NAT(int_of_string(Lexing.lexeme lexbuf)) }
  | ident { let s = Lexing.lexeme lexbuf in
              try List.assoc s keyword_al
              with Not_found -> IDENT(s) }
  | qident { QIDENT(Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { raise(Error.Illegal_character
		(Lexing.lexeme_char lexbuf 0,
		 Location.mkloc(lexbuf.lex_start_p) (lexbuf.lex_curr_p))) }

and comment = parse
    "/*" { comment_start_loc := lexbuf.lex_curr_p :: !comment_start_loc;
           comment lexbuf; }
  | "*/" { match !comment_start_loc with
             | [] -> assert false
             | [x] -> comment_start_loc := [];
             | _ :: l -> comment_start_loc := l;
                 comment lexbuf; }
  | eof { match !comment_start_loc with
            | [] -> assert false
            | loc :: _ -> comment_start_loc := [];
		raise(Error.Unterminated_comment
			(Location.mkloc loc (lexbuf.lex_curr_p))) }
  | newline { update_loc lexbuf 1 false 0;
              comment lexbuf }
  | _ { comment lexbuf }

{ (* trailer *)
}
