%{ (* header *)

open Misc
open Parsetree

let mkexp d = { pexp_desc = d; pexp_loc = Location.symbol_loc() }
let mkexp_ghost d = { pexp_desc = d; pexp_loc = Location.none }
let mkstm d = { pstm_desc = d; pstm_loc = Location.symbol_loc() }
let mkstm_ghost d = { pstm_desc = d; pstm_loc = Location.none }

let check_distinct il s loc =
  let is = ref StringSet.empty in
  let f i = if StringSet.mem i !is
  then raise(Error.Not_distinct(s,loc))
  else is := StringSet.add i !is
  in List.iter f il

let mk_formal_params (rl,vl) loc =
  check_distinct (rl@vl) "Formal parameters" loc;
  (rl,vl)

let mk_ref_params cel loc =
  let check_par = function
    | {pexp_desc = Pexp_ident i} -> i
    | _ -> raise(Error.Parameters_not_variables(loc)) in
  let il = List.map check_par cel
  in check_distinct il "Reference parameters" loc;
     il

(* implicitly called when no grammar rules apply *)
let parse_error _ =
  raise(
    Error.Parse_error(
      match !Location.lexbuf with
	| None -> Location.symbol_loc()
	| Some lexbuf ->
	    (* the Parsing library only updates symbol_end_pos when successfully
	     * reducing a grammar rule, so here we ask the lexer for the current
	     * position directly *)
	    Location.mkloc (Parsing.symbol_start_pos()) lexbuf.Lexing.lex_curr_p))

%} /* declarations */

/* tokens */

%token AMPERAMPER
%token BANGEQUAL
%token BARBAR
%token COLON
%token COMMA
%token DISPOSE
%token DLSEG
%token ELSE
%token EMPTY
%token EOF
%token EQUAL
%token EQUALEQUAL
%token FF
%token <string> IDENT
%token <string> QIDENT
%token IF
%token <string> INFIXOP1
%token <string> INFIXOP2
%token <string> INFIXOP3
%token LBRACE
%token LBRACKET
%token LIST
%token LISTSEG
%token LOCAL
%token LPAREN
%token MINUSGREATER
%token <int> NAT
%token NEW
%token POINTSTO
%token RBRACE
%token RBRACKET
%token RESOURCE
%token RPAREN
%token SEMI
%token STAR
%token THEN
%token TREE
%token TT
%token WHEN
%token WHILE
%token WITH
%token XLSEG
%token XOR

/* precedences (increasing) and associativities for expressions */

%nonassoc below_ELSE
%nonassoc ELSE
%left STAR AMPERAMPER
%left EQUALEQUAL BANGEQUAL
%left INFIXOP1 EQUAL
%left INFIXOP2
%left INFIXOP3 XOR POINTSTO
%nonassoc unary_prefix

/* entry points */

%start program
%type <Parsetree.p_program> program

%start a_proposition
%type <Parsetree.a_proposition> a_proposition


%% /* rules */

/* entry points */
program:
  | program_item_star
      { Pprogram ([Config.list_data_tag; Config.list_link_tag;
		   Config.tree_data_tag;
		   fst Config.tree_link_tags; snd Config.tree_link_tags],
		  $1) }
  | ident_decl program_item_star { Pprogram ($1,$2) }
;
program_item_star:
  | /* empty */            { [] }
  | program_item program_item_star { $1::$2 }
;
program_item:
  | fun_decl { $1 }
  | resource_decl {$1 }
;
fun_decl:
  | IDENT LPAREN formal_params RPAREN invariant LBRACE local_decls statement_star RBRACE invariant
      { Pfundecl($1,$3,$5,$7,$8,$10,Location.rhs_loc 10,Location.symbol_loc()) }
;
resource_decl:
  | RESOURCE IDENT LPAREN ident_seq RPAREN LBRACKET a_proposition RBRACKET
      { Presource($2,$4,$7,Location.symbol_loc()) }
;
ident_decl:
  | ident_seq SEMI { $1 }
;
ident_seq:
  | /* empty */      { [] }
  | ident_notempty_seq { $1 }
;
ident_notempty_seq:
  | IDENT            { [$1] }
  | IDENT COMMA ident_notempty_seq { $1::$3 }
;
local_decls:
  | /* empty */              { [] }
  | LOCAL ident_notempty_seq SEMI local_decls { $2 @ $4 }
;
statement_star:
  | /* empty */              { [] }
  | statement statement_star { $1::$2 }
;
statement:
  | IDENT EQUAL expression SEMI
	  { mkstm(Pstm_assign($1, $3)) }
  | IDENT EQUAL expression MINUSGREATER IDENT SEMI
	  { mkstm(Pstm_fldlookup($1, $3, $5)) }
  | expression MINUSGREATER IDENT EQUAL expression SEMI
	  { mkstm(Pstm_fldassign($1, $3, $5)) }
  | IDENT EQUAL NEW LPAREN RPAREN SEMI
	  { mkstm(Pstm_new($1)) }
  | DISPOSE expression SEMI
          { mkstm(Pstm_dispose($2)) }
  | LBRACE statement_star RBRACE
	  { mkstm(Pstm_block($2)) }
  | IF LPAREN expression RPAREN statement %prec below_ELSE
	  { mkstm(Pstm_if($3, $5, mkstm_ghost(Pstm_block []))) }
  | IF LPAREN expression RPAREN statement ELSE statement
	  { mkstm(Pstm_if($3, $5, $7)) }
  | WHILE LPAREN expression RPAREN invariant statement
	  { mkstm(Pstm_while($5, $3, $6)) }
  | WITH IDENT WHEN LPAREN expression RPAREN statement
          { mkstm(Pstm_withres($2,$5,$7)) }
  | IDENT LPAREN actual_params RPAREN SEMI
          { mkstm(Pstm_fcall($1,$3)) }
  | IDENT LPAREN actual_params RPAREN
    BARBAR
    IDENT LPAREN actual_params RPAREN SEMI
          { mkstm(Pstm_parallel_fcall($1,$3,$6,$8)) }

;
invariant:
  | /* empty */
          { None }
  | LBRACKET a_proposition RBRACKET
          { Some $2 }
;
expression:
  | IDENT
	  { mkexp(Pexp_ident($1)) }
  | NAT
	  { mkexp(Pexp_num($1)) }
  | TT
          { mkexp(Pexp_infix("==", mkexp_ghost(Pexp_num(0)), mkexp_ghost(Pexp_num(0)))) }
  | FF
          { mkexp(Pexp_infix("!=", mkexp_ghost(Pexp_num(0)), mkexp_ghost(Pexp_num(0)))) }
  | LPAREN expression RPAREN
	  { $2 }
  | INFIXOP2 expression %prec unary_prefix
	  { mkexp(Pexp_prefix($1, $2)) }
  | expression AMPERAMPER expression
	  { mkexp(Pexp_infix("&&", $1, $3)) }
  | expression STAR expression
	  { mkexp(Pexp_infix("*", $1, $3)) }
  | expression XOR expression
	  { mkexp(Pexp_infix("^", $1, $3)) }
  | expression EQUALEQUAL expression
	  { mkexp(Pexp_infix("==", $1, $3)) }
  | expression BANGEQUAL expression
	  { mkexp(Pexp_infix("!=", $1, $3)) }
  | expression INFIXOP1 expression
	  { mkexp(Pexp_infix($2, $1, $3)) }
  | expression INFIXOP2 expression
	  { mkexp(Pexp_infix($2, $1, $3)) }
  | expression INFIXOP3 expression
	  { mkexp(Pexp_infix($2, $1, $3)) }
;
expression_seq:
  | /* empty */      { [] }
  | expression_notempty_seq { $1 }
;
expression_notempty_seq:
  | expression            { [$1] }
  | expression COMMA expression_notempty_seq { $1::$3 }
;
formal_params:
  | ident_seq { mk_formal_params ([],$1) (Location.symbol_loc()) }
  | ident_seq SEMI ident_seq { mk_formal_params ($1,$3) (Location.symbol_loc()) }
;
actual_params:
  | expression_seq { ([],$1) }
  | expression_seq SEMI expression_seq { (mk_ref_params $1 (Location.rhs_loc 1), $3) }
;
a_component_expression_seq:
  | /* empty */      { [] }
  | a_component_expression_notempty_seq { $1 }
;
a_component_expression_notempty_seq:
  | IDENT COLON a_expression            { [($1,$3)] }
  | IDENT COLON a_expression COMMA a_component_expression_notempty_seq { ($1,$3)::$5 }

a_space_pred:
  | LIST LPAREN IDENT SEMI a_expression RPAREN
	  { Aspred_list($3,$5) }
  | LIST LPAREN a_expression RPAREN
	  { Aspred_list(Config.list_link_tag, $3) }
  | LISTSEG LPAREN IDENT SEMI a_expression COMMA a_expression RPAREN
	  { Aspred_listseg($3,$5,$7) }
  | LISTSEG LPAREN a_expression COMMA a_expression RPAREN
	  { Aspred_listseg(Config.list_link_tag, $3, $5) }
  | DLSEG LPAREN IDENT SEMI IDENT SEMI a_expression COMMA a_expression COMMA a_expression COMMA a_expression RPAREN
	  { Aspred_dlseg(DL,$3,$7,$9,$5,$11,$13) }
  | DLSEG LPAREN a_expression COMMA a_expression COMMA a_expression COMMA a_expression RPAREN
	  { Aspred_dlseg(DL, Config.dl_Rlink_tag, $3, $5, Config.dl_Llink_tag,$7, $9) }
  | XLSEG LPAREN IDENT SEMI IDENT SEMI a_expression COMMA a_expression COMMA a_expression COMMA a_expression RPAREN
	  { Aspred_dlseg(XL,$3,$7,$9,$5,$11,$13) }
  | XLSEG LPAREN a_expression COMMA a_expression COMMA a_expression COMMA a_expression RPAREN
	  { Aspred_dlseg(XL, Config.dl_Llink_tag, $3, $5, Config.dl_Llink_tag,$7, $9) }
  | TREE LPAREN IDENT SEMI IDENT SEMI a_expression RPAREN
          { Aspred_tree($3,$5,$7) }
  | TREE LPAREN a_expression RPAREN
          { Aspred_tree(fst Config.tree_link_tags, snd Config.tree_link_tags,
			$3) }
  | EMPTY
          { Aspred_empty }
  | a_expression POINTSTO a_component_expression_seq
          { Aspred_pointsto($1,$3) }
  | a_expression POINTSTO a_expression
          { Aspred_pointsto($1,[(Config.list_link_tag, $3)]) }
  | a_expression POINTSTO a_expression COMMA a_expression
          { Aspred_pointsto($1,[(fst Config.tree_link_tags, $3);
				(snd Config.tree_link_tags, $5)]) }
;

a_proposition:
  | LPAREN a_proposition RPAREN
	  { $2 }
  | a_expression EQUALEQUAL a_expression
	  { Aprop_equal($1,$3) }
  | a_expression BANGEQUAL a_expression
	  { Aprop_not_equal($1,$3) }
  | FF
	  { Aprop_false }
  | a_proposition STAR a_proposition
          { Aprop_star($1,$3) }
  | IF a_proposition THEN a_proposition ELSE a_proposition
      { Aprop_ifthenelse($2,$4,$6) }
  | a_space_pred
          { Aprop_spred $1 }
;
a_expression:
  | LPAREN a_expression RPAREN            { $2 }
  | a_expression XOR a_expression         { Aexp_infix("^",$1,$3) }
  | IDENT                                 { Aexp_ident($1) }
  | QIDENT                                { Aexp_ident($1) }
  | NAT                                   { Aexp_num($1) }
;

%% (* trailer *)
