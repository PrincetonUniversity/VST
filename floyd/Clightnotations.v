(* This file was prepared by Jason Gross, September 18, 2017.

It originally came from his repo BUT HAS BEEN EDITED BY HAND
 SINCE THEN.

https://gist.github.com/JasonGross/2c792768f8ca895351152b388f167440

It was autogenerated by a terrible, kludgy python script that does ad-hoc
parsing of `cfrontend/PrintClight.ml` and `cfrontend/PrintCsyntax.ml`, and 
translates a couple of functions (mainly `expr` and `print_stmt` and
`print_cases`, but it can be made to handle others) to Coq notations. 

There's a switch in the python script for if you want to drop compatibility 
with 8.6.1; Coq 8.7 introduces the ability to make use of multiple boxes in 
notations, which allows nicer printing of if-then-else statements (though we
still can't quite match OCaml's pp; 
see https://coq.inria.fr/bugs/show_bug.cgi?id=5737). 
Also, the parentheses are going to be all messed up, because Coq doesn't
(yet) let us override levels of identifiers used in the standard library (see al
so
https://github.com/coq/coq/pull/982#issuecomment-324617760), so I had
to make a post-hoc adjustment to the precedence and associativity levels of
some operators.
*)

Require Import Clightdefs.

Delimit Scope None_scope with None.
Delimit Scope C_scope with C.
Delimit Scope Z_scope with Z.
Delimit Scope camlfloat_of_coqfloat_scope with camlfloat_of_coqfloat.
Delimit Scope camlfloat_of_coqfloat32_scope with camlfloat_of_coqfloat32.
Delimit Scope int64_repr_scope with int64_repr.
Delimit Scope int_repr_scope with int_repr.
Delimit Scope expr_scope with expr.
Delimit Scope extern_atom_scope with extern_atom.
Delimit Scope name_of_external_scope with name_of_external.
Delimit Scope name_type_scope with name_type.
Delimit Scope positive_scope with positive.
Delimit Scope print_case_label_scope with print_case_label.
Delimit Scope print_cases_scope with print_cases.
Delimit Scope print_expr_list_true_scope with print_expr_list_true.
Delimit Scope print_stmt_for_scope with print_stmt_for.

Notation "x" := (Int.repr x%Z) (only printing, at level 10) : int_repr_scope.
Notation "x" := (Int64.repr x%Z) (only printing, at level 10) : int64_repr_scope.

Notation "({ s_val })" := s_val%C (only printing, right associativity, at level 26, s_val at level 27, format "({  s_val  })") : print_stmt_for_scope.
Notation "id = 'builtin' ef ( el );" := (Sbuiltin (Some id%positive) ef%name_of_external _ el%print_expr_list_true) (only printing, ef at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' id  =  '/' 'builtin'  ef '/' ( el ); ']'") : print_stmt_for_scope.
Notation "'builtin' ef ( el );" := (Sbuiltin None ef%name_of_external _ el%print_expr_list_true) (only printing, ef at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' 'builtin'  ef '/' ( el ); ']'") : print_stmt_for_scope.
Notation "id = e1 ( el )" := (Scall (Some id%positive) e1%expr el%print_expr_list_true) (only printing, e1 at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' id  =  '/' e1 '/' ( el ) ']'") : print_stmt_for_scope.
Notation "e1 ( el )" := (Scall None e1%expr el%print_expr_list_true) (only printing, el at level 26, right associativity, at level 26, format "'[hv  ' e1 '/' ( el ) ']'") : print_stmt_for_scope.
Notation "s1 , s2" := (Ssequence s1%print_stmt_for s2%print_stmt_for) (only printing, s2 at level 26, right associativity, at level 26, format "s1 ,  s2") : print_stmt_for_scope.
Notation "id = e2" := (Sset id%positive e2%expr) (only printing, format "id  =  e2", at level 70) : print_stmt_for_scope.
Notation "e1 = e2" := (Sassign e1%expr e2%expr) (only printing, format "e1  =  e2", at level 70) : print_stmt_for_scope.
Notation "/*nothing*/" := Sskip (only printing, format "/*nothing*/", at level 10) : print_stmt_for_scope.
Notation "'goto' lbl ;" := (Sgoto lbl%extern_atom) (only printing, lbl at level 26, left associativity, at level 26, format "'goto'  lbl ;") : C_scope.
Notation "lbl <: s1" := (Slabel lbl%extern_atom s1%C) (only printing, s1 at level 26, left associativity, at level 26, format "lbl <:  '/' s1") : C_scope.
(*Notation "lbl : s1" := (Slabel lbl%extern_atom s1%C) (only printing, s1 at level 26, right associativity, at level 26, format "lbl :  '/' s1") : C_scope.*)
Notation "return;" := (Sreturn None) (only printing, format "return;", at level 10) : C_scope.
Notation "'switch' ( e_val ) { cases }" := (Sswitch e_val%expr cases%print_cases) (only printing, cases at level 26, right associativity, at level 26, format "'[v' 'switch'  ( e_val )  {  '/  ' cases '/' } ']'") : C_scope.
Notation "continue;" := Scontinue (only printing, format "continue;", at level 10) : C_scope.
Notation "break;" := Sbreak (only printing, format "break;", at level 10) : C_scope.
Notation "'for' ( ; 1; s2 ) { s1 }" := (Sloop s1%C s2%print_stmt_for) (only printing, s2 at level 26, s1 at level 26, right associativity, at level 26, format "'[v' 'for'  ( ;  '/' 1;  '/' s2 )  {  '/  ' s1 '/' } ']'") : C_scope.
Notation "'while' (1) { s1 }" := (Sloop s1%C Sskip) (only printing, s1 at level 26, right associativity, at level 26, format "'[v' 'while'  (1)  {  '/  ' s1 '/' } ']'") : C_scope.
Notation "'if' ( e_val ) { s1 } 'else' { s2 }" := (Sifthenelse e_val%expr s1%C s2%C) (only printing, s1 at level 26, s2 at level 26, right associativity, at level 26, format "'[v' 'if'  ( e_val )  {  '/  ' s1 '/' }  'else'  {  '/  ' s2 '/' } ']'") : C_scope.
Notation "'if' (! e_val ) { s2 }" := (Sifthenelse e_val%expr Sskip s2%C) (only printing, s2 at level 26, right associativity, at level 26, format "'[v' 'if'  (!  e_val )  {  '/  ' s2 '/' } ']'") : C_scope.
Notation "'if' ( e_val ) { s1 }" := (Sifthenelse e_val%expr s1%C Sskip) (only printing, s1 at level 26, right associativity, at level 26, format "'[v' 'if'  ( e_val )  {  '/  ' s1 '/' } ']'") : C_scope.
Notation "s1 s2" := (Ssequence s1%C s2%C) (only printing, s2 at level 27, right associativity, at level 27, format "s1  '//' s2") : C_scope.
(*Notation "s1" := (Ssequence s1%C Sskip) (only printing, format "s1", at level 10) : C_scope.
Notation "s2" := (Ssequence Sskip s2%C) (only printing, format "s2", at level 10) : C_scope.
*)
Notation "id = 'builtin' ef ( el );" := (Sbuiltin (Some id%positive) ef%name_of_external _ el%print_expr_list_true) (only printing, ef at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' id  =  '/' 'builtin'  ef '/' ( el ); ']'") : C_scope.
Notation "'builtin' ef ( el );" := (Sbuiltin None ef%name_of_external _ el%print_expr_list_true) (only printing, ef at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' 'builtin'  ef '/' ( el ); ']'") : C_scope.
Notation "id = e1 ( el );" := (Scall (Some id%positive) e1%expr el%print_expr_list_true) (only printing, e1 at level 26, el at level 26, right associativity, at level 26, format "'[hv  ' id  =  '/' e1 '/' ( el ); ']'") : C_scope.
Notation "e1 ( el );" := (Scall None e1%expr el%print_expr_list_true) (only printing, el at level 26, right associativity, at level 26, format "'[hv  ' e1 '/' ( el ); ']'") : C_scope.
Notation "id = e2 ;" := (Sset id%positive e2%expr) (only printing, e2 at level 26, right associativity, at level 26, format "'[hv  ' id  =  '/' e2 ; ']'") : C_scope.
Notation "e1 = e2 ;" := (Sassign e1%expr e2%expr) (only printing, e2 at level 26, right associativity, at level 26, format "'[hv  ' e1  =  '/' e2 ; ']'") : C_scope.
Notation "/*skip*/;" := Sskip (only printing, format "/*skip*/;", at level 10) : C_scope.
Notation "'__alignof__(' ty )" := (Ealignof ty%name_type _) (only printing, ty at level 11, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' '__alignof__(' ty ) ']'") : expr_scope.
Notation "'sizeof(' ty )" := (Esizeof ty%name_type _) (only printing, ty at level 11, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' 'sizeof(' ty ) ']'") : expr_scope.
Notation "( ty ) a1" := (Ecast a1%expr ty%name_type) (only printing, ty at level 12, a1 at level 12, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 12, format "'[hv  ' ( ty )  a1 ']'") : expr_scope.
Notation "a1 < a2" := (Ebinop Olt a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' <  a2 ']'", at level 70) : expr_scope.
Notation "a1 > a2" := (Ebinop Ogt a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' >  a2 ']'", at level 70) : expr_scope.
Notation "a1 >= a2" := (Ebinop Oge a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' >=  a2 ']'", at level 70) : expr_scope.
Notation "a1 % a2" := (Ebinop Omod a1%expr a2%expr _) (only printing, a2 at level 12, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 13, format "'[hv  ' a1  '/' %  a2 ']'") : expr_scope.
Notation "a1 ^ a2" := (Ebinop Oxor a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' ^  a2 ']'", at level 30, right associativity) : expr_scope.
Notation "a1 - a2" := (Ebinop Osub a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' -  a2 ']'", at level 50, left associativity) : expr_scope.
Notation "a1 >> a2" := (Ebinop Oshr a1%expr a2%expr _) (only printing, a2 at level 14, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 15, format "'[hv  ' a1  '/' >>  a2 ']'") : expr_scope.
Notation "a1 <= a2" := (Ebinop Ole a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' <=  a2 ']'", at level 70) : expr_scope.
Notation "a1 | a2" := (Ebinop Oor a1%expr a2%expr _) (only printing, a2 at level 19, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 20, format "'[hv  ' a1  '/' |  a2 ']'") : expr_scope.
Notation "a1 / a2" := (Ebinop Odiv a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' /  a2 ']'", at level 40, left associativity) : expr_scope.
Notation "a1 << a2" := (Ebinop Oshl a1%expr a2%expr _) (only printing, a2 at level 14, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 15, format "'[hv  ' a1  '/' <<  a2 ']'") : expr_scope.
Notation "a1 & a2" := (Ebinop Oand a1%expr a2%expr _) (only printing, a2 at level 17, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 18, format "'[hv  ' a1  '/' &  a2 ']'") : expr_scope.
Notation "a1 != a2" := (Ebinop Cop.One a1%expr a2%expr _) (only printing, a2 at level 16, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 17, format "'[hv  ' a1  '/' !=  a2 ']'") : expr_scope.
Notation "a1 * a2" := (Ebinop Omul a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' *  a2 ']'", at level 40, left associativity) : expr_scope.
Notation "a1 == a2" := (Ebinop Oeq a1%expr a2%expr _) (only printing, a2 at level 16, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 17, format "'[hv  ' a1  '/' ==  a2 ']'") : expr_scope.
Notation "a1 + a2" := (Ebinop Oadd a1%expr a2%expr _) (only printing, format "'[hv  ' a1  '/' +  a2 ']'", at level 50, left associativity) : expr_scope.
Notation "& a1" := (Eaddrof a1%expr _) (only printing, a1 at level 11, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' & a1 ']'") : expr_scope.
Notation "'__builtin_fabs' a1" := (Eunop Oabsfloat a1%expr _) (only printing, a1 at level 11, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' '__builtin_fabs' a1 ']'") : expr_scope.
Notation "~ a1" := (Eunop Onotint a1%expr _) (only printing, format "'[hv  ' ~ a1 ']'", at level 75, right associativity) : expr_scope.
Notation "! a1" := (Eunop Onotbool a1%expr _) (only printing, format "'[hv  ' ! a1 ']'", at level 30, right associativity) : expr_scope.
Notation "- a1" := (Eunop Oneg a1%expr _) (only printing, format "'[hv  ' - a1 ']'", at level 35, right associativity) : expr_scope.
Notation "'__builtin_fabs(' a1 )" := (Eunop Oabsfloat a1%expr _) (only printing, a1 at level 24, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' '__builtin_fabs(' a1 ) ']'") : expr_scope.
Notation "n_val 'LL'" := (Econst_long n_val%int64_repr _) (only printing, no associativity, at level 10, format "'[hv  ' n_val 'LL' ']'") : expr_scope.
Notation "n_val 'LLU'" := (Econst_long n_val%int64_repr (Tlong Unsigned _)) (only printing, no associativity, at level 10, format "'[hv  ' n_val 'LLU' ']'") : expr_scope.
Notation "f_val 'f'" := (Econst_single f_val%camlfloat_of_coqfloat32 _) (only printing, no associativity, at level 10, format "'[hv  ' f_val 'f' ']'") : expr_scope.
Notation "f_val" := (Econst_float f_val%camlfloat_of_coqfloat _) (only printing, format "'[hv  ' f_val ']'", at level 10) : expr_scope.
Notation "n_val" := (Econst_int n_val%int_repr _) (only printing, format "'[hv  ' n_val ']'", at level 10) : expr_scope.
Notation "n_val 'U'" := (Econst_int n_val%int_repr (Tint I32 Unsigned _)) (only printing, no associativity, at level 10, format "'[hv  ' n_val 'U' ']'") : expr_scope.
Notation "a1 . f_val" := (Efield a1%expr f_val%extern_atom _) (only printing, left associativity (* XXX Is LtoR the same as left associativity in Coq? *), at level 10, format "'[hv  ' a1 . f_val ']'") : expr_scope.
Notation "* a1" := (Ederef a1%expr _) (only printing, a1 at level 11, right associativity (* XXX Is RtoL the same as right associativity in Coq? *), at level 11, format "'[hv  ' * a1 ']'") : expr_scope.
Notation "id" := (Etempvar id%positive _) (only printing, format "'[hv  ' id ']'", at level 10) : expr_scope.
Notation "id" := (Evar id%extern_atom _) (only printing, format "'[hv  ' id ']'", at level 10) : expr_scope.
Notation "lbl <: s_val rem" := (LScons lbl%print_case_label s_val%C rem%print_cases) (only printing, rem at level 26, left associativity, at level 26, format "'[v  ' lbl <:  '/' s_val ']'  '/' rem") : print_cases_scope.
(*Notation "lbl : s_val rem" := (LScons lbl%print_case_label s_val%C rem%print_cases) (only printing, rem at level 26, right associativity, at level 26, format "'[v  ' lbl :  '/' s_val ']'  '/' rem") : print_cases_scope.*)
Notation "lbl <: rem" := (LScons lbl%print_case_label Sskip rem%print_cases) (only printing, rem at level 26, left associativity, at level 26, format "lbl <:  '/' rem") : print_cases_scope.
(*Notation "lbl : rem" := (LScons lbl%print_case_label Sskip rem%print_cases) (only printing, rem at level 26, right associativity, at level 26, format "lbl :  '/' rem") : print_cases_scope.*)
Notation "" := LSnil (only printing, left associativity, at level 26, format "") : print_cases_scope.
Notation "'case' lbl" := (Some lbl%Z) (only printing, lbl at level 26, left associativity, at level 26, format "'case'  lbl") : print_case_label_scope.
Notation "'default'" := None (only printing, format "'default'", at level 10) : print_case_label_scope.

Notation "p_val -> f_val" := (Efield (Ederef p_val%expr _) f_val%extern_atom _) (only printing, right associativity, at level 99, f_val at level 200, format "p_val -> f_val") : expr_scope.
Notation "p_val [ i_val ]" := (Ederef (Ebinop Oadd p_val%expr i_val%expr _) _) (only printing, left associativity, at level 26, format "p_val [ i_val ]") : expr_scope.
Notation "x , .. , y" := (@cons expr x%expr .. (@cons expr y%expr (@nil expr)) .. ) (only printing, at level 26, x at level 24, y at level 24) : print_expr_list_true_scope.
Notation "'while' ( e_val ) { s1 }" := (Swhile e_val%expr s1%C) (only printing, s1 at level 26, left associativity, at level 26, format "'[v' 'while'  ( e_val )  {  '/  ' s1 '/' } ']'") : C_scope.

Undelimit Scope camlfloat_of_coqfloat_scope.
Undelimit Scope camlfloat_of_coqfloat32_scope.
Undelimit Scope int64_repr_scope.
Undelimit Scope int_repr_scope.
Undelimit Scope extern_atom_scope.
Undelimit Scope name_of_external_scope.
Undelimit Scope name_type_scope.
Undelimit Scope print_case_label_scope.
Undelimit Scope print_cases_scope.
Undelimit Scope print_expr_list_true_scope.
Undelimit Scope print_stmt_for_scope.

(*Global Open Scope expr_scope.*)
(*Global Open Scope C_scope. *)

(*Open Scope C_scope.
Check (Ssequence Sskip (Ssequence Sskip Sskip)).
Check (Ssequence (Ssequence Sskip Sskip) Sskip).
*)
