Require Import Clightdefs.

Delimit Scope None_scope with None.
Delimit Scope Z_scope with Z.
Delimit Scope camlfloat_of_coqfloat_scope with camlfloat_of_coqfloat.
Delimit Scope camlfloat_of_coqfloat32_scope with camlfloat_of_coqfloat32.
Delimit Scope camlint64_of_coqint_scope with camlint64_of_coqint.
Delimit Scope camlint_of_coqint_scope with camlint_of_coqint.
Delimit Scope expr_scope with expr.
Delimit Scope extern_atom_scope with extern_atom.
Delimit Scope name_of_external_scope with name_of_external.
Delimit Scope name_type_scope with name_type.
Delimit Scope positive_scope with positive.
Delimit Scope print_case_label_scope with print_case_label.
Delimit Scope print_cases_scope with print_cases.
Delimit Scope expr_scope with expr.
Delimit Scope print_expr_list_true_scope with print_expr_list_true.
Delimit Scope print_stmt_scope with C.
Delimit Scope print_stmt_for_scope with print_stmt_for.

Notation "x" := (Int.repr x%Z) (only printing, at level 10) : expr_scope.

Notation "'goto' lbl ;" := (Sgoto lbl%extern_atom) (only printing, left associativity, at level 10, lbl at level 10, format "'goto'  lbl ;") : print_stmt_scope.
Notation "lbl : s1" := (Slabel lbl%extern_atom s1%C) (only printing, left associativity, at level 10, s1 at level 10, format "lbl :  '/' s1") : print_stmt_scope.
Notation "'return' e_val ;" := (Sreturn (Some e_val%expr)) (only printing, left associativity, at level 10, format "'return'  e_val ;") : print_stmt_scope.
Notation "return;" := (Sreturn None) (only printing, left associativity, at level 10, format "return;") : print_stmt_scope.
Notation "'switch' ( e_val ) { cases }" := (Sswitch e_val%expr cases%print_cases) (only printing, left associativity, at level 10, cases at level 10, format "'[v  ' 'switch'  ( e_val )  {  '//' cases '//' } ']'") : print_stmt_scope.
Notation "continue;" := Scontinue (only printing, left associativity, at level 10, format "continue;") : print_stmt_scope.
Notation "break;" := Sbreak (only printing, left associativity, at level 10, format "break;") : print_stmt_scope.
Notation "'for' ( ; 1; s2 ) { s1 }" := (Sloop s1%C s2%print_stmt_for) (only printing, left associativity, at level 10, s2 at level 10, s1 at level 10, format "'[v  ' 'for'  ( ;  '//' 1;  '//' s2 )  {  '//' s1 '//' } ']'") : print_stmt_scope.
Notation "'while' (1) { s1 }" := (Sloop s1%C Sskip) (only printing, left associativity, at level 10, s1 at level 10, format "'[v  ' 'while'  (1)  {  '//' s1 '//' } ']'") : print_stmt_scope.
Notation "'if' ( e_val ) { s1 } 'else' { s2 }" := (Sifthenelse e_val%expr s1%C s2%C) (only printing, left associativity, at level 10, s1 at level 10, s2 at level 10, format "'[v  ' 'if'  ( e_val )  {  '//' s1 '//' }  'else'  {  '//' s2 '//' } ']'") : print_stmt_scope.
Notation "'if' (! e_val ) { s2 }" := (Sifthenelse e_val%expr Sskip s2%C) (only printing, left associativity, at level 10, s2 at level 10, format "'[v  ' 'if'  (!  e_val )  {  '//' s2 '//' } ']'") : print_stmt_scope.
Notation "'if' ( e_val ) { s1 }" := (Sifthenelse e_val%expr s1%C Sskip) (only printing, left associativity, at level 10, s1 at level 10, format "'[v  ' 'if'  ( e_val )  {  '//' s1 '//' } ']'") : print_stmt_scope.
Notation "s1 s2" := (Ssequence s1%C s2%C) (only printing, left associativity, at level 10, s2 at level 10, format "s1  '/' s2") : print_stmt_scope.
Notation "s1" := (Ssequence s1%C Sskip) (only printing, left associativity, at level 10, format "s1") : print_stmt_scope.
Notation "s2" := (Ssequence Sskip s2%C) (only printing, left associativity, at level 10, format "s2") : print_stmt_scope.
Notation "$ id = 'builtin' ef ( el );" := (Sbuiltin (Some id%positive) ef%name_of_external _ el%print_expr_list_true) (only printing, left associativity, at level 10, id at level 10, ef at level 10, el at level 10, format "'[hv  ' $ id  =  '/' 'builtin'  ef '/' ( el ); ']'") : print_stmt_scope.
Notation "'builtin' ef ( el );" := (Sbuiltin None ef%name_of_external _ el%print_expr_list_true) (only printing, left associativity, at level 10, ef at level 10, el at level 10, format "'[hv  ' 'builtin'  ef '/' ( el ); ']'") : print_stmt_scope.
Notation "$ id = e1 ( el );" := (Scall (Some id%positive) e1%expr el%print_expr_list_true) (only printing, left associativity, at level 10, id at level 10, e1 at level 10, el at level 10, format "'[hv  ' $ id  =  '/' e1 '/' ( el ); ']'") : print_stmt_scope.
Notation "e1 ( el );" := (Scall None e1%expr el%print_expr_list_true) (only printing, left associativity, at level 10, el at level 10, format "'[hv  ' e1 '/' ( el ); ']'") : print_stmt_scope.
Notation "$ id = e2 ;" := (Sset id%positive e2%expr) (only printing, left associativity, at level 10, id at level 10, e2 at level 10, format "'[hv  ' $ id  =  '/' e2 ; ']'") : print_stmt_scope.
Notation "e1 = e2 ;" := (Sassign e1%expr e2%expr) (only printing, left associativity, at level 10, e2 at level 10, format "'[hv  ' e1  =  '/' e2 ; ']'") : print_stmt_scope.
Notation "/*skip*/;" := Sskip (only printing, left associativity, at level 10, format "/*skip*/;") : print_stmt_scope.
Notation "'__alignof__(' ty )" := (Ealignof ty%name_type _) (only printing, left associativity, at level 10, ty at level 10, format "'__alignof__(' ty )") : expr_scope.
Notation "'sizeof(' ty )" := (Esizeof ty%name_type _) (only printing, left associativity, at level 10, ty at level 10, format "'sizeof(' ty )") : expr_scope.
Notation "( ty ) a1" := (Ecast a1%expr ty%name_type) (only printing, left associativity, at level 10, ty at level 10, a1 at level 14, format "( ty )  a1") : expr_scope.
Notation "a1 < a2" := (Ebinop Olt a1%expr a2%expr _) (only printing, format "a1  '/' <  a2", at level 70) : expr_scope.
Notation "a1 > a2" := (Ebinop Ogt a1%expr a2%expr _) (only printing, format "a1  '/' >  a2", at level 70) : expr_scope.
Notation "a1 >= a2" := (Ebinop Oge a1%expr a2%expr _) (only printing, format "a1  '/' >=  a2", at level 70) : expr_scope.
Notation "a1 % a2" := (Ebinop Omod a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 14, format "a1  '/' %  a2") : expr_scope.
Notation "a1 ^ a2" := (Ebinop Oxor a1%expr a2%expr _) (only printing, format "a1  '/' ^  a2", at level 30, right associativity) : expr_scope.
Notation "a1 - a2" := (Ebinop Osub a1%expr a2%expr _) (only printing, format "a1  '/' -  a2", at level 50, left associativity) : expr_scope.
Notation "a1 >> a2" := (Ebinop Oshr a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 12, format "a1  '/' >>  a2") : expr_scope.
Notation "a1 <= a2" := (Ebinop Ole a1%expr a2%expr _) (only printing, format "a1  '/' <=  a2", at level 70) : expr_scope.
Notation "a1 | a2" := (Ebinop Oor a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 7, format "a1  '/' |  a2") : expr_scope.
Notation "a1 / a2" := (Ebinop Odiv a1%expr a2%expr _) (only printing, format "a1  '/' /  a2", at level 40, left associativity) : expr_scope.
Notation "a1 << a2" := (Ebinop Oshl a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 12, format "a1  '/' <<  a2") : expr_scope.
Notation "a1 & a2" := (Ebinop Oand a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 9, format "a1  '/' &  a2") : expr_scope.
Notation "a1 != a2" := (Ebinop Cop.One a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 10, format "a1  '/' !=  a2") : expr_scope.
Notation "a1 * a2" := (Ebinop Omul a1%expr a2%expr _) (only printing, format "a1  '/' *  a2", at level 40, left associativity) : expr_scope.
Notation "a1 == a2" := (Ebinop Oeq a1%expr a2%expr _) (only printing, left associativity, at level 10, a2 at level 10, format "a1  '/' ==  a2") : expr_scope.
Notation "a1 + a2" := (Ebinop Oadd a1%expr a2%expr _) (only printing, format "a1  '/' +  a2", at level 50, left associativity) : expr_scope.
Notation "& a1" := (Eaddrof a1%expr _) (only printing, left associativity, at level 10, a1 at level 15, format "& a1") : expr_scope.
Notation "'__builtin_fabs' a1" := (Eunop Oabsfloat a1%expr _) (only printing, left associativity, at level 10, a1 at level 15, format "'__builtin_fabs' a1") : expr_scope.
Notation "~ a1" := (Eunop Onotint a1%expr _) (only printing, format "~ a1", at level 75, right associativity) : expr_scope.
Notation "! a1" := (Eunop Onotbool a1%expr _) (only printing, format "! a1", at level 30, right associativity) : expr_scope.
Notation "- a1" := (Eunop Oneg a1%expr _) (only printing, format "- a1", at level 35, right associativity) : expr_scope.
Notation "'__builtin_fabs(' a1 )" := (Eunop Oabsfloat a1%expr _) (only printing, left associativity, at level 10, a1 at level 2, format "'__builtin_fabs(' a1 )") : expr_scope.
Notation "n_val 'LL'" := (Econst_long n_val%camlint64_of_coqint _) (only printing, left associativity, at level 10, format "n_val 'LL'") : expr_scope.
Notation "n_val 'LLU'" := (Econst_long n_val%camlint64_of_coqint (Tlong Unsigned _)) (only printing, left associativity, at level 10, format "n_val 'LLU'") : expr_scope.
Notation "f_val 'f'" := (Econst_single f_val%camlfloat_of_coqfloat32 _) (only printing, left associativity, at level 10, format "f_val 'f'") : expr_scope.
Notation "f_val" := (Econst_float f_val%camlfloat_of_coqfloat _) (only printing, left associativity, at level 10, format "f_val") : expr_scope.
Notation "n_val" := (Econst_int n_val%camlint_of_coqint _) (only printing, left associativity, at level 10, format "n_val") : expr_scope.
Notation "n_val 'U'" := (Econst_int n_val%camlint_of_coqint (Tint I32 Unsigned _)) (only printing, left associativity, at level 10, format "n_val 'U'") : expr_scope.
Notation "a1 . f_val" := (Efield a1%expr f_val%extern_atom _) (only printing, left associativity, at level 10, format "a1 . f_val") : expr_scope.
Notation "* a1" := (Ederef a1%expr _) (only printing, left associativity, at level 10, a1 at level 15, format "* a1") : expr_scope.
Notation "$ id" := (Etempvar id%positive _) (only printing, left associativity, at level 10, id at level 10, format "$ id") : expr_scope.
Notation "id" := (Evar id%extern_atom _) (only printing, left associativity, at level 10, format "id") : expr_scope.
Notation "lbl : s_val rem" := (LScons lbl%print_case_label s_val%C rem%print_cases) (only printing, left associativity, at level 10, rem at level 10, format "'[v  ' lbl :  '/' s_val ']'  '/' rem") : print_cases_scope.
Notation "lbl : rem" := (LScons lbl%print_case_label Sskip rem%print_cases) (only printing, left associativity, at level 10, rem at level 10, format "lbl :  '/' rem") : print_cases_scope.
Notation "" := LSnil (only printing, left associativity, at level 10, format "") : print_cases_scope.
Notation "'case' lbl" := (Some lbl%Z) (only printing, left associativity, at level 10, lbl at level 10, format "'case'  lbl") : print_case_label_scope.
Notation "'default'" := None (only printing, left associativity, at level 10, format "'default'") : print_case_label_scope.
