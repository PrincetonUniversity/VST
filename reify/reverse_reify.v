Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Local Open Scope logic.


(*Some definitions needed from the example file (verif_reverse.v) *)
Instance LS: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition sum_int := fold_right Int.add Int.zero.

Definition Delta := 
(PTree.Node
         (PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                     PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                  PTree.Leaf))) None
         (PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)
                  None PTree.Leaf) None PTree.Leaf) None
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf))),
      var_types
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_list, false))
                       PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                    PTree.Leaf))) None
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)
                    None PTree.Leaf) None PTree.Leaf) None
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf))),
        var_types
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some (tptr t_struct_list, false)) PTree.Leaf) None
                      PTree.Leaf) None PTree.Leaf) None
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                      PTree.Leaf))) None
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)
                      None PTree.Leaf) None PTree.Leaf) None
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf))),
          PTree.empty type, tint,
          PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tptr tvoid), 
                            (3%positive, tuint), (4%positive, tuint)]
                            (fun _ : environ => !!False) POST  [tvoid]
                            (fun _ : environ => !!False)))) PTree.Leaf) None
                  PTree.Leaf) None
               (PTree.Node
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH x : share * list int PRE 
                               [(_p, tptr t_struct_list)]
                               (let (sh0, contents0) := x in
                                `(lseg LS sh0 (map Vint contents0))
                                  (eval_id _p) `nullval) POST  [tint]
                               (let (_, contents0) := x in
                                local
                                  (`(eq (Vint (sum_int contents0))) retval)))))
                        PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tschar),
                            (2%positive, tint)](fun _ : environ => !!False)
                            POST  [tint](fun _ : environ => !!False))))
                     PTree.Leaf) None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH  sh0 : share, contents0 : 
                               list val PRE  [(_p, tptr t_struct_list)]
                               (fun x0 : environ =>
                                !!writable_share sh0 &&
                                `(lseg LS sh0 contents0) 
                                  (eval_id _p) `nullval x0) POST 
                               [tptr t_struct_list]
                               `(lseg LS sh0 (rev contents0)) retval `nullval)))
                        PTree.Leaf)
                     (Some (Global_var (Tarray t_struct_list 3 noattr)))
                     PTree.Leaf)) None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tdouble)]
                         (fun _ : environ => !!False) POST  [tdouble]
                         (fun _ : environ => !!False))))
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH u : unit PRE  []
                               main_pre prog u POST  [tint]
                               main_post prog u))) PTree.Leaf) None
                     PTree.Leaf)))), tint,
        PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tptr tvoid), 
                          (3%positive, tuint), (4%positive, tuint)]
                          (fun _ : environ => !!False) POST  [tvoid]
                          (fun _ : environ => !!False)))) PTree.Leaf) None
                PTree.Leaf) None
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH x : share * list int PRE 
                             [(_p, tptr t_struct_list)]
                             (let (sh0, contents0) := x in
                              `(lseg LS sh0 (map Vint contents0))
                                (eval_id _p) `nullval) POST  [tint]
                             (let (_, contents0) := x in
                              local (`(eq (Vint (sum_int contents0))) retval)))))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tschar),
                          (2%positive, tint)](fun _ : environ => !!False)
                          POST  [tint](fun _ : environ => !!False))))
                   PTree.Leaf) None
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  sh0 : share, contents0 : 
                             list val PRE  [(_p, tptr t_struct_list)]
                             (fun x0 : environ =>
                              !!writable_share sh0 &&
                              `(lseg LS sh0 contents0) 
                                (eval_id _p) `nullval x0) POST 
                             [tptr t_struct_list]
                             `(lseg LS sh0 (rev contents0)) retval `nullval)))
                      PTree.Leaf)
                   (Some (Global_var (Tarray t_struct_list 3 noattr)))
                   PTree.Leaf)) None
             (PTree.Node PTree.Leaf
                (Some
                   (Global_func
                      (WITH _ : unit PRE  [(1%positive, tdouble)]
                       (fun _ : environ => !!False) POST  [tdouble]
                       (fun _ : environ => !!False))))
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH u : unit PRE  []main_pre prog u POST 
                             [tint]main_post prog u))) PTree.Leaf) None
                   PTree.Leaf)))), tint,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 PTree.Leaf) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH x : share * list int PRE 
                           [(_p, tptr t_struct_list)]
                           (let (sh0, contents0) := x in
                            `(lseg LS sh0 (map Vint contents0)) 
                              (eval_id _p) `nullval) POST  [tint]
                           (let (_, contents0) := x in
                            local (`(eq (Vint (sum_int contents0))) retval)))))
                    PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False)))) PTree.Leaf)
              None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  sh0 : share, contents0 : 
                           list val PRE  [(_p, tptr t_struct_list)]
                           (fun x0 : environ =>
                            !!writable_share sh0 &&
                            `(lseg LS sh0 contents0) (eval_id _p) `nullval x0)
                           POST  [tptr t_struct_list]
                           `(lseg LS sh0 (rev contents0)) retval `nullval)))
                    PTree.Leaf)
                 (Some (Global_var (Tarray t_struct_list 3 noattr)))
                 PTree.Leaf)) None
           (PTree.Node PTree.Leaf
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf) None PTree.Leaf)))).


(*types we need that aren't defined yet... 
this is just an example, we don't really need this one*)
Definition LS_type := cons (no_eqb_type (listspec t_struct_list _tail)) nil.

Module uk_types <: unknown_types.
Definition unknown_types := LS_type.
End uk_types.

Module funcs := funcs uk_types.
Import funcs.
Import all_types.

Definition list_spec_tv := Expr.tvType (length our_types).


(*Separation logic predicate just for this file *)

Definition lseg_signature :=
Sep.PSig all_types (cons share_tv
                   (cons list_val_tv (cons val_tv (cons val_tv nil))))
(lseg LS).

Definition predicates := lseg_signature :: nil.
Definition lseg_p := length sep_predicates.

(*Functions just for this file. These three represent variables
  that are above the line. *)

Definition sum_int_signature :=
Expr.Sig all_types (list_int_tv :: nil)
int_tv sum_int.


Definition more_funcs rho contents sh :=
make_environ_signature rho ::
make_list_int_signature contents ::
make_share_signature sh ::
sum_int_signature :: nil.


Definition rho_f := length functions.
Definition contents_f := S rho_f.
Definition sh_f := S contents_f.
Definition sum_int_f := S sh_f.

Definition rho_func := nullary_func rho_f.
Definition contents_func := nullary_func contents_f.
Definition sh_func := nullary_func sh_f.
Definition sum_int_func i1  := 
@Expr.Func all_types sum_int_f (i1  :: nil).

(*Some constants we will use *)

Definition true_c := prop_const True.
Definition zero_c := val_const (Vint (Int.repr 0)).
Definition _p_c := id_const _p.
Definition _t_c := id_const _t.
Definition _s_c := id_const _s.
Definition nullval_c := val_const nullval.
Definition delta_c := tycontext_const Delta.

(*Put it together with functions and stars *)
Definition eval_id_p := eval_id_func _p_c rho_func.
Definition eval_id_t := eval_id_func _t_c rho_func.
Definition eval_id_s := eval_id_func _s_c rho_func.
Definition eq1 := val_eq eval_id_t eval_id_p.
Definition eq2 := val_eq eval_id_s zero_c.


Definition pure := and_func true_c (and_func eq1 (and_func eq2 true_c)).

Definition lseg_func := @Sep.Func all_types lseg_p
(sh_func :: (map_vint_func contents_func) :: eval_id_p :: nullval_c :: nil).

Definition left_side :=
(Sep.Star (Sep.Inj pure)
(Sep.Star lseg_func (Sep.Emp all_types))).

Definition sum_int_contents :=
sum_int_func (contents_func).

Definition sub_val := 
vint_func (int_sub_func sum_int_contents sum_int_contents).

Definition eq_s_sub :=
val_eq sub_val eval_id_s.

Definition pure_r :=
and_func true_c (and_func eq_s_sub true_c).

Definition lseg_r := 
@Sep.Func all_types lseg_p (sh_func :: (map_vint_func contents_func) :: eval_id_t :: nullval_c :: nil).
 
Definition sep_r := Sep.Star (Sep.Star (Sep.Const all_types (!!True)) lseg_r) (Sep.Emp all_types).

Definition right_side := 
Sep.Star (Sep.Inj pure_r)
sep_r.

Definition tc_environ_r := 
tc_environ_func delta_c rho_func.


Ltac unfold_VericSepLogic := simpl; unfold VericSepLogic.star, 
VericSepLogic.inj, VericSepLogic.emp.

Lemma convert_inj : forall S Q, !!S && Q  = (!!S && emp) * Q.
intros.
apply pred_ext.
 entailer!. 
entailer!.
Qed.

(*When prepare_reify is finished, all !!s should be in the form
!!P && emp * ... so that they can be converted to SepExpr.Inj 
this tactic is likely incomplete*)
Ltac prepare_reify :=
autorewrite with gather_prop;
match goal with 
| [ |- !!?X && _ |-- !!?Y && _] => rewrite (convert_inj X); rewrite (convert_inj Y)
| [ |- !!?X && _ |-- _] => rewrite (convert_inj X)
end.

(*Turns a reified derives into a reified goal with no assumptions, 
sort of a base case for rev_reify *)
Ltac start_goalD :=
match goal with 
[ |- derivesD ?t ?f ?p ?e ?v ?d] => 
replace (derivesD t f p e v d) with (goalD t f p e v (nil, d)) by reflexivity
end.

(*Pulls down any reified assumptions and puts them into 
a goal *)
Ltac rev_reify :=
repeat match goal with
| [ H : force_Opt (Expr.exprD ?f ?e ?v ?P ?ty) False |- goalD ?t ?f ?p ?e ?v (?l, ?d) ] => revert H; 
replace (force_Opt (Expr.exprD f e v P ty) False ->
goalD t f p e v (l, d)) with
(goalD t f p e v (P::l, d)) by reflexivity
end.

Ltac finish_reify :=
match goal with 
[ |- @Sep.sexprD ?t ?f ?p ?e ?v ?le |-- Sep.sexprD ?f ?p ?e ?v ?re ] => 
  replace (Sep.sexprD f p e v le |-- Sep.sexprD f p e v re) with 
  (derivesD t f p e v (le, re)) by reflexivity end;
start_goalD;
rev_reify.


Lemma while_entail1 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
   PROP  ()
   LOCAL 
   (tc_environ
      Delta;
   `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list))
);
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
   SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
   |-- PROP  ()
       LOCAL 
       (`(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
          (eval_id _s))
       SEP  (TT; `(lseg LS sh (map Vint contents)) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
prepare_reify.

replace
(!!(True /\
      eval_id _t rho = eval_id _p rho /\
      eval_id _s rho = Vint (Int.repr 0) /\ True) && emp *
   (lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp))
with
(@Sep.sexprD all_types (functions ++ (more_funcs rho contents sh))  
predicates nil nil (left_side)) by reflexivity.

replace
(!!(True /\
          Vint (Int.sub (sum_int contents) (sum_int contents)) =
          eval_id _s rho /\ True) && emp *
       (!!True * lseg LS sh (map Vint contents) (eval_id _t rho) nullval * emp))
with
(@Sep.sexprD all_types (functions ++ (more_funcs rho contents sh))
predicates nil nil (right_side)) by reflexivity.

replace 
(tc_environ Delta rho) with 
(force_Opt (@Expr.exprD all_types (functions ++ (more_funcs rho contents sh)) nil nil tc_environ_r Expr.tvProp)False) in H3 by reflexivity.
finish_reify.

Admitted.