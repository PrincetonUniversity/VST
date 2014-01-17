Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Require Import MirrorShard.ReifySepExpr.
Require Import MirrorShard.ReifyExpr.
Local Open Scope logic.

Unset Ltac Debug.

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

Definition lseg_LS := lseg LS.

Definition lseg_LS_signature :=
Sep.PSig all_types (cons share_tv
                   (cons list_val_tv (cons val_tv (cons val_tv nil))))
(lseg_LS).

Definition predicates := (lseg_LS_signature :: nil).
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
sum_int_signature ::
nil.

Definition more_funcs2 rho contents sh i cts y :=
make_environ_signature rho ::
make_list_int_signature contents ::
make_share_signature sh ::
sum_int_signature :: 
make_int_signature i ::
make_list_int_signature cts ::
make_val_signature y ::
nil.


Definition rho_f := length functions.
Definition contents_f := S rho_f.
Definition sh_f := S contents_f.
Definition sum_int_f := S sh_f.
Definition i_f := S sum_int_f.
Definition cts_f := S i_f.
Definition y_f := S cts_f.

Definition rho_func := nullary_func rho_f.
Definition contents_func := nullary_func contents_f.
Definition sh_func := nullary_func sh_f.
Definition sum_int_func i1  := 
@Expr.Func all_types sum_int_f (i1  :: nil).
Definition i_func := nullary_func i_f.
Definition cts_func := nullary_func cts_f.
Definition y_func := nullary_func y_f.

(*Tactics for reifying derives and hypothesis *)

Lemma convert_inj : forall S Q, !!S && Q  = (!!S && emp) * Q.
intros.
apply pred_ext.
 entailer!. 
entailer!.
Qed.

(*When prepare_reify is finished, all !!s should be in the form
!!P && emp * ... so that they can be converted to SepExpr.Inj 
this tactic is likely incomplete*)

Ltac fold_seplog := 
fold VericSepLogic_Kernel.star VericSepLogic.star
VericSepLogic_Kernel.emp VericSepLogic.emp
VericSepLogic_Kernel.inj VericSepLogic.inj
VericSepLogic_Kernel.ex VericSepLogic.ex.

Ltac prepare_reify :=
autorewrite with gather_prop;
match goal with 
| [ |- !!?X && _ |-- !!?Y && _] => rewrite (convert_inj X); rewrite (convert_inj Y)
| [ |- !!?X && _ |-- _] => rewrite (convert_inj X)
| [ |- _ |-- _] => idtac
end;
fold_seplog.

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

Ltac abbreviate_goal :=
match goal with
[ |- goalD _ ?f ?p ?u _ _] => 
abbreviate f as funcs;
abbreviate p as preds;
abbreviate u as uenv
end.


Ltac finish_reify :=
match goal with 
[ |- @Sep.sexprD ?t ?f ?p ?e ?v ?le |-- Sep.sexprD ?f ?p ?e ?v ?re ] => 
  replace (Sep.sexprD f p e v le |-- Sep.sexprD f p e v re) with 
  (derivesD t f p e v (le, re)) by reflexivity end;
start_goalD;
rev_reify;
abbreviate_goal.

Ltac get_types :=
match goal with 
| [ H := ?X : (list Expr.type) |- _] => X
end.

Ltac clear_types :=
match goal with 
| [ H := ?X : (list Expr.type) |- _] => unfold H in *; clear H
end.

Ltac get_funcs t := 
match goal with
[ _ := ?X : list (Expr.signature t) |- _ ] => X end.

Ltac get_predicates t :=
match goal with
[ _ := ?X : list (Sep.predicate t) |- _] => X end.

Ltac get_uenv t := 
match goal with 
| [ _ := ?X : Expr.env t |- _ ] => X
| [ _ := ?X : list (sigT (Expr.tvarD t)) |- _ ] => X
| [ _ : _ |- _ ] => constr:(@nil (sigT (Expr.tvarD all_types)))
end.

Ltac replace_reify_e H v r :=
let types := get_types in
let funcs := get_funcs types in
let uenv := get_uenv types in
replace v with 
(force_Opt (@Expr.exprD types funcs uenv nil r Expr.tvProp)False) in H; [ | try reflexivity]. 

Ltac reflect_sexpr types evars :=
let reflect_sexpr' uvars funcs sfuncs s :=
constr:(Sep.sexprD types funcs sfuncs uvars evars s) in
reflect_sexpr'.

Ltac reify_assumption H r:=
match goal with
[ H : ?X |- _] => replace_reify_e H X r
end.

Ltac replace_reify_s e r :=
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in 
replace e with
(@Sep.sexprD types funcs preds uenv  nil r); [ | try reflexivity ].

Ltac replace_reify_s2 e funcs preds uenv r :=
let types := get_types in
replace e with
(@Sep.sexprD types funcs preds uenv  nil r); [ | try reflexivity ].

Module ReifySepM := ReifySepExpr VericSepLogic Sep.

Ltac reify_derives :=
prepare_reify;
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in
match goal with
[ |- ?ls |-- ?rs ] => 
ReifySepM.reify_sexpr is_const ls types funcs tt tt
preds uenv nil 
ltac:(fun uenv' funcs' preds' ls_r => 
ReifySepM.reify_sexpr is_const rs types funcs' tt tt
preds' uenv' nil ltac:(fun uenv'' funcs'' preds'' rs_r =>
replace_reify_s2 ls funcs'' preds'' uenv'' ls_r;
replace_reify_s2 rs funcs'' preds'' uenv'' rs_r)) 
end;
try finish_reify.

(*Tests for reifier*)
(*Note: The continuation k must return a TACTIC to be executed on completion, not a value*)

Ltac is_const e := 
match type of e with
| type => constr:(true)
| ident => constr:(true)
| _ => 
  match e with 
  | nil => constr:(true)
  | nullval => constr:(true)
  | _ => constr:(false)
  end
end.

Ltac id_this ex := assert (forall n, ex = n).

Lemma test_reify_expr : forall (rho:environ),
False. 
Proof.
intros.
reify_expr is_const (typed_true (tptr t_struct_list) (eval_id _t rho)) all_types functions
0 0  ltac:(fun a b c => id_this c).
Admitted.

Lemma test_reify_sexpr : forall (rho:environ) (contents : list int) (sh : share),
lseg_LS sh nil (eval_id _p rho) nullval * emp |-- emp.
Proof.
intros.
pose (types := all_types).
pose (funcs := functions).
pose (predicates := predicates).
reify_derives.
simpl.
Check goalD.
abbreviate_goal.
Admitted.

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

Definition lseg_func sh cts v1 v2 := @Sep.Func all_types lseg_p
(sh :: cts :: v1 :: v2 :: nil).

Definition lseg_func2 :=  lseg_func sh_func (map_vint_func contents_func)
eval_id_p nullval_c.

Definition left_side :=
(Sep.Star (Sep.Inj pure)
(Sep.Star lseg_func2 (Sep.Emp all_types))).

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
pose (functions := (functions ++ (more_funcs rho contents sh))).
pose (types := all_types).
pose (preds := sep_predicates ++ predicates).
reify_assumption H3 tc_environ_r.
reify_derives left_side right_side.
Admitted.

Definition typed_true_t :=
typed_true_func (c_type_const (tptr t_struct_list)) (eval_id_t).

Definition sub_int_val :=
vint_func (int_sub_func sum_int_contents 
(int_add_func i_func (sum_int_func cts_func))).

Definition field_at1 :=
field_at_func sh_func (c_type_const t_struct_list) 
(id_const _head) (vint_func i_func) eval_id_t.

Definition field_at2 :=
field_at_func sh_func (c_type_const t_struct_list) 
(id_const _tail) y_func eval_id_t.

Definition lseg_cts :=
lseg_func sh_func (map_vint_func cts_func) y_func nullval_c.

Definition left_side_sep :=
Sep.Star
(Sep.Star 
(Sep.Star
(Sep.Star field_at1 field_at2) lseg_cts) (Sep.Const all_types TT))
(Sep.Emp all_types) .

Definition left_side_pure :=
Sep.Inj
(and_func true_c (and_func typed_true_t (and_func (val_eq sub_int_val eval_id_s)  true_c))).

Definition left_side2 := Sep.Star left_side_pure left_side_sep.

Definition right_side2 :=
Sep.Star 
(Sep.Inj true_c)
(Sep.Star
   (field_at_func (Expr.UVar 0%nat) (c_type_const t_struct_list)
                 (id_const _head) (Expr.UVar 1%nat) (eval_id_t))
   (Sep.Const all_types (!!True))).

(*Only for next example. Probably an unfortunate necessity of doing 
this by hand*)
Ltac ugly_create_uenv := 
match goal with [ |- _ |-- _ && (field_at ?u1 _ _ ?u2 _ * !!True) ]=>
pose (uenv := existT (Expr.tvarD all_types) share_tv u1
:: existT (Expr.tvarD all_types) val_tv u2 :: nil)
end. 

Lemma example_2 : False.
evar (e1 : share).
evar (e2 : val).
assert ( forall (sh : share) (contents : list int) (i : int) 
     (cts : list int) (y : val) (t : name _t) (p : name _p) 
     (s : name _s) (h : name _h),
   PROP  ()
   LOCAL  (tc_environ Delta;
   `(typed_true (typeof (Etempvar _t (tptr t_struct_list))))
     (eval_expr (Etempvar _t (tptr t_struct_list)));
   `(eq (Vint (Int.sub (sum_int contents) (sum_int (i :: cts)))))
     (eval_id _s))
   SEP  (`(field_at sh t_struct_list _head (Vint i)) (eval_id _t);
   `(field_at sh t_struct_list _tail y) (eval_id _t);
   `(lseg LS sh (map Vint cts)) `y `nullval; TT)
   |-- local (tc_expr Delta (Etempvar _t (tptr t_struct_list))) &&
       (`(field_at e1 t_struct_list _head e2)
          (eval_expr (Etempvar _t (tptr t_struct_list))) * TT)).
unfold e1. unfold e2. clear e1 e2.
intros.
go_lower0.
pose (functions := (functions ++ (more_funcs2 rho contents sh i cts y))).
pose (types := all_types).
pose (preds := sep_predicates ++ predicates).
ugly_create_uenv.
reify_assumption H3 tc_environ_r.
reify_derives left_side2 right_side2.
Admitted.