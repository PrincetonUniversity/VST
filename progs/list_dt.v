(* Require Import floyd.proofauto.
   TEMPORARILY replace "floyd.proofauto" 
   with all the imports in the list below.
   This reduces makefile-based recompilation
   when changing things in (e.g.) forward.v
*)
Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.nested_loadstore.
(*Require Import floyd.unfold_data_at.*)
Require Import floyd.entailer.
(*  End TEMPORARILY *)

Lemma ptr_eq_refl: forall x, isptr x -> ptr_eq x x.
Proof.
destruct x; simpl; intros; try contradiction.
split; auto. apply Int.eq_true.
Qed.

Lemma allp_andp1  {A}{ND: NatDed A}:  forall B (any: B) (p: B -> A) q, andp (allp p) q = (allp (fun x => andp (p x) q)).
Proof.
 intros. apply pred_ext.
 apply allp_right; intro x.
 apply andp_derives; auto. apply allp_left with x; auto.
 apply andp_right. apply allp_right; intro x. apply allp_left with x. apply andp_left1; auto.
 apply allp_left with any. apply andp_left2; auto.
Qed.

Lemma allp_andp2  {A}{ND: NatDed A}:  forall B (any: B) p (q: B -> A), 
     andp p (allp q) = (allp (fun x => andp p (q x))).
Proof.
intros. rewrite andp_comm. rewrite allp_andp1; auto.
f_equal. extensionality x. rewrite andp_comm; auto.
Qed.

Local Open Scope logic.

Class listspec {cs: compspecs} {csl: compspecs_legal cs} (list_structid: ident) (list_link: ident) :=
  mk_listspec {  
   list_fields: members;
   list_struct := Tstruct list_structid noattr;
   list_members_eq: list_fields = co_members (get_co list_structid);
   list_struct_alignas_legal: legal_alignas_type list_struct = true;
   list_link_type: nested_field_type2 list_struct (StructField list_link :: nil) = Tpointer list_struct noattr
}.

Section LIST1.
Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.
Context  {list_structid: ident} {list_link: ident}.

Fixpoint all_but_link (f: members) : members :=
 match f with
 | nil => nil
 | cons (i, t) f' => if ident_eq i list_link
                               then f' 
                               else cons (i, t) (all_but_link f')
 end.

Lemma list_link_size_in_range (ls: listspec list_structid list_link):  
  0 < sizeof cenv_cs (nested_field_type2 list_struct (StructField list_link :: nil)) < Int.modulus.
Proof.
  rewrite list_link_type.
  cbv.
  split; reflexivity.
Qed.

Definition elemtype (ls: listspec list_structid list_link) :=
  compact_prod
  (map (fun it => reptype (field_type (fst it) list_fields)) (all_but_link list_fields)).
 
Definition add_link_back {ls: listspec list_structid list_link} {f F: members}
  (v: compact_prod (map (fun it => reptype (field_type (fst it) F)) (all_but_link f))) :
  compact_prod (map (fun it => reptype (field_type (fst it) F)) f).
  unfold all_but_link in v.
  induction f as [| [i0 t0] f].
  + exact tt.
  + simpl in *; destruct f as [| [i1 t1] f0] eqn:?; [| destruct (ident_eq i0 list_link)].
    - exact (default_val _).
    - exact (default_val _, v).
    - fold (all_but_link ((i1, t1) :: f0)) in IHf, v.
      destruct (all_but_link ((i1, t1) :: f0)) eqn:?.
      * simpl in Heqm. 
        if_tac in Heqm; [| congruence].
        subst f0.
        exact (v, default_val _).
      * exact (fst v, IHf (snd v)).
Defined.

Definition list_data {ls: listspec list_structid list_link} (v: elemtype ls): reptype list_struct.
  unfold list_struct.
  pose (add_link_back v: reptype_structlist _).
  rewrite list_members_eq in r.
  exact (@fold_reptype _ _ (Tstruct _ _) r).
Defined.

Definition maybe_data_at (ls: listspec list_structid list_link) (sh: share) (v: elemtype ls) (p: val) : mpred :=
  if readable_share_dec sh
  then data_at sh list_struct (list_data v) p
  else memory_block sh (sizeof cenv_cs list_struct) p.

Definition list_cell (ls: listspec list_structid list_link) sh v p :=
  (field_at_ sh list_struct (StructField list_link :: nil) p) -* (maybe_data_at ls sh v p).
End LIST1.

Module LsegGeneral.

Section LIST2.
Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.
Context  {list_structid: ident} {list_link: ident}.

Fixpoint lseg (ls: listspec list_structid list_link) (dsh psh: share) 
            (contents: list (val * elemtype ls)) (x z: val) : mpred :=
 match contents with
 | (p,h)::hs => !! (p=x /\ ~ptr_eq x z) && 
              EX y:val,  !! is_pointer_or_null y &&
               list_cell ls dsh h x 
              * field_at psh list_struct (StructField list_link ::nil)
                  (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x 
              * lseg ls dsh psh hs y z
 | nil => !! (ptr_eq x z) && emp
 end.

Lemma lseg_unfold (ls: listspec list_structid list_link): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 = 
     match contents with
     | (p,h)::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_cell ls dsh h v1
                      * field_at psh list_struct (StructField list_link :: nil) 
                          (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 destruct contents as [ | [? ?] ?]; simpl; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link):
  forall dsh psh l v , 
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
destruct v; inv H; unfold Int.cmpu; rewrite Int.eq_true; auto.
destruct p.
apply pred_ext;
apply derives_extract_prop; intro.
destruct H0.
contradiction H1.
destruct v; inv H; try split; auto; apply Int.eq_true.
inv H0.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link) dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val, 
             !!(l=(x,h)::r  /\ is_pointer_or_null y) && 
             list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x * 
             lseg ls dsh psh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link): forall dsh psh l x z , 
    lseg ls dsh psh l x z = 
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls dsh psh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply derives_extract_prop; intros. 
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply orp_right1; auto.
destruct p.
apply orp_right2.
unfold lseg_cons.
apply derives_extract_prop; intros.
destruct H. 
apply exp_left; intro tail.
normalize.
apply exp_right with e. rewrite TT_andp.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'.
apply andp_right.
apply prop_right; split; auto.
subst.
auto.
subst. auto.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto. auto.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
inv H0.
destruct p. 
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
inv H0.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
symmetry in H0; inv H0.
 rewrite prop_true_andp by auto.
apply exp_right with y.
normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link):
   forall p P dsh psh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_cell ls dsh h v1 *
             (field_at psh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls dsh psh tail p v2) ->
    P |-- lseg ls dsh psh ((v1,h)::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link):
  forall dsh psh s v v2,
    ptr_neq v v2 ->
     lseg ls dsh psh s v v2 = lseg_cons ls dsh psh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply orp_left; auto. 
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro). 
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link):
  forall dsh psh s v,
      typed_true (tptr list_struct) v ->
     lseg ls dsh psh s v nullval = lseg_cons ls dsh psh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
destruct v; inv H; intuition; try congruence.
intro. apply ptr_eq_e in H. 
inv H.
inv H1.
intro. simpl in H. congruence.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link):
   forall P Q1 Q R (v v2: environ -> val) dsh psh (s: list (val * elemtype ls)),
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) => 
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       local (`(eq p) v) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h) v::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) v ::
                  `(lseg ls dsh psh r) (`y) (v2) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg_cons ls dsh psh s) v v2 :: R)))).
apply derives_trans with
(local (`ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl. 
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y, v rho).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link):
   forall P Q1 Q R e dsh psh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) e (`nullval) :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) => 
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       local (`(eq p) e) && 
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h) e ::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) e ::
                  `(lseg ls dsh psh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
eapply derives_trans.
apply H. normalize.
unfold local. super_unfold_lift.
 intro rho.
apply derives_extract_prop0; intro.
unfold nullval.
normalize. destruct (e rho); inv H0; try congruence; auto.
intro. apply ptr_eq_e in H0. congruence.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val), 
    s=(v,h)::r -> is_pointer_or_null y ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h v) ::
                  `(field_at psh list_struct (StructField list_link :: nil) 
                      (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                  `(lseg ls dsh psh r y v2) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls dsh psh s v v2) :: R)))) 
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (val * elemtype ls), EX y: val,
  !!(s = (v, h) :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (`(list_cell ls dsh h v) ::
       `(field_at psh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type2 list_struct
                         (StructField list_link :: nil)) y) v) ::
        `(lseg ls dsh psh r y v2) :: R)))).
entailer.
apply exp_right with h.
apply exp_right with r.
apply exp_right with y.
normalize.
apply extract_exists_pre; intro h.
apply extract_exists_pre; intro r.
apply extract_exists_pre; intro y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls dsh psh s v nullval) :: R))) |-- 
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val), 
    s=(v,h)::r -> is_pointer_or_null y -> 
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h v) ::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                  `(lseg ls dsh psh r y nullval) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls dsh psh s v nullval) :: R)))) 
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
eapply derives_trans; [apply H |].
normalize.
clear - H1; destruct v; try contradiction; intro H; inv H.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link): 
    forall dsh psh p q, lseg ls dsh psh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H0.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link):
     forall dsh psh h r x z , 
    lseg ls dsh psh (h::r) x z = 
        !!(x = fst h /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_cell ls dsh (snd h) x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x *
   lseg ls dsh psh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold lseg_cons.
 normalize.
 symmetry in H0; inv H0.
 apply exp_right with y. normalize.
 normalize. destruct h as [p h]. simpl in *.
 apply orp_right2.
 unfold lseg_cons.
 rewrite prop_true_andp by auto.
 apply exp_right with h. apply exp_right with r.  apply exp_right with y.
 normalize.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link) 
           dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val, 
             !!(l=r++(y,h)::nil /\ is_pointer_or_null y)  && 
                       list_cell ls dsh h y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls dsh psh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link): forall dsh psh l x h y w z, 
             sepalg.nonidentity psh ->
             list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls dsh psh l x y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls dsh psh (l++(y,h)::nil) x z * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z.
Proof.
intros. rename H into SH.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
revert x; induction l; simpl; intros.
*
normalize.
apply exp_right with z.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H. subst y.
rewrite sepcon_assoc.
eapply derives_trans.
apply sepcon_derives.
apply derives_refl.
2: rewrite sepcon_FF; auto.
apply field_at_conflict; auto.
apply list_link_size_in_range.
apply list_struct_alignas_legal.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by (apply ptr_eq_refl; auto).
normalize.
*
destruct a as [v el].
normalize.
apply exp_right with x0.
normalize.
specialize (IHl x0).
apply andp_right.
rewrite prop_and.
apply andp_right; [ | apply prop_right; auto].
apply not_prop_right; intro.
apply ptr_eq_e in H1. subst x.
pull_right (field_at psh list_struct (StructField list_link :: nil)
  (valinject (nested_field_type2 list_struct (StructField list_link :: nil))
     x0) z).
rewrite sepcon_assoc.
eapply derives_trans.
apply sepcon_derives.
apply derives_refl.
2: rewrite sepcon_FF; auto.
apply field_at_conflict; auto.
apply list_link_size_in_range.
apply list_struct_alignas_legal.
pull_right (list_cell ls dsh el x).
apply sepcon_derives; auto.
pull_right (field_at psh list_struct (StructField list_link :: nil)
      (valinject
         (nested_field_type2 list_struct (StructField list_link :: nil)) x0)
      x).
apply sepcon_derives; auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link): forall dsh psh l x h y, 
             list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * 
             lseg ls dsh psh l x y
   |--   lseg ls dsh psh (l++(y,h)::nil) x nullval.
Proof.
intros.
revert x; induction l; simpl; intros.
*
normalize.
apply exp_right with nullval.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H. subst y.
entailer!.
destruct H. contradiction H.
rewrite prop_true_andp by reflexivity.
rewrite prop_true_andp by (split; reflexivity).
normalize.
*
destruct a as [v el].
normalize.
apply exp_right with x0.
normalize.
specialize (IHl x0).
apply andp_right.
rewrite prop_and.
apply andp_right; [ | apply prop_right; auto].
apply not_prop_right; intro.
apply ptr_eq_e in H1. subst x.
entailer.
destruct H2; contradiction H2.
eapply derives_trans.
2: apply sepcon_derives; [ | eassumption]; apply derives_refl.
clear IHl.
cancel.
Qed.

(*
Lemma lseg_unroll_right (ls: listspec list_structid list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)
*)

Lemma lseg_local_facts: 
  forall ls dsh psh contents p q, 
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H. 
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0.
apply int_eq_e in H. subst. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0. subst.
split; auto; split; auto.
destruct p0.
normalize.
rewrite field_at_isptr.
normalize.
apply prop_right.
split. intro; subst q.
contradiction H. normalize.
intros. inv H1.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link)
    (dsh psh : share) 
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link) (dsh psh : share) (h : elemtype ls)
   (r : list (val * elemtype ls)) 
  (x x' z : val), lseg ls dsh psh ((x',h) :: r) x z =
  !!(x=x' /\ ~ ptr_eq x z) && (EX  y : val, lseg_cell ls dsh psh h x y * lseg ls dsh psh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {dsh psh: share} 
  {ls : listspec list_structid list_link} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls dsh psh x tl tl' * P tl |-- FF) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  revert hd; induction ct1; simpl; intros; auto.
  *
  normalize.
  *
  destruct a  as [v a].
  normalize.
  apply exp_right with y.
  apply andp_right.
  apply not_prop_right; intro. apply ptr_eq_e in H2; subst hd.
  clear IHct1.
  unfold lseg_cell in H.
  specialize (H a y).
  rewrite prop_true_andp in H by auto.
  apply derives_trans with
        (lseg ls dsh psh ct1 y mid * lseg ls dsh psh ct2 mid tl * FF).
 cancel. auto.
  rewrite sepcon_FF; auto.
  normalize.
  specialize (IHct1 y). clear H. 
   do 2 rewrite sepcon_assoc.
  eapply derives_trans.
 apply sepcon_derives.
  apply derives_refl.
  rewrite <- !sepcon_assoc; eassumption.
  cancel.
Qed.

End LIST2.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

Hint Resolve lseg_local_facts : saturate_local.
End LsegGeneral.

Module LsegSpecial.

Section LIST.
Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.
Context  {list_structid: ident} {list_link: ident}.

Definition lseg (ls: listspec list_structid list_link) (sh: share)
   (contents: list (elemtype ls)) (x y: val) : mpred :=
    EX al:list (val*elemtype ls),
          !! (contents = map snd al) && 
             LsegGeneral.lseg ls sh sh al x y.

Lemma lseg_unfold (ls: listspec list_structid list_link): forall sh contents v1 v2,
    lseg ls sh contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_cell ls sh h v1
                      * field_at sh list_struct (StructField list_link :: nil) 
                          (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) v1
                      *  lseg ls sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 revert v1; induction contents; intros.
 apply pred_ext.
 normalize. destruct al; inv H.
 rewrite LsegGeneral.lseg_nil_eq; auto.
 apply exp_right with nil.
 apply derives_extract_prop; intro.
 normalize.
 apply pred_ext.
 apply exp_left; intros [ | [v1' a'] al].
 normalize. inv H.
 apply derives_extract_prop; intro.
 symmetry in H; inv H.
 rewrite LsegGeneral.lseg_cons_eq; auto.
 apply derives_extract_prop; intros [? ?].
 simpl in H;  subst v1'.
 apply exp_left; intro y.
 normalize. apply exp_right with y. normalize.
 repeat apply sepcon_derives; auto.
 apply exp_right with al; normalize.
 normalize.
 apply exp_right with ((v1,a)::al); normalize.
 simpl.
 normalize. apply exp_right with tail. normalize.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link):
  forall sh l v , 
  is_pointer_or_null v ->
    lseg ls sh l v v = !!(l=nil) && emp.
Proof.
intros.
unfold lseg.
apply pred_ext.
normalize.
rewrite LsegGeneral.lseg_eq by auto. normalize.
apply exp_right with nil.
normalize.
Qed. 

Definition lseg_cons (ls: listspec list_structid list_link) sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val, 
             !!(l=h::r  /\ is_pointer_or_null y) && 
             list_cell ls sh h x *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x * 
              lseg ls sh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link): forall sh l x z , 
    lseg ls sh l x z = 
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls sh l x z.
Proof.
intros.
unfold lseg, lseg_cons.
apply pred_ext.
*
apply exp_left; intros.
apply derives_extract_prop; intro.
rewrite LsegGeneral.lseg_unroll.
apply orp_left; [apply orp_right1 | apply orp_right2].
rewrite andp_assoc; repeat (apply derives_extract_prop; intro).
subst. simpl.
normalize.
unfold LsegGeneral.lseg_cons.
apply derives_extract_prop; intro.
rewrite prop_true_andp by auto.
apply exp_derives; intro h.
apply exp_left; intro r; apply exp_right with (map snd r).
apply exp_derives; intro y.
normalize.
subst l.
unfold lseg.
cancel.
apply exp_right with r; normalize.
*
apply orp_left.
rewrite andp_assoc; repeat (apply derives_extract_prop; intro).
subst.
apply exp_right with nil.
simpl. normalize.
apply derives_extract_prop; intro.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
normalize.
unfold lseg.
normalize.
apply exp_right with ((x,h)::al).
normalize.
simpl.
normalize.
apply exp_right with y.
normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link):
   forall p P sh h (tail: list (elemtype ls)) v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_cell ls sh h v1 *
             (field_at sh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls sh tail p v2) ->
    P |-- lseg ls sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link):
  forall sh s v v2,
    ptr_neq v v2 ->
     lseg ls sh s v v2 = lseg_cons ls sh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply orp_left; auto. 
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro). 
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link):
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg ls sh s v nullval = lseg_cons ls sh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
destruct v; inv H; intuition; try congruence.
intro. apply ptr_eq_e in H. 
inv H.
inv H1.
intro. simpl in H. congruence.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link):
   forall P Q1 Q R (v v2: environ -> val) sh (s: list (elemtype ls)),
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) => 
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h) v::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) v ::
                   `(lseg ls sh r) (`y) (v2) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg_cons ls sh s) v v2 :: R)))).
apply derives_trans with
(local (`ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl. 
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link):
   forall P Q1 Q R e sh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) e (`nullval) :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) => 
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h) e ::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) e ::
                   `(lseg ls sh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
eapply derives_trans.
apply H. normalize.
unfold local. super_unfold_lift.
 intro rho.
apply derives_extract_prop0; intro.
unfold nullval.
normalize. destruct (e rho); inv H0; try congruence; auto.
intro. apply ptr_eq_e in H0. congruence.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q sh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), 
    s=h::r -> is_pointer_or_null y ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h v) ::
                  `(field_at sh list_struct (StructField list_link :: nil) 
                      (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                   `(lseg ls sh r y v2) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s v v2) :: R)))) 
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (elemtype ls), EX y: val,
  !!(s = h :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (`(list_cell ls sh h v) ::
       `(field_at sh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type2 list_struct
                         (StructField list_link :: nil)) y) v) ::
        `(lseg ls sh r y v2) :: R)))).
entailer.
apply exp_right with h.
apply exp_right with r.
apply exp_right with y.
normalize.
apply extract_exists_pre; intro h.
apply extract_exists_pre; intro r.
apply extract_exists_pre; intro y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q sh s v R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls sh s v nullval) :: R))) |-- 
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), 
    s=h::r -> is_pointer_or_null y -> 
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h v) ::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                   `(lseg ls sh r y nullval) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s v nullval) :: R)))) 
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
eapply derives_trans; [apply H |].
normalize.
clear - H1; destruct v; try contradiction; intro H; inv H.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link): 
    forall sh p q, lseg ls sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H0.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link):
     forall sh h r x z , 
    lseg ls sh (h::r) x z = 
        !!(~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_cell ls sh h x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x *
   lseg ls sh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold lseg_cons.
 normalize.
 symmetry in H0; inv H0.
 apply exp_right with y. normalize.
 apply orp_right2.
 unfold lseg_cons.
 apply andp_derives; auto.
 apply exp_right with h. apply exp_right with r.  apply exp_derives; intro y.
 normalize.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link) 
           sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val, 
             !!(l=r++(h::nil) /\ is_pointer_or_null y)  && 
                       list_cell ls sh h y *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
              lseg ls sh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link): forall sh l x h y w z, 
       sepalg.nonidentity sh ->
             list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls sh l x y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls sh (l++h::nil) x z * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z.
Proof.
intros.
unfold lseg.
normalize.
apply exp_right with (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
eapply derives_trans; [ | apply LsegGeneral.lseg_cons_right_neq; auto].
cancel.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link): forall sh l x h y, 
             list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * 
             lseg ls sh l x y
   |--   lseg ls sh (l++h::nil) x nullval.
Proof.
intros.
unfold lseg.
normalize.
apply exp_right with (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
eapply derives_trans; [ | apply LsegGeneral.lseg_cons_right_null].
cancel.
Qed.

(*
Lemma lseg_unroll_right (ls: listspec list_structid list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)
*)

Lemma lseg_local_facts: 
  forall ls sh contents p q, 
     lseg ls sh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
unfold lseg.
normalize.
eapply derives_trans; [apply LsegGeneral.lseg_local_facts |].
normalize.
split; auto.
rewrite H0.
clear.
destruct al; simpl; intuition; try congruence.
Qed.

Definition lseg_cell (ls: listspec list_structid list_link)
    (sh : share) 
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_cell ls sh v x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link) (sh : share) (h : elemtype ls)
   (r : list (elemtype ls)) 
  (x z : val), lseg ls sh (h :: r) x z =
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls sh h x y * lseg ls sh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {sh: share} 
  {ls : listspec list_structid list_link} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls sh x tl tl' * P tl |-- FF) ->
  (lseg ls sh ct1 hd mid) * lseg ls sh ct2 mid tl * P tl|--
  (lseg ls sh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  unfold lseg.
 normalize.
 eapply derives_trans.
 apply LsegGeneral.list_append.
 intros.
 eapply derives_trans; [ | apply (H x0 tl')].
 unfold lseg_cell, LsegGeneral.lseg_cell.
 entailer.
 apply exp_right with (x++al).
 rewrite prop_true_andp; auto.
 rewrite map_app; reflexivity.
Qed.
End LIST.

Hint Rewrite @lseg_nil_eq : norm.
Hint Rewrite @lseg_eq using reflexivity: norm.
Hint Resolve lseg_local_facts : saturate_local.

End LsegSpecial.

Module Links.

Section LIST2.
Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.
Context  {list_structid: ident} {list_link: ident}.

Definition vund  (ls: listspec list_structid list_link) : elemtype ls :=
 compact_prod_gen
      (fun it => default_val (field_type (fst it) list_fields)) (@all_but_link list_link  list_fields).

Definition lseg (ls: listspec list_structid list_link) (dsh psh: share) 
            (contents: list val) (x z: val) : mpred :=
  LsegGeneral.lseg ls dsh psh (map (fun v => (v, vund ls)) contents) x z.

Lemma join_cell_link (ls: listspec list_structid list_link):
  forall v' ash bsh psh p v, 
   sepalg.join ash bsh psh ->
  ~ (readable_share ash) ->
    readable_share bsh ->
   list_cell ls ash v' p * list_cell ls bsh v p = list_cell ls psh v p.
 Proof.
 intros.
 unfold list_cell.
 unfold maybe_data_at.
 rewrite if_false by auto.
 rewrite if_true by auto.
 rewrite if_true.
Focus 2. {
  clear - H H1;
        unfold readable_share in *.
  unfold nonempty_share, sepalg.nonidentity in *.
  contradict H1.
  assert (Share.Ord bsh psh) 
    by (apply leq_join_sub; eexists; eauto).
  apply Share.ord_spec1 in H0. rewrite H0.
  rewrite <- Share.glb_assoc.
  rewrite (Share.glb_commute Share.Rsh).
  rewrite Share.glb_assoc.
  apply identity_share_bot in  H1. rewrite H1.
  rewrite Share.glb_bot.
  apply bot_identity.
} Unfocus.
 apply pred_ext.
*
 eapply derives_trans.
 apply wand_join.
 apply wand_derives; auto.
 unfold field_at_.
 rewrite (field_at_share_join ash bsh psh); try auto.
 erewrite nonreadable_readable_memory_block_data_at_join; eauto.
*  admit.  (* for Qinxiang *)
Qed.

Lemma lseg_unfold (ls: listspec list_structid list_link): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 = 
     match contents with
     | p::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_cell ls dsh (vund ls) v1
                      * field_at psh list_struct (StructField list_link :: nil) 
                          (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 rewrite LsegGeneral.lseg_unfold.
 revert v1; induction contents; simpl; intros; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link):
  forall dsh psh l v , 
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
destruct v; inv H; unfold Int.cmpu; rewrite Int.eq_true; auto.
apply pred_ext;
apply derives_extract_prop; intro.
destruct H0.
contradiction H1.
destruct v; inv H; try split; auto; apply Int.eq_true.
inv H0.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link) dsh psh
           (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list val, EX y:val, 
             !!(l=x::r  /\ is_pointer_or_null y) && 
             list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x * 
             lseg ls dsh psh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link): forall dsh psh l x z , 
    ~ (readable_share dsh) ->
    lseg ls dsh psh l x z = 
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls dsh psh l x z.
Proof.
intros.
rename H into NR.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply derives_extract_prop; intros. 
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply orp_right1; auto.
apply orp_right2.
unfold lseg_cons.
apply derives_extract_prop; intros.
destruct H.
subst x. 
apply exp_left; intro tail.
rewrite (prop_true_andp (~ptr_eq v z)) by auto.
apply exp_right with (vund ls).
apply exp_right with l.
apply exp_right with tail.
normalize.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto. auto.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
inv H0.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
inv H0.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
symmetry in H0; inv H0.
 rewrite prop_true_andp by auto.
apply exp_right with y.
normalize.
repeat (apply sepcon_derives; auto).
clear - NR.
unfold list_cell.
apply wand_derives; auto.
unfold maybe_data_at.
rewrite if_false by auto.
rewrite if_false by auto.
auto.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link):
   forall p P dsh psh h tail v1 v2,
    ~ (readable_share dsh) ->
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_cell ls dsh h v1 *
             (field_at psh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls dsh psh tail p v2) ->
    P |-- lseg ls dsh psh (v1::tail) v1 v2.
Proof. intros. rewrite lseg_unroll by auto. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ eassumption | ].
 apply sepcon_derives; auto.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link):
  forall dsh psh s v v2,
    ~ (readable_share dsh) ->
    ptr_neq v v2 ->
     lseg ls dsh psh s v v2 = lseg_cons ls dsh psh s v v2.
intros. rewrite lseg_unroll by auto.
apply pred_ext. apply orp_left; auto. 
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro). 
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link):
  forall dsh psh s v,
    ~ (readable_share dsh) ->
      typed_true (tptr list_struct) v ->
     lseg ls dsh psh s v nullval = lseg_cons ls dsh psh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq; auto.
destruct v; inv H0; intuition; try congruence.
intro. apply ptr_eq_e in H0. 
inv H0.
inv H2.
intro. simpl in H0. auto.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link):
   forall P Q1 Q R (v v2: environ -> val) dsh psh (s: list val),
    ~ (readable_share dsh) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R))) |--
     EX hryp: elemtype ls * list val * val * val,
      match hryp with (h,r,y,p) => 
       !! (s=p::r /\ is_pointer_or_null y) &&
       local (`(eq p) v) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h) v::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) v ::
                  `(lseg ls dsh psh r) (`y) (v2) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg_cons ls dsh psh s) v v2 :: R)))).
apply derives_trans with
(local (`ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl. 
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y, v rho).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link):
   forall P Q1 Q R e dsh psh s,
    ~ (readable_share dsh) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls dsh psh s) e (`nullval) :: R))) |--
     EX hryp: elemtype ls * list val * val * val,
      match hryp with (h,r,y,p) => 
       !! (s=p::r /\ is_pointer_or_null y) &&
       local (`(eq p) e) && 
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h) e ::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) e ::
                  `(lseg ls dsh psh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq; auto.
eapply derives_trans.
apply H0. normalize.
unfold local. super_unfold_lift.
 intro rho.
apply derives_extract_prop0; intro.
unfold nullval.
normalize. destruct (e rho); inv H1; try congruence; auto.
intro. apply ptr_eq_e in H1. congruence.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v v2 R c Post,
    ~ (readable_share dsh) ->
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list val) (y: val), 
    s=v::r -> is_pointer_or_null y ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h v) ::
                  `(field_at psh list_struct (StructField list_link :: nil) 
                      (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                  `(lseg ls dsh psh r y v2) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls dsh psh s v v2) :: R)))) 
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list val, EX y: val,
  !!(s = v :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (`(list_cell ls dsh h v) ::
       `(field_at psh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type2 list_struct
                         (StructField list_link :: nil)) y) v) ::
        `(lseg ls dsh psh r y v2) :: R)))).
entailer.
apply exp_right with h.
apply exp_right with r.
apply exp_right with y.
normalize.
apply extract_exists_pre; intro h.
apply extract_exists_pre; intro r.
apply extract_exists_pre; intro y.
apply semax_extract_prop; intros [? ?].
eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link):
  forall (Espec: OracleKind)
      Delta P Q dsh psh s v R c Post,
    ~ (readable_share dsh) ->
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls dsh psh s v nullval) :: R))) |-- 
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list val) (y: val), 
    s=v::r -> is_pointer_or_null y -> 
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls dsh h v) ::
                  `(field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                  `(lseg ls dsh psh r y nullval) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls dsh psh s v nullval) :: R)))) 
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
eapply derives_trans; [eapply H0 |].
normalize.
clear - H2; destruct v; try contradiction; intro H0; inv H0.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link): 
    forall dsh psh p q,
    ~ (readable_share dsh) ->
   lseg ls dsh psh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll by auto.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H1.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link):
     forall dsh psh h r x z ,
     ~ (readable_share dsh) ->
    lseg ls dsh psh (h::r) x z = 
        !!(x = h /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_cell ls dsh (vund ls) x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x *
   lseg ls dsh psh r y z).
Proof.
 intros. rewrite lseg_unroll by auto.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H1.
 unfold lseg_cons.
 normalize.
 symmetry in H1; inv H1.
 apply exp_right with y. normalize.
 repeat (apply sepcon_derives; auto).
 unfold list_cell, maybe_data_at;
  rewrite !if_false by auto; auto.
 normalize. simpl in *.
 apply orp_right2.
 unfold lseg_cons.
 rewrite prop_true_andp by auto.
 apply exp_right with (vund ls). apply exp_right with r.  apply exp_right with y.
 normalize.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link) 
           dsh psh (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX r:list val , EX y:val, 
             !!(l=r++y::nil /\ is_pointer_or_null y)  && 
                       list_cell ls dsh (vund ls) y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls dsh psh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link): 
      forall dsh psh l x h y w z, 
     sepalg.nonidentity psh ->
     ~ (readable_share dsh) ->
             list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls dsh psh l x y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls dsh psh (l++y::nil) x z * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z.
Proof.
intros. rename H into SH. rename H0 into NR.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
revert x; induction l; simpl; intros.
*
unfold lseg.
simpl.
normalize.
apply exp_right with z.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H. subst y.
rewrite sepcon_assoc.
eapply derives_trans.
apply sepcon_derives.
apply derives_refl.
2: rewrite sepcon_FF; auto.
apply field_at_conflict; auto.
apply list_link_size_in_range.
apply list_struct_alignas_legal.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by (apply ptr_eq_refl; auto).
normalize.
 unfold list_cell, maybe_data_at;
  rewrite !if_false by auto; auto.
*
unfold lseg; simpl.
normalize.
apply exp_right with x0.
normalize.
specialize (IHl x0).
apply andp_right.
rewrite prop_and.
apply andp_right; [ | apply prop_right; auto].
apply not_prop_right; intro.
apply ptr_eq_e in H1. subst x.
pull_right (field_at psh list_struct (StructField list_link :: nil)
  (valinject (nested_field_type2 list_struct (StructField list_link :: nil))
     x0) z).
rewrite sepcon_assoc.
eapply derives_trans.
apply sepcon_derives.
apply derives_refl.
2: rewrite sepcon_FF; auto.
apply field_at_conflict; auto.
apply list_link_size_in_range.
apply list_struct_alignas_legal.
pull_right (list_cell ls dsh (vund ls) x).
apply sepcon_derives; auto.
pull_right (field_at psh list_struct (StructField list_link :: nil)
      (valinject
         (nested_field_type2 list_struct (StructField list_link :: nil)) x0)
      x).
apply sepcon_derives; auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link): forall dsh psh l x h y,
     ~ (readable_share dsh) -> 
             list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * 
             lseg ls dsh psh l x y
   |--   lseg ls dsh psh (l++y::nil) x nullval.
Proof.
intros. rename H into NR.
unfold lseg.
revert x; induction l; simpl; intros.
*
normalize.
apply exp_right with nullval.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H. subst y.
entailer!.
destruct H. contradiction H.
rewrite prop_true_andp by reflexivity.
rewrite prop_true_andp by (split; reflexivity).
normalize.
 unfold list_cell, maybe_data_at;
  rewrite !if_false by auto; auto.
*
normalize.
apply exp_right with x0.
normalize.
specialize (IHl x0).
apply andp_right.
rewrite prop_and.
apply andp_right; [ | apply prop_right; auto].
apply not_prop_right; intro.
apply ptr_eq_e in H1. subst x.
entailer.
destruct H2; contradiction H2.
eapply derives_trans.
2: apply sepcon_derives; [ | eassumption]; apply derives_refl.
clear IHl.
cancel.
Qed.

(*
Lemma lseg_unroll_right (ls: listspec list_structid list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)
*)

Lemma lseg_local_facts: 
  forall ls dsh psh contents p q, 
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H. 
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0.
apply int_eq_e in H. subst. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0. subst.
split; auto; split; auto.
normalize.
rewrite field_at_isptr.
normalize.
apply prop_right.
split. intro; subst q.
contradiction H. normalize.
intros. inv H1.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link)
    (dsh psh : share) 
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link) (dsh psh : share) (h : elemtype ls)
   (r : list val )  (x z : val), 
     ~ (readable_share dsh) -> 
  lseg ls dsh psh (x :: r) x z =
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls dsh psh h x y * lseg ls dsh psh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq by auto.
  unfold lseg_cell.
 normalize.
 f_equal. extensionality y.
 f_equal. f_equal. f_equal. f_equal.
 unfold list_cell, maybe_data_at;
  rewrite !if_false by auto; auto.
Qed.

Lemma list_append: forall {dsh psh: share} 
  {ls : listspec list_structid list_link} (hd mid tl:val) ct1 ct2 P,
  (forall tl', lseg_cell ls dsh psh (vund ls) tl tl' * P tl |-- FF) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  unfold lseg.
  revert hd; induction ct1; simpl; intros; auto.
  *
  normalize.
  *
  normalize.
  apply exp_right with y.
  apply andp_right.
  apply not_prop_right; intro. apply ptr_eq_e in H2; subst hd.
  clear IHct1.
  specialize (H y).
  unfold lseg_cell in H.
  rewrite prop_true_andp in H by auto.
  apply derives_trans with
        (lseg ls dsh psh ct1 y mid * lseg ls dsh psh ct2 mid tl * FF).
 cancel. auto.
  rewrite sepcon_FF; auto.
  normalize.
  specialize (IHct1 y). clear H. 
   do 2 rewrite sepcon_assoc.
  eapply derives_trans.
 apply sepcon_derives.
  apply derives_refl.
  rewrite <- !sepcon_assoc; eassumption.
  cancel.
Qed.

Lemma list_cell_valid_pointer:
  forall (ls : listspec list_structid list_link)  sh v p, 
   sh <> Share.bot ->
   list_cell ls sh v p |-- valid_pointer p.
Proof.
 intros.
Admitted. (* for Qinxiang *)

Lemma lseg_valid_pointer:
  forall (ls : listspec list_structid list_link) dsh psh contents p q R,
   dsh <> Share.bot ->
    R |-- valid_pointer q ->
    R * lseg ls dsh psh contents p q |-- valid_pointer p.
Proof.
intros.
unfold lseg.
destruct contents; simpl; intros.
normalize.
normalize.
apply sepcon_valid_pointer2.
apply sepcon_valid_pointer1.
apply sepcon_valid_pointer1.
apply list_cell_valid_pointer; auto.
Qed.

End LIST2.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

Hint Resolve lseg_local_facts : saturate_local.


Hint Resolve list_cell_valid_pointer : valid_pointer.
Hint Resolve denote_tc_comparable_split : valid_pointer.

Ltac resolve_lseg_valid_pointer :=
match goal with 
 | |- ?Q |-- valid_pointer ?p =>
   match Q with context [lseg ?A ?B ?C ?D p ?q] =>
   repeat rewrite <- sepcon_assoc;
   pull_right (lseg A B C D p q);
   apply lseg_valid_pointer; 
   auto 50 with valid_pointer
   end
 end.

Hint Extern 10 (_ |-- valid_pointer _) => resolve_lseg_valid_pointer.

End Links.

