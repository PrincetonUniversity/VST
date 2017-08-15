Load loadpath.
Require Import Coq.Lists.List.
Require Import veristar.variables veristar.datatypes veristar.list_denote.
Require Import compcert.Coqlib.
Require Import VST.veric.Coqlib2.
Require Import VST.msl.predicates_sa.
Require Import ZArith.
Require Import veristar.veristar_sound.
Require Import veristar.model_type veristar.model.
Require Import Permutation.
Require Import veristar.veristar.
Require Import veristar.isolate.
Require Import veristar.fresh.
Require Import veristar.basic.
Require Import Classical.

Module Type ISO_SOUND.
Declare Module VeriStarSound : VERISTAR_SOUND.
Import VeriStarSound VSM VeriStarLogic.

Axiom expr_denote_heap_ind : forall x s h h',
  expr_denote x (State s h)=expr_denote x (State s h').

Axiom oracle_sound: forall (e: entailment),
    oracle e = true -> entailment_denote e.


Definition existsv (nextv: var) (P: spred) : spred :=
   fun s => exists y,  P (State (env_set nextv y (stk s)) (hp s)).

Axiom existsv_refl:  forall P x, P |-- existsv x P.

Definition fresh {A} (f: A -> var) (a: A) (x: var) : Prop :=  Ident.lt (f a) x.

Ltac do_fresh1 :=
  repeat match goal with H: Ile _ _ |- _ => revert H
                                     | H: Ident.lt _ _ |- _ => revert H
                                     | H: fresh _ _ _ |- _ => revert H end;
  clear;
  unfold fresh; simpl;
  repeat ((rewrite freshmax_list_app || rewrite freshmax_list_rev
                || rewrite varmax_minid || rewrite varmax_minid'); simpl).

Ltac do_fresh :=
  do_fresh1; intros;
  repeat match goal with
             |  H: Ident.lt (var_max _ _) _ |- _ => apply var_max_split in H; destruct H
             end;
  repeat apply var_max_intro; auto;
  try solve [etransitivity; eauto].

Definition set_in_state nextv z s := State (env_set nextv z (stk s)) (hp s).

Axiom expr_denote_agree:
  forall e s nextv z,
  fresh freshmax_expr e nextv ->
  expr_denote e s = expr_denote e (set_in_state nextv z s).

Axiom pn_atom_denote_agree:
 forall a s nextv z,
  fresh freshmax_pn_atom a nextv ->
  pn_atom_denote a s ->
  pn_atom_denote a (set_in_state nextv z s).

Axiom space_atom_denote_agree:
 forall a s nextv z,
  fresh freshmax_space_atom a nextv ->
  space_atom_denote a s ->
  space_atom_denote a (set_in_state nextv z s).

Axiom list_denote__pn_atom_agree:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_pn_atom) pos nextv ->
  list_denote pn_atom_denote (@andp _) TT pos s ->
  list_denote pn_atom_denote (@andp _) TT pos (set_in_state nextv z s).

Axiom list_denote_space_agree:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_space_atom) pos nextv ->
  list_denote space_atom_denote (@sepcon _ _) emp pos s ->
  list_denote space_atom_denote (@sepcon _ _) emp pos (set_in_state nextv z s).

(*
 Lemma agree_except_sym:
  forall x s s', agree_except x s s' -> agree_except x s' s.
 Proof.
 unfold agree_except; intuition. symmetry. apply H0; auto.
 Qed.
*)



Axiom list_denote_agree_pn_atom_neg:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_pn_atom) pos nextv ->
  list_denote (neg oo pn_atom_denote) (@andp _) TT pos s ->
  list_denote (neg oo pn_atom_denote) (@andp _) TT pos (set_in_state nextv z s).

Axiom fresh_lt:
  forall {A} (f: A -> var) a x y, fresh f a x -> Ident.lt x y -> fresh f a y.

Axiom space_denote_permute: forall l l',
  Permutation l l' ->  space_denote l = space_denote l'.

Axiom assertion_denote_permute: forall pi l l',
  Permutation l l' ->
   assertion_denote (Assertion pi l) = assertion_denote (Assertion pi l').


Axiom incon_e: forall P, incon P = true -> assertion_denote P |-- FF.

Axiom isolate_sound:
  forall e P nextv nextv2 results
      (LT: Ident.lt nextv nextv2),
      isolate e P nextv = Some results ->
       fresh freshmax_expr e nextv ->
       fresh freshmax_assertion P nextv ->
      assertion_denote P |--
        fold_right (fun P => orp (existsv nextv (assertion_denote P))) FF results /\
      forall Q, In Q results ->
            match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end /\
           fresh freshmax_assertion Q nextv2.
End ISO_SOUND.

Module Iso_Sound (VSS: VERISTAR_SOUND) : ISO_SOUND with Module VeriStarSound := VSS.
Module VeriStarSound := VSS.
Import VeriStarSound VSM VeriStarLogic.

(********duplicate temporarily a lemma from wellformed_sound.
Maybe some of the lemmas there Repair import-structire later******
********)

Lemma expr_denote_heap_ind : forall x s h h',
  expr_denote x (State s h)=expr_denote x (State s h').
Proof.
intros. destruct x; auto.
Qed.

(************end of duplicated lemma ********)

Lemma oracle_sound: forall (e: entailment),
    oracle e = true -> entailment_denote e.
Proof.
unfold oracle;
intros.
apply check_entailment_sound.
destruct (VeriStar.check_entailment e); congruence.
Qed.

(*
Definition agree_except (x: var) (s s': state) : Prop :=
   (forall x', x' <> x -> stack_get (stk s) (Some x') = stack_get (stk s') (Some x')) /\ hp s = hp s'.

Lemma agree_except_refl: forall x s, agree_except x s s.
Proof. unfold agree_except; intuition.
Qed.
Hint Resolve agree_except_refl.

Definition existsv (nextv: var) (P: spred) : spred :=
   fun s => exists s', agree_except nextv s s' /\ P s'.
*)

Definition existsv (nextv: var) (P: spred) : spred :=
   fun s => exists y,  P (State (env_set nextv y (stk s)) (hp s)).

Lemma existsv_refl:
  forall P x, P |-- existsv x P.
Proof.
intros; intros s ?. exists (env_get (stk s) x).
destruct s; simpl. replace (env_set x (env_get s x) s) with s; auto.
rewrite env_reset; auto.
Qed.

Definition fresh {A} (f: A -> var) (a: A) (x: var) : Prop :=  Ident.lt (f a) x.

Lemma list_denote_separate':
  forall (X Y: Type) (f: X -> spred) (g: Y -> spred) (base: spred) l1 l2,
  list_denote f (@sepcon _ _) (list_denote g (@sepcon _ _) base l2) l1 =
  sepcon (list_denote f (@sepcon _ _) emp l1)
   (sepcon (list_denote g (@sepcon _ _) emp l2)
     base).
Proof.
induction l1; simpl; intros.
rewrite emp_sepcon.
induction l2; simpl. rewrite emp_sepcon; auto.
rewrite IHl2. rewrite sepcon_assoc; auto.
rewrite sepcon_assoc.
f_equal.
auto.
Qed.

Ltac do_fresh1 :=
  repeat match goal with H: Ile _ _ |- _ => revert H
                                     | H: Ident.lt _ _ |- _ => revert H
                                     | H: fresh _ _ _ |- _ => revert H end;
  clear;
  unfold fresh; simpl;
  repeat ((rewrite freshmax_list_app || rewrite freshmax_list_rev
                || rewrite varmax_minid || rewrite varmax_minid'); simpl).

Ltac do_fresh :=
  do_fresh1; intros;
  repeat match goal with
             |  H: Ident.lt (var_max _ _) _ |- _ => apply var_max_split in H; destruct H
             end;
  repeat apply var_max_intro; auto;
  try solve [etransitivity; eauto].
(*  repeat rewrite Zpos_succ_morphism in *; solve [auto | omega]. *)

Lemma freshmax_pn_atom_Equ_Destruct: forall e e' nextv,
fresh freshmax_pn_atom (Equ e e') nextv ->
fresh freshmax_expr e nextv /\ fresh freshmax_expr e' nextv.
Proof.
intros.
split; do_fresh.
Qed.

Lemma freshmax_pn_atom_Nequ_Destruct: forall e e' nextv,
fresh freshmax_pn_atom (Nequ e e') nextv ->
fresh freshmax_expr e nextv /\ fresh freshmax_expr e' nextv.
Proof.
intros.
do_fresh.
Qed.

Definition set_in_state nextv z s := State (env_set nextv z (stk s)) (hp s).



Lemma expr_denote_agree:
  forall e s nextv z,
  fresh freshmax_expr e nextv ->
  expr_denote e s = expr_denote e (set_in_state nextv z s).
Proof.
intros.
destruct e; simpl; auto.
rewrite gso_env; auto.
do_fresh. intro; subst.
eapply Ilt_irrefl; eauto.
Qed.

Lemma pn_atom_denote_agree:
 forall a s nextv z,
  fresh freshmax_pn_atom a nextv ->
  pn_atom_denote a s ->
  pn_atom_denote a (set_in_state nextv z s).
Proof.
intros.
destruct a.
  destruct (freshmax_pn_atom_Equ_Destruct _ _ _ H) as [Fe Fe0].
  simpl in *.
  unfold var_eq in *.
  repeat rewrite <- expr_denote_agree; auto.

  destruct (freshmax_pn_atom_Nequ_Destruct _ _ _ H) as [Fe Fe0].
  simpl in *. unfold neg in *.
  contradict H0.
  unfold var_eq in *.
  rewrite <- expr_denote_agree in H0; auto.
  rewrite <- expr_denote_agree in H0; auto.
Qed.

Lemma space_atom_denote_agree:
 forall a s nextv z,
  fresh freshmax_space_atom a nextv ->
  space_atom_denote a s ->
  space_atom_denote a (set_in_state nextv z s).
Proof.
intros.
destruct a.
simpl in *.
rewrite <- (expr_denote_agree e s nextv z) by do_fresh.
rewrite <- (expr_denote_agree e0 s nextv z) by do_fresh.
auto.
simpl in *.
rewrite <- (expr_denote_agree e s nextv z) by do_fresh.
rewrite <- (expr_denote_agree e0 s nextv z) by do_fresh.
auto.
Qed.

Lemma list_denote__pn_atom_agree:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_pn_atom) pos nextv ->
  list_denote pn_atom_denote (@andp _) TT pos s ->
  list_denote pn_atom_denote (@andp _) TT pos (set_in_state nextv z s).
Proof.
intros.
revert H H0; induction pos; simpl; intros; auto.
destruct H0; split.
eapply pn_atom_denote_agree; eauto. do_fresh.
apply IHpos; auto.
do_fresh.
Qed.

Lemma list_denote_space_agree:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_space_atom) pos nextv ->
  list_denote space_atom_denote (@sepcon _ _) emp pos s ->
  list_denote space_atom_denote (@sepcon _ _) emp pos (set_in_state nextv z s).
Proof.
intros.
revert s H H0; induction pos; simpl; intros; auto.
rewrite empstate_empheap in *. simpl; auto.
destruct H0 as [s1 [s2 [ ? [? ?]]]].
exists (set_in_state nextv z s1); exists (set_in_state nextv z s2); split3.
destruct s1; destruct s2; destruct s; destruct H0; destruct H0; simpl in *; subst; unfold set_in_state; split; simpl; auto.
apply msl.sepalg_generators.join_equiv_refl.
apply space_atom_denote_agree; auto; do_fresh.
apply IHpos; auto.
do_fresh.
Qed.

(*
 Lemma agree_except_sym:
  forall x s s', agree_except x s s' -> agree_except x s' s.
 Proof.
 unfold agree_except; intuition. symmetry. apply H0; auto.
 Qed.
*)

Axiom env_reset2: forall s x z, env_set x (env_get s x) (env_set x z s) = s.

Lemma list_denote_agree_pn_atom_neg:
 forall pos s nextv z,
  fresh (freshmax_list freshmax_pn_atom) pos nextv ->
  list_denote (neg oo pn_atom_denote) (@andp _) TT pos s ->
  list_denote (neg oo pn_atom_denote) (@andp _) TT pos (set_in_state nextv z s).
Proof.
intros.
revert H H0; induction pos; simpl; intros; auto.
destruct H0; split.
unfold compose, neg in H0|-*.
contradict H0.
replace s with (set_in_state nextv (env_get (stk s) nextv) (set_in_state nextv z s)).
apply pn_atom_denote_agree; auto.
do_fresh.
clear. unfold set_in_state; destruct s; simpl. f_equal.
apply env_reset2.
apply IHpos; auto.
do_fresh.
Qed.

Lemma fresh_lt:
  forall {A} (f: A -> var) a x y, fresh f a x -> Ident.lt x y -> fresh f a y.
Proof.
intros.
unfold fresh in *. transitivity x; auto.
Qed.

Lemma or_FF: forall {A} (P: pred A), (orp P FF) = P.
Proof. unfold orp; intros; extensionality z; apply prop_ext; intuition.
Qed.

Lemma permute_sigma0:
 forall sigma0 (a: space_atom) sigma, Permutation (sigma0 ++ a :: sigma) (a :: sigma0 ++ sigma).
Proof.
intros; eapply perm_trans; [apply Permutation_app_comm | apply Permutation_cons; apply Permutation_app_comm].
Qed.

Lemma space_denote_permute: forall l l',
  Permutation l l' ->
   space_denote l = space_denote l'.
intros.
unfold space_denote.
apply (listd_perm space_atom_denote _ emp (sepconS _ _) (@sepconA state _ _) l l' H) .
Qed.

Lemma assertion_denote_permute: forall pi l l',
  Permutation l l' ->
   assertion_denote (Assertion pi l) = assertion_denote (Assertion pi l').
intros.
simpl.
rewrite (space_denote_permute _ _ H).
trivial.
Qed.

Lemma Lseg_unfold_neq:
  forall e nextv pi sigma0 e0 e1 sigma s,
    fresh freshmax_expr e nextv ->
    fresh freshmax_assertion (Assertion pi (sigma0 ++ Lseg e0 e1 :: sigma)) nextv ->
    (e === e0) s ->
    list_denote pn_atom_denote (@andp _)
         (space_denote (sigma0 ++ Lseg e0 e1 :: sigma)) pi s ->
    ~ (e0 === e1) s ->
    existsv nextv
      (assertion_denote (Assertion pi (Next e (Var nextv) :: Lseg (Var nextv) e1 :: sigma0 ++ sigma))) s.
Proof.
intros.
rewrite (@listd_prop pn_atom state pn_atom_denote) in H2.
destruct H2 as [HypP HypSig].
rewrite (space_denote_permute _ _  (permute_sigma0 _ _ _ )) in HypSig.
unfold space_denote in HypSig.
rewrite listd_cons in HypSig.
destruct HypSig as [s1 [s2 [? [? ?]]]].
inv H4.
contradiction H3.
unfold var_eq.
clear - H6 H2.
 destruct s1; destruct s2; destruct s; destruct H2; destruct H; simpl in *; auto.
subst; rewrite (expr_denote_heap_ind e0 s h1 h). rewrite (expr_denote_heap_ind e1 s h1 h).
auto.
exists z.
change (State (env_set nextv z (stk s)) (hp s)) with (set_in_state nextv z s).
simpl.
rewrite (@listd_prop pn_atom state pn_atom_denote).
rewrite sepconA; auto with typeclass_instances.
split.
apply list_denote__pn_atom_agree; trivial. do_fresh.
clear HypP.
exists (set_in_state nextv z s1).
exists (set_in_state nextv z s2).
split3.
clear - H2. destruct H2; destruct H;
unfold set_in_state; repeat split; simpl; try congruence.
exists (set_in_state nextv z (State (stk s1) h0)).
exists (set_in_state nextv z (State (stk s1) h1)).
split3; simpl; auto.
split; auto.
apply msl.sepalg_generators.join_equiv_refl.
unfold var_eq in *.
repeat rewrite <- expr_denote_agree by do_fresh.
destruct s as [s h]. destruct s1 as [s1 h1']; destruct s2 as [s2 h2'].
destruct H2. destruct H2. simpl in H11. subst.
simpl in *. subst.
repeat rewrite expr_denote_heap_ind with (h:=h0)(h':=h) in *.
repeat rewrite expr_denote_heap_ind with (h:=h1')(h':=h) in *.
rewrite H1. rewrite H7.
rewrite gss_env.
split; auto.
inv H9; auto.
unfold nil_or_loc. right; eauto.
rewrite gss_env. rewrite <- expr_denote_agree by do_fresh.
destruct s1 as [s' h']; simpl in *.
rewrite expr_denote_heap_ind with (h:=h1)(h':=h'); auto.
apply list_denote_space_agree; auto; do_fresh.
Qed.


Lemma exorcize_sound_Lseg:
 forall (e : expr) (pnatoms : list pn_atom) (e0 e1 : expr)
  (sigma : list space_atom) (nextv : var) (nextv2 : var)
  (sigma0 : list space_atom) (l : list assertion),
  fresh freshmax_expr e nextv ->
  Ident.lt nextv nextv2 ->
  fresh freshmax_assertion
    (Assertion pnatoms (rev (Lseg e0 e1 :: sigma0) ++ sigma)) nextv ->
  entailment_denote
    (Entailment (Assertion pnatoms (rev (Lseg e0 e1 :: sigma0) ++ sigma))
       (Assertion [Equ e e0] (rev (Lseg e0 e1 :: sigma0) ++ sigma))) ->
  (assertion_denote
     (Assertion (Equ e0 e1 :: pnatoms) (rev (Lseg e0 e1 :: sigma0) ++ sigma))
    |-- fold_right
         (fun P => orp (existsv nextv (assertion_denote P))) FF l) /\
   (forall (Q : assertion),
     In Q l ->
          match Q with
          |Assertion _ (Next e0 _ :: _) => e=e0
          | _ => False
          end /\
          fresh freshmax_assertion Q nextv2) ->
        (assertion_denote (Assertion pnatoms (rev (Lseg e0 e1 :: sigma0) ++ sigma))
      |-- fold_right
          (fun P => orp (existsv nextv (assertion_denote P))) FF
          (Assertion pnatoms (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma) :: l)) /\
   (forall Q,
    In Q (Assertion pnatoms (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma) :: l) ->
          match Q with
          |Assertion _ (Next e0 _ :: _) => e=e0
          | _ => False
          end /\
    fresh freshmax_assertion Q nextv2).
Proof.
intros e pnatoms e0 e1 sigma nextv nextv2 sigma0 l FRESHe H1 H H0 IHsigma.
destruct IHsigma.
split.
simpl in H0,H2.
intros s ?.
simpl in H0, H4.
generalize (H0 _ H4); clear H0; intros [? _].
rewrite (@listd_prop pn_atom state pn_atom_denote) in H4.
destruct H4 as [HypP HypSig].
destruct (classic ((e0===e1) s)).
right.
apply H2.
split; auto.
rewrite (@listd_prop pn_atom state pn_atom_denote).
split; auto.
left.
eapply Lseg_unfold_neq with e0; auto.
simpl in H.
rewrite app_ass in H; apply H.
(*repeat rewrite list_denote_separate.*)
rewrite (@listd_prop pn_atom state pn_atom_denote).
split; auto.
rewrite app_ass in HypSig; apply HypSig.
intros.
simpl in H4.
destruct H4.
inv H4.
split; auto.
do_fresh.
apply H3; auto.
Qed.

Lemma incon_e: forall P, incon P = true -> assertion_denote P |-- FF.
Proof.
unfold incon; intros.
forget match P with Assertion _ sigma => sigma end as Q.
apply oracle_sound in H.
simpl in H.
eapply derives_trans; [apply H | clear H].
intros w [H ?]; apply H; reflexivity.
Qed.

Lemma exorcize_sound_nil:
 forall e pnatoms nextv nextv2 sigma0 cl,
    Ident.lt nextv nextv2 ->
    exorcize e pnatoms sigma0 [ ] nextv = Some cl ->
    (assertion_denote (Assertion pnatoms (rev sigma0 ++ [ ]))
     |-- fold_right
       (fun P => orp (existsv nextv (assertion_denote P))) FF cl) /\
       (forall (Q : assertion),
         In Q cl ->
          (match Q with
          |Assertion  _ (Next e0 _ :: _) => e=e0
          | _ => False
          end /\
          fresh freshmax_assertion Q nextv2)).
Proof.
simpl; intros.
revert H0; case_eq (incon (Assertion pnatoms (rev sigma0))); intros; inv H1.
apply incon_e in H0.
split.
rewrite <- app_nil_end.
eapply derives_trans; [apply H0 | auto].
simpl; intros; contradiction.
Qed.


 (* need this bogus "exorcize_e" lemma, because doing it in-line, in the
   obvious way using case_eq or (remember; destruct) makes the Qed take forever. *)
Lemma exorcize_e:
 forall e pnatoms sigma0 e0 e1 sigma nextv cl,
  exorcize e pnatoms sigma0 (Lseg e0 e1 :: sigma) nextv = Some cl ->
  (entailment_denote
       (Entailment (Assertion pnatoms (rev (Lseg e0 e1 :: sigma0) ++ sigma))
          (Assertion [Equ e e0] (rev (Lseg e0 e1 :: sigma0) ++ sigma)))
    /\ (exists cl',
          exorcize e (Equ e0 e1 :: pnatoms) (Lseg e0 e1 :: sigma0) sigma nextv = Some cl' /\
           cl = (Assertion pnatoms
                       (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma)) :: cl'))
  \/ exorcize e pnatoms (Lseg e0 e1 :: sigma0) sigma nextv = Some cl.
Proof.
simpl; intros until cl.
case_eq (oracle
      (Entailment (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
         (Assertion [Equ e e0] (rev sigma0 ++ Lseg e0 e1 :: sigma)))); intros.
revert H0; case_eq (exorcize e (Equ e0 e1 :: pnatoms) (Lseg e0 e1 :: sigma0) sigma nextv);
  intros; inv H1.
left; split; auto.
apply oracle_sound in H; simpl in H.
rewrite app_ass. auto.
exists l; split; auto.
right. auto.
Qed.


Lemma exorcize_sound:
  forall e pnatoms sigma nextv nextv2
      (FRESHe: fresh freshmax_expr e nextv)
      (LT: Ident.lt nextv nextv2),
      (fresh freshmax_assertion (Assertion pnatoms sigma) nextv) ->
      forall cl,
      (exorcize e pnatoms nil sigma nextv) = Some cl ->
 (assertion_denote (Assertion pnatoms sigma)
 |-- fold_right (fun P => orp (existsv nextv (assertion_denote P))) FF cl) /\
       (forall Q,
          In Q cl ->
           match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end /\
          fresh freshmax_assertion Q nextv2).
Proof.
intros.
replace sigma with (rev nil++sigma) in H by auto.
pattern sigma at 1; replace sigma with (rev nil++sigma) by auto.
remember (@nil space_atom) as sigma0.
clear Heqsigma0.
revert pnatoms sigma0 cl H0 H; induction sigma; intros.
apply exorcize_sound_nil; auto.
replace (rev sigma0 ++ a :: sigma) with (rev (a::sigma0) ++ sigma)  in * by apply app_ass.

destruct a.
(* 'Next' case *)
apply (IHsigma _ _ _ H0 H).

(* 'Lseg' case *)
apply exorcize_e in H0.
destruct H0 as [[? [cl' [? ?]]] | ?].
subst cl.
specialize (IHsigma _ _ _ H1).
spec IHsigma; [do_fresh | ].
apply exorcize_sound_Lseg; auto.
apply (IHsigma _ _ _ H0 H).
Qed.


 (* need this bogus "isolate_e" lemma, because doing it in-line, in the
   obvious way using case_eq or (remember; destruct) makes the Qed take forever. *)
Lemma isolate_e:
 forall e pnatoms sigma0 e0 e1 sigma nextv N results,
  isolate' e pnatoms sigma0 (Lseg e0 e1 :: sigma) nextv N = Some results ->
  (entailment_denote
       (Entailment (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
          (Assertion [Equ e e0, Nequ e0 e1] (rev sigma0 ++ Lseg e0 e1 :: sigma)))
          /\ results = [Assertion pnatoms (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma)]
    \/ (entailment_denote
           (Entailment (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
              (Assertion [Equ e e0] (rev sigma0 ++ Lseg e0 e1 :: sigma)))
          /\ isolate' e pnatoms (Lseg e0 e1 :: sigma0) sigma nextv (S N) =Some results)
    \/ isolate' e pnatoms (Lseg e0 e1 :: sigma0) sigma nextv N = Some results).
Proof.
simpl; intros; revert H.
case_eq (oracle
      (Entailment (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
         (Assertion [Equ e e0, Nequ e0 e1] (rev sigma0 ++ Lseg e0 e1 :: sigma)))); intros.
apply oracle_sound in H.
inv H0.
left; auto.
revert H0;
 case_eq (oracle
           (Entailment
              (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
              (Assertion [Equ e e0] (rev sigma0 ++ Lseg e0 e1 :: sigma)))); simpl; intros.
apply oracle_sound in H0.
right; left; auto.
right; right; auto.
Qed.

Lemma if_bool_e:
  forall {A: Type} (b: bool) (c d e: A),
     (if b then c else d) = e ->
     b=true /\ c=e \/ b=false /\ d=e.
Proof.
destruct b; auto.
Qed.

Lemma isolate_Next1:
 forall e e1 sigma nextv nextv2 pnatoms sigma0
    (LT: Ident.lt nextv nextv2),
    fresh freshmax_assertion
       (Assertion pnatoms (rev sigma0 ++ Next e e1 :: sigma)) nextv ->
  (assertion_denote (Assertion pnatoms (rev sigma0 ++ Next e e1 :: sigma))
     |-- fold_right (fun P : assertion => orp (existsv nextv (assertion_denote P))) FF
       [Assertion pnatoms (Next e e1 :: rev sigma0 ++ sigma)]) /\
   (forall Q : assertion,
      In Q [(Assertion pnatoms (Next e e1 :: rev sigma0 ++ sigma))] ->
         match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end  /\
      fresh freshmax_assertion Q nextv2).
Proof.
intros. rename H into H0.
split.
unfold fold_right, snd.
rewrite or_FF.
eapply derives_trans ; [ | apply existsv_refl].
rewrite (assertion_denote_permute pnatoms _ _ (permute_sigma0 _ _ _ )). trivial.
intros.
simpl in H.
destruct H; try contradiction.
inv H.
split; auto.
do_fresh.
Qed.

Lemma isolate_Next2:
  forall e e0 e1 sigma nextv nextv2 pnatoms sigma0
  (FRESHe:  fresh freshmax_expr e nextv)
  (LT: Ident.lt nextv nextv2),
  entailment_denote
     (Entailment (Assertion pnatoms (rev sigma0 ++ Next e0 e1 :: sigma))
        (Assertion [Equ e e0] (rev sigma0 ++ Next e0 e1 :: sigma))) ->
  fresh freshmax_assertion
     (Assertion pnatoms (rev sigma0 ++ Next e0 e1 :: sigma)) nextv ->
  (assertion_denote (Assertion pnatoms (rev sigma0 ++ Next e0 e1 :: sigma))
   |-- fold_right (fun P : assertion => orp (existsv nextv (assertion_denote P))) FF
         [Assertion pnatoms (Next e e1 :: rev sigma0 ++ sigma)]) /\
  (forall (Q : assertion),
   In Q [Assertion pnatoms (Next e e1 :: rev sigma0 ++ sigma)] ->
           match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end/\
   fresh freshmax_assertion Q nextv2).
Proof.
intros.
unfold fold_right, snd. rewrite or_FF.
split.
clear - H.
eapply derives_trans; [ | apply existsv_refl ].
apply derives_trans with (assertion_denote (Assertion (Equ e e0::pnatoms) (rev sigma0 ++ Next e e1 :: sigma))).
intros s H1; generalize (H _ H1); intro.
clear H; simpl  in *. destruct H0. split; auto.
repeat rewrite list_denote_separate in *.
rewrite (@listd_prop pn_atom state pn_atom_denote).
rewrite (@listd_prop pn_atom state pn_atom_denote) in H1.
destruct H1 as [? ?]; split; auto.
rewrite (space_denote_permute _ _ (permute_sigma0 _ _ _)) in H0.
rewrite (space_denote_permute _ _ (permute_sigma0 _ _ _)).
forget (rev sigma0 ++ sigma) as sig.
clear - H0 H.
unfold space_denote in *.
simpl in *.
destruct H0 as [s1 [s2 [? [? ?]]]]; exists s1; exists s2; split3; auto.
destruct s,s1,s2; destruct H0 as [[? ?] ?]; simpl in *; subst.
unfold var_eq in H.
repeat rewrite expr_denote_heap_ind with (h:=h0)(h':=h) in *.
rewrite <- H in *.
apply H1.
simpl in H. unfold assertion_denote.
intros s [_ ?].
rewrite space_denote_permute with (l':= rev sigma0 ++ Next e e1 :: sigma); auto.
apply Permutation_sym; apply permute_sigma0.
intros.
destruct H1; try contradiction.
subst Q.
split; auto.
do_fresh.
Qed.

Lemma isolate_Lseg1: forall e e0 e1 sigma nextv nextv2 pnatoms sigma0
  (FRESHe : fresh freshmax_expr e nextv)
  (LT: Ident.lt nextv nextv2),
   entailment_denote
     (Entailment (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
        (Assertion [Equ e e0, Nequ e0 e1] (rev sigma0 ++ Lseg e0 e1 :: sigma))) ->
   fresh freshmax_assertion
     (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma)) nextv ->
   (assertion_denote (Assertion pnatoms (rev sigma0 ++ Lseg e0 e1 :: sigma))
    |-- fold_right (fun P => orp (existsv nextv (assertion_denote P))) FF
          [Assertion pnatoms (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma)]) /\
   (forall Q : assertion,
    In Q
      [Assertion pnatoms (Next e (Var nextv) :: Lseg (Var nextv) e1 :: rev sigma0 ++ sigma)] ->
        match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end /\
    fresh freshmax_assertion Q nextv2).
Proof.
intros.
split.
assert (list_denote pn_atom_denote (@andp _ )
         (space_denote (rev sigma0 ++ Lseg e0 e1 :: sigma)) pnatoms |--
         e===e0 && neg (pn_atom_denote (Equ e0 e1))).
eapply derives_trans; try apply H. intros w [? [? ?]]; split; auto.
clear H.
intros s ?.
generalize (H1 _ H); intros [? ?].
unfold fold_right. unfold orp. left.
eapply Lseg_unfold_neq with e0; auto.
intros.
simpl in H1. destruct H1; try contradiction.
subst.
split; auto.
do_fresh.
Qed.

Lemma isolate'_sound:
  forall e pnatoms sigma nextv nextv2 results
  (LT: Ident.lt nextv nextv2),
      isolate' e pnatoms nil sigma nextv 0 = Some results ->
      fresh freshmax_expr e nextv ->
      fresh freshmax_assertion (Assertion pnatoms sigma) nextv ->
      assertion_denote (Assertion pnatoms sigma) |--
        fold_right (fun P => orp (existsv nextv (assertion_denote P))) FF results /\
      (forall Q, In Q results ->
            match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end /\
           fresh freshmax_assertion Q nextv2).
Proof.
intros until 2. intro FRESHe; intros.
assert (rev nil ++ sigma = sigma) by auto.
remember (@nil space_atom) as sigma0.
rewrite <- H1 in H0|-*.
clear Heqsigma0 H1.
remember O as N. clear HeqN.
revert pnatoms sigma0 results N H H0; induction sigma; intros.

(* nil case *)
rewrite <- app_nil_end in *;
unfold isolate' in H.
apply exorcize_sound; auto.
destruct (lt_dec N 2) as [? | _];  [ inversion H | ].
destruct (incon (Assertion (Equ e Nil :: pnatoms) (rev sigma0))); inversion H; auto.

(* cons case *)
specialize (IHsigma pnatoms (a::sigma0) results).
destruct a.

(* 'Next' case *)
simpl in H.
if_tac in H.
clear IHsigma.
subst e0.
inv H.
apply isolate_Next1; auto.

revert H; case_eq (oracle
          (Entailment
             (Assertion pnatoms (rev sigma0 ++ Next e0 e1 :: sigma))
             (Assertion [Equ e e0] (rev sigma0 ++ Next e0 e1 :: sigma))));
     intros; inv H2; [|clear H].
apply isolate_Next2; auto; apply oracle_sound; auto.

specialize (IHsigma _ H4); clear H4.
destruct IHsigma.
change (rev (Next e0 e1 :: sigma0)) with (rev sigma0 ++ [Next e0 e1]).
rewrite app_ass. apply H0.
split; auto.
eapply derives_trans; try apply H.
simpl.
rewrite app_ass. auto.

(* 'Lseg' case *)
apply isolate_e in H.
destruct H as [[? ?] | [[? ?] | ?]].
clear IHsigma.
subst.
apply isolate_Lseg1; auto.

change (rev (Lseg e0 e1 :: sigma0)) with (rev sigma0 ++ [Lseg e0 e1]) in *.
rewrite app_ass in *.
simpl in *.
apply (IHsigma _ H1); auto.

change (rev (Lseg e0 e1 :: sigma0)) with (rev sigma0 ++ [Lseg e0 e1]) in *.
rewrite app_ass in IHsigma.
apply (IHsigma _ H); auto.
Qed.

Lemma isolate_sound:
  forall e P nextv nextv2 results
      (LT: Ident.lt nextv nextv2),
      isolate e P nextv = Some results ->
       fresh freshmax_expr e nextv ->
       fresh freshmax_assertion P nextv ->
      assertion_denote P |--
        fold_right (fun P => orp (existsv nextv (assertion_denote P))) FF results /\
      forall Q, In Q results ->
            match Q with
           |Assertion _ (Next e0 _ :: _) => e=e0
           | _ => False
           end /\
           fresh freshmax_assertion Q nextv2.
Proof.
unfold isolate; destruct P; intros.
apply isolate'_sound with (nextv2:=nextv2) in H; auto.
Qed.

End Iso_Sound.