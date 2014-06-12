Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Inlining.
Require Import Inliningspec.
Require Import RTL.

Require Import mem_lemmas.
Require Import core_semantics.
Require Import sepcomp.reach.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Export Axioms.

Load Santiago_tactics.

(** * Tactic Preamble *)

Ltac dest_own mu b:= 
destruct (locBlocksSrc mu b) eqn:locS, (pubBlocksSrc mu b) eqn:pubS, (extBlocksSrc mu b) eqn:extS, (frgnBlocksSrc mu b) eqn:frgnS, (locBlocksTgt mu b) eqn:locT, (pubBlocksTgt mu b) eqn:pubT, (extBlocksTgt mu b) eqn:extT, (frgnBlocksTgt mu b) eqn:frgnT; simpl; auto.
Ltac dest_own_S mu b:=
let locS := fresh "locS" in 
let pubS := fresh "pubS" in 
let extS := fresh "extS" in 
let frgnS := fresh "frgnS" in 
destruct (locBlocksSrc mu b) eqn:locS, (pubBlocksSrc mu b) eqn:pubS, (extBlocksSrc mu b) eqn:extS, (frgnBlocksSrc mu b) eqn:frgnS; simpl; auto.
Ltac dest_own_T mu b:= 
let locT := fresh "locT" in 
let pubT := fresh "pubT" in 
let extT := fresh "extT" in 
let frgnT := fresh "frgnT" in 
destruct (locBlocksTgt mu b) eqn:locT, (pubBlocksTgt mu b) eqn:pubT, (extBlocksTgt mu b) eqn:extT, (frgnBlocksTgt mu b) eqn:frgnT; simpl; auto.

(*Ill-formed SM_Injections*)
Lemma loc_and_ext_S: forall mu b, SM_wd mu -> locBlocksSrc mu b = true -> extBlocksSrc mu b = true -> False.
intros mu b H locS extS.
destruct H.
specialize ( disjoint_extern_local_Src b).
destruct  disjoint_extern_local_Src; repeat rewriter'; intuition.
Qed.

Lemma pub_not_loc_S: forall mu b, SM_wd mu -> pubBlocksSrc mu b = true -> locBlocksSrc mu b = false -> False.
intros mu b H pubS locS.
destruct H.
apply pubSrcAx in pubS.
destruct pubS as [b2 [z [locof pubT]]]. 
apply local_DomRng in locof; destruct locof.
repeat rewriter'; intuition.
Qed.

Lemma frgn_not_ext_S: forall mu b, SM_wd mu -> frgnBlocksSrc mu b = true -> extBlocksSrc mu b = false -> False.
intros mu b H frgnS extS.
destruct H.
apply frgnSrcAx in frgnS.
destruct frgnS as [b2 [z [extof frgnT]]]. 
apply extern_DomRng in extof; destruct extof.
repeat rewriter'; intuition.
Qed.

Lemma loc_and_ext_T: forall mu b, SM_wd mu -> locBlocksTgt mu b = true -> extBlocksTgt mu b = true -> False.
intros mu b H locT extT.
destruct H.
specialize ( disjoint_extern_local_Tgt b).
destruct  disjoint_extern_local_Tgt; repeat rewriter'; intuition.
Qed.

Lemma pub_not_loc_T: forall mu b, SM_wd mu -> pubBlocksTgt mu b = true -> locBlocksTgt mu b = false -> False.
intros mu b H pubT locT.
destruct H.
apply pubBlocksLocalTgt in pubT; repeat rewriter'; intuition.
Qed.

Lemma frgn_not_ext_T: forall mu b, SM_wd mu -> frgnBlocksTgt mu b = true -> extBlocksTgt mu b = false -> False.
intros mu b H frgnT extT.
destruct H.
apply frgnBlocksExternTgt in frgnT; repeat rewriter'; intuition.
Qed.

Ltac contra:= match goal with
                  | H:False |- _ => contradict H
              end. 
Ltac discr_inj:=
match goal with
    | H1:_, H2:_, H3:_  |- _ => solve [apply (loc_and_ext_S _ _ H1 H2) in H3; eauto; try contra]
    | H1:_, H2:_, H3:_  |- _ => solve [apply (pub_not_loc_S _ _ H1 H2) in H3; eauto; try contra]
    | H1:_, H2:_, H3:_  |- _ => solve [apply (frgn_not_ext_S _ _ H1 H2) in H3; eauto; try contra]
    | H1:_, H2:_, H3:_  |- _ => solve [apply (loc_and_ext_T _ _ H1 H2) in H3; eauto; try contra]
    | H1:_, H2:_, H3:_  |- _ => solve [apply (pub_not_loc_T _ _ H1 H2) in H3; eauto; try contra]
    | H1:_, H2:_, H3:_  |- _ => solve [apply (frgn_not_ext_T _ _ H1 H2) in H3; eauto; try contra]
end.

Ltac discr_inj':=
match goal with
    | H:_ |- _ => solve [eapply loc_and_ext_S in H; eauto]
    | H:_ |- _ => solve [eapply pub_not_loc_S in H; eauto]
    | H:_ |- _ => solve [eapply frgn_not_ext_S in H; eauto]
    | H:_ |- _ => solve [eapply loc_and_ext_T in H; eauto]
    | H:_ |- _ => solve [eapply pub_not_loc_T in H; eauto]
    | H:_ |- _ => solve [eapply frgn_not_ext_T in H; eauto]
end.

Ltac clean:= repeat (try rewriter'; simpl in *).

Ltac dest_inj mu b:= 
destruct (extern_of mu b) eqn:extofb, (local_of mu b) eqn:locofb;
repeat match goal with
    | H: _ = Some ?p |- _ => match p with
                                | (?a, ?b) => fail 1
                                | _ => destruct p
                             end
end; clean;
try match goal with
      |H: _ |- _ => apply H in extofb; destruct extofb
end;
try match goal with
      |H: _ |- _ => apply H in locofb; destruct locofb
end. 


Lemma complete_locS: forall mu b, SM_wd mu -> locBlocksSrc mu b = true ->
locBlocksSrc mu b = true /\ extBlocksSrc mu b = false /\ frgnBlocksSrc mu b = false.
intros. split; auto.
destruct H.
destruct (frgnBlocksSrc mu b) eqn:frgnS; auto.
apply frgnSrcAx in frgnS; destruct frgnS as [? [? [? ?]]];
apply extern_DomRng in H; destruct H; clean; auto.
specialize (disjoint_extern_local_Src b); destruct disjoint_extern_local_Src; clean; auto; discriminate.
specialize (disjoint_extern_local_Src b); destruct disjoint_extern_local_Src; clean; auto; discriminate.
Qed.

Lemma complete_extS: forall mu b, SM_wd mu -> extBlocksSrc mu b = true ->
extBlocksSrc mu b = true /\ locBlocksSrc mu b = false /\ pubBlocksSrc mu b = false.
intros; split; auto.
destruct H.
destruct (pubBlocksSrc mu b) eqn:pubS; auto.
apply pubSrcAx in pubS; destruct pubS as [? [? [? ?]]];
apply local_DomRng in H; destruct H; clean; auto.
specialize (disjoint_extern_local_Src b); destruct disjoint_extern_local_Src; clean; auto; discriminate.
specialize (disjoint_extern_local_Src b); destruct disjoint_extern_local_Src; clean; auto; discriminate.
Qed.

Lemma complete_pubS: forall mu b, SM_wd mu -> pubBlocksSrc mu b = true ->
pubBlocksSrc mu b = true /\ locBlocksSrc mu b = true /\ extBlocksSrc mu b = false /\ frgnBlocksSrc mu b = false.
intros; split; auto.
assert (locS: locBlocksSrc mu b = true).
apply H in H0. destruct H0 as [?[?[? ?]]].
apply H in H0. destruct H0; auto.
descend; auto; apply complete_locS in locS; repeat open_Hyp; clean; auto.
Qed.

Lemma complete_frgnS: forall mu b, SM_wd mu -> frgnBlocksSrc mu b = true ->
frgnBlocksSrc mu b = true /\ extBlocksSrc mu b = true /\ locBlocksSrc mu b = false /\ pubBlocksSrc mu b = false.
intros; split; auto.
assert (extS: extBlocksSrc mu b = true).
apply H in H0. destruct H0 as [?[?[? ?]]].
apply H in H0. destruct H0; auto.
descend; auto; apply complete_extS in extS; repeat open_Hyp; clean; auto.
Qed.

Ltac completeS:= (repeat match goal with
                    |H: _ = true |- _ => apply complete_locS in H; [|solve [assumption]] 
                    |H: _ = true |- _ => apply complete_extS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_pubS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_frgnS in H; [|solve [assumption]]
                 end); repeat open_Hyp.

Lemma complete_locT: forall mu b, SM_wd mu -> locBlocksTgt mu b = true ->
locBlocksTgt mu b = true /\ extBlocksTgt mu b = false /\ frgnBlocksTgt mu b = false.
intros. split; auto.
destruct H.
destruct (frgnBlocksTgt mu b) eqn:frgn; auto.
apply frgnBlocksExternTgt in frgn; clean.
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt; clean; auto; discriminate.
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt; clean; auto; discriminate.
Qed.

Lemma complete_extT: forall mu b, SM_wd mu -> extBlocksTgt mu b = true ->
extBlocksTgt mu b = true /\ locBlocksTgt mu b = false /\ pubBlocksTgt mu b = false.
intros. split; auto.
destruct H.
destruct (pubBlocksTgt mu b) eqn:pub; auto.
apply pubBlocksLocalTgt in pub; clean.
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt; clean; auto; discriminate.
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt; clean; auto; discriminate.
Qed.

Lemma complete_pubT: forall mu b, SM_wd mu -> pubBlocksTgt mu b = true ->
pubBlocksTgt mu b = true /\ locBlocksTgt mu b = true /\ extBlocksTgt mu b = false /\ frgnBlocksTgt mu b = false.
intros; split; auto.
assert (loc: locBlocksTgt mu b = true).
apply H in H0; auto.
descend; auto; apply complete_locT in loc; repeat open_Hyp; clean; auto.
Qed.

Lemma complete_frgnT: forall mu b, SM_wd mu -> frgnBlocksTgt mu b = true ->
frgnBlocksTgt mu b = true /\ extBlocksTgt mu b = true /\ locBlocksTgt mu b = false /\ pubBlocksTgt mu b = false.
intros; split; auto.
assert (ext: extBlocksTgt mu b = true).
apply H in H0; auto.
descend; auto; apply complete_extT in ext; repeat open_Hyp; clean; auto.
Qed.

Ltac completeT:= (repeat match goal with
                    |H: _ = true |- _ => apply complete_locT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_extT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_pubT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_frgnT in H; [|solve [assumption]]
                 end); repeat open_Hyp.


Ltac complete:= (repeat match goal with
                    |H: _ = true |- _ => apply complete_locS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_extS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_pubS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_frgnS in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_locT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_extT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_pubT in H; [|solve [assumption]]
                    |H: _ = true |- _ => apply complete_frgnT in H; [|solve [assumption]]
                 end); repeat open_Hyp.

(** End Of Preamble*)


Inductive Leakage:=
|Undf (*Undefined*)
|Invi (*Invisible*)
|Frgn (*Foreign*) 
|Priv (*Private*)
|Publ (*Public*).


Definition Lleq a b:=
match a, b with
| Publ, Priv => True
| Frgn, Invi => True
| Undf, Undf => True
| Invi, Invi => True
| Frgn, Frgn => True
| Priv, Priv => True
| Publ, Publ => True
| _, _ => False
end.
Infix "<=" := Lleq.

Definition Ldec a b:=
match a, b with
|Undf, Undf => true
|Invi, Invi => true
|Frgn, Frgn => true
|Priv, Priv => true
|Publ, Publ => true
|_, _ => false
end.
Infix "==" := Ldec (at level 80, right associativity).


Ltac Lomega:= first [solve [unfold Lleq; auto] |
                     solve [unfold Ldec; auto]|
                     solve [subst; unfold Lleq; auto]].

Inductive Ownership:=
|Noman
|Local
|External.

Definition Owner leak:= 
match leak with
|Undf => Noman
|Invi => External
|Frgn => External 
|Priv => Local
|Publ => Local
end.

Definition Own_eq l1 l2 := Owner l1 = Owner l2.
Infix "=o" := Own_eq (at level 80, right associativity).

Definition structure:= block -> Leakage.

Definition wd_structure st mem := forall b, ~ Mem.valid_block mem b <-> st b = Undf.


(** *translation*)
Definition locBlocks (st:structure) b:= (st b == Publ) || (st b == Priv).

Definition pubBlocks (st:structure) b:= (st b == Publ).

Definition extBlocks (st:structure) b:= (st b == Invi) || (st b == Frgn).

Definition frgnBlocks (st:structure) b:= (st b == Frgn).

Definition local_restrict (F: meminj) (st: structure):=
  fun b => if locBlocks st b then F b else None.

Definition external_restrict (F: meminj) (st: structure):=
  fun b => if extBlocks st b then F b else None.

Print SM_Injection.
Definition factor (F: meminj) (st1 st2: structure) :=
  Build_SM_Injection
    (locBlocks st1)
    (locBlocks st2)
    (pubBlocks st1)
    (pubBlocks st2)
    (local_restrict F st1)
    (extBlocks st1)
    (extBlocks st2)
    (frgnBlocks st1)
    (frgnBlocks st2)
    (external_restrict F st1).

Definition SM2structure1 (mu: SM_Injection):=
  match mu with 
    Build_SM_Injection locS _ pubS _ _ extS _ frgnS _ _ => 
    fun b => 
      match (locS b, pubS b, extS b, frgnS b) with
          | (true, true, false, false) => Publ
          | (true, false, false, false) => Priv
          | (false, false, true, true) => Frgn
          | (false, false, true, false) => Invi
          | _ => Undf
      end
  end.

Definition SM2structure2 (mu: SM_Injection):=
  match mu with 
    Build_SM_Injection _ locT _ pubT _ _ extT _ frgnT _ => 
    fun b => 
      match (locT b, pubT b, extT b, frgnT b) with
          | (true, true, false, false) => Publ
          | (true, false, false, false) => Priv
          | (false, false, true, true) => Frgn
          | (false, false, true, false) => Invi
          | _ => Undf
      end
  end.

Definition de_factor (mu:SM_Injection):=
  (SM2structure1 mu, SM2structure2 mu, as_inj mu).

Print SM_wd.
(** *Well-formedness *)
Record inj_wd (F:meminj) (st1 st2: structure) := Build_inj_wd
{ non_decreasing_ownership: forall b1 b2 z, F b1 = Some (b2, z) -> st2 b2 <= st1 b1;
  public_axiom: forall b1, st1 b1 = Publ -> exists b2 z, F b1 = Some( b2, z);
  foreign_axiom: forall b1, st1 b1 = Frgn -> exists b2 z, F b1 = Some( b2, z);
  undefined_axiom: forall b1, st1 b1 = Undf -> F b1 = None}.


(** *Equivalence* *)
Print SM_wd.
Lemma factor_wd : forall F st1 st2, inj_wd F st1 st2 -> SM_wd (factor F st1 st2).
intros.
destruct H; unfold factor, local_restrict, external_restrict, locBlocks, pubBlocks, extBlocks, frgnBlocks.
apply Build_SM_wd; intros; simpl in *.

(*disjoint_extern_local_Src*)
destruct (st1 b); auto.
(*disjoint_extern_local_Tgt*)
destruct (st2 b); auto.
(*local_DomRng*)
destruct (st1 b1) eqn:st1b1; simpl in *; try discriminate;
apply non_decreasing_ownership0 in H; destruct (st2 b2); clean; try contra; auto.
(*extern_DomRng*)
destruct (st1 b1) eqn:st1b1; simpl in *; try discriminate;
apply non_decreasing_ownership0 in H; destruct (st2 b2); clean; try contra; auto.
(* pubSrcAx*)
destruct (st1 b1) eqn:st1b1; try discriminate.  
assert (st1b1':=st1b1);
apply public_axiom0 in st1b1'.
destruct st1b1' as [b2 [z smthng]].
exists b2, z; simpl. split; auto.
apply non_decreasing_ownership0 in smthng. clean.
destruct (st2 b2); try discriminate; auto.
(*frgnSrcAx*)
destruct (st1 b1) eqn:st1b1; try discriminate.  
assert (st1b1':=st1b1);
apply foreign_axiom0 in st1b1'.
destruct st1b1' as [b2 [z smthng]].
exists b2, z; simpl. split; auto.
apply non_decreasing_ownership0 in smthng. clean.
destruct (st2 b2); try discriminate; auto.
(*pubBlocksLocalTgt*)
destruct (st2 b); try discriminate; auto.
(*frgnBlocksExternTgt*)
destruct (st2 b); try discriminate; auto.
Qed.

Lemma de_factor_wd : forall mu, SM_wd mu ->
let (st, F) := de_factor mu in let (st1, st2) := st in
inj_wd F st1 st2.
unfold de_factor, as_inj, join. (*SM2structure1, SM2structure2.*)
intros; apply Build_inj_wd; simpl; intros.
(*non_decreasing_ownership*)
destruct (extern_of mu b1) eqn:extof; try destruct p;
destruct (local_of mu b1) eqn:locof; try destruct p; inv H0;
assert (extof':=extof); assert (locof':=locof);
try apply H in extof'; try apply H in locof'; repeat open_Hyp; clean; auto; complete; clean; try discriminate.
destruct (frgnBlocksTgt mu b2) eqn:loc2, (frgnBlocksSrc mu b1) eqn:loc1; complete; clean; try discriminate; try solve[destruct mu; clean; auto]. 
apply H in H6. destruct H6 as [?[?[? ?]]]. complete; clean. inv extof; clean; discriminate.
destruct (pubBlocksTgt mu b2) eqn:pub2, (pubBlocksSrc mu b1) eqn:pub1; complete; clean; try discriminate; try solve[destruct mu; clean; auto]. 
apply H in H6. destruct H6 as [?[?[? ?]]]. complete; clean. inv locof; clean; discriminate.

Print inj_wd.
(*public_axiom*)
destruct (extern_of mu b1) eqn:extof; try destruct p;
destruct (local_of mu b1) eqn:locof; try destruct p; inv H0;
assert (extof':=extof); assert (locof':=locof);
try apply H in extof'; try apply H in locof'; repeat open_Hyp; clean; auto; complete; clean; try discriminate.
exists b, z; auto.
exists b, z; auto.
destruct (pubBlocksSrc mu b1) eqn:pubS; complete. 
apply H in H0; destruct H0 as [?[?[? ?]]]. clean; discriminate.
dest_own_S mu b1; destruct mu; clean; try discriminate.

(*foreign_axiom*)
destruct (extern_of mu b1) eqn:extof; try destruct p;
destruct (local_of mu b1) eqn:locof; try destruct p; inv H0;
assert (extof':=extof); assert (locof':=locof);
try apply H in extof'; try apply H in locof'; repeat open_Hyp; clean; auto; complete; clean; try discriminate.
exists b, z; auto.
exists b, z; auto.
destruct (frgnBlocksSrc mu b1) eqn:frgnS; complete. 
apply H in H0; destruct H0 as [?[?[? ?]]]. clean; discriminate.
dest_own_S mu b1; destruct mu; clean; try discriminate.

(*undefined_axiom*)
destruct (extern_of mu b1) eqn:extof; try destruct p;
destruct (local_of mu b1) eqn:locof; try destruct p; inv H0;
assert (extof':=extof); assert (locof':=locof);
try apply H in extof'; try apply H in locof'; repeat open_Hyp; clean; auto; complete; clean; try discriminate.
dest_own_S mu b1; clean; try discriminate;
destruct mu; clean; discriminate.

dest_own_S mu b1; clean; try discriminate;
destruct mu; clean; discriminate.
Qed.

Lemma factor_roundworld : forall F st1 st2, inj_wd F st1 st2 -> de_factor (factor F st1 st2) = (st1, st2, F).
  intros.
  unfold de_factor. repeat f_equal.
  (*SM2structure1*)
  unfold SM2structure1.
  unfold factor.
  extensionality b.
  unfold locBlocks, pubBlocks, extBlocks, frgnBlocks.
  destruct (st1 b) eqn:st1_b; auto.
  (*SM2structure2*)
  unfold SM2structure2.
  unfold factor.
  extensionality b.
  unfold locBlocks, pubBlocks, extBlocks, frgnBlocks.
  destruct (st2 b) eqn:st2_b; auto.
  (*as_inj *)
  unfold factor.
  unfold as_inj; simpl.
  unfold join.
  unfold join, external_restrict, local_restrict.
  extensionality b.
  unfold extBlocks, locBlocks.
  destruct (st1 b) eqn:st1_b; try (solve [ 
  destruct (F b); intuition]).
  destruct H.
  rewrite undefined_axiom0; auto.
Qed.

Lemma de_factor_roundworld : forall mu, SM_wd mu ->
let (st, mu') := de_factor mu in let (st1, st2) := st in
                                                                         (factor mu' st1 st2 = mu).

intros mu H.
unfold de_factor, factor, local_restrict, external_restrict, SM2structure1, SM2structure2, locBlocks, pubBlocks, extBlocks, frgnBlocks, as_inj, join.

destruct mu eqn:mu_eq; simpl in *; f_equal; extensionality b; simpl.
dest_own_S mu b; clean; auto; discr_inj.
dest_own_T mu b; clean; auto; discr_inj.
dest_own_S mu b; clean; auto; discr_inj.
dest_own_T mu b; clean; auto; discr_inj.

(*local_of*)
dest_own_S mu b; clean; try discr_inj;
destruct H; clean;
dest_inj mu b; clean; intuition.

dest_own_S mu b; clean; auto; discr_inj.
dest_own_T mu b; clean; auto; discr_inj.
dest_own_S mu b; clean; auto; discr_inj.
dest_own_T mu b; clean; auto; discr_inj.

(*extern_of*)
dest_own_S mu b; clean; try discr_inj;
destruct H; clean;
dest_inj mu b; clean; intuition.
Qed.

(** *locAllocated *)

Print sm_locally_allocated.
(* This definition is too strong but beautiful *)
Definition st_nonalloc_step (st st':structure) m m':= forall b, (freshloc m m' b = false) -> st' b =o st b.
Definition st_alloc_step (st':structure) m m':= forall b, (freshloc m m' b = true) -> st' b <= Priv.
Definition st_locally_allocated (st st':structure) m m':= st_nonalloc_step st st' m m' /\ st_alloc_step st' m m'.


Lemma locAllocated_equiv2: forall mu mu' m1 m2 m1' m2', 
SM_wd mu ->
SM_wd mu'->
sm_locally_allocated mu mu' m1 m2 m1' m2'->
let (st, F) := de_factor mu in let (st1, st2) := st in
let (st', F') := de_factor mu' in let (st1', st2') := st' in
st_locally_allocated st1 st1' m1 m1' /\
st_locally_allocated st2 st2' m2 m2'.

unfold de_factor, st_locally_allocated, st_nonalloc_step, st_alloc_step; intros; descend;
unfold sm_locally_allocated in H1;
destruct mu eqn:mu_eq; destruct mu' eqn:mu'_eq; simpl in H1; repeat open_Hyp;
clean.
rewrite orb_false_r;
assert (locBlocksSrc0 b = locBlocksSrc b) by (repeat rewriter; rewrite orb_false_r; auto);
destruct (locBlocksSrc b) eqn:locS; clean;
destruct (pubBlocksSrc b) eqn:pubS; clean;
destruct (extBlocksSrc b) eqn:extS; clean;
destruct (frgnBlocksSrc b) eqn:frgnS; clean; auto;
destruct (pubBlocksSrc0 b) eqn:pubS0, (frgnBlocksSrc0 b) eqn:frgnS0; clean; 
unfold Own_eq; auto; try discr_inj; try
(apply  H0 in pubS0; simpl in pubS0;
destruct pubS0 as [? [? [H7 H8]]];
apply H0 in H7; simpl in H7; destruct H7; clean; inv H7).

rewrite orb_true_r;
assert (locBlocksSrc0 b = true) by (repeat rewriter; rewrite orb_true_r; auto);
destruct (locBlocksSrc b) eqn:locS; clean;
destruct (pubBlocksSrc b) eqn:pubS; clean;
destruct (extBlocksSrc b) eqn:extS; clean;
destruct (frgnBlocksSrc b) eqn:frgnS; clean; auto;
destruct (pubBlocksSrc0 b) eqn:pubS0, (frgnBlocksSrc0 b) eqn:frgnS0; clean; 
unfold Lleq; auto; try discr_inj; try (
destruct H0; clean;
specialize (disjoint_extern_local_Src b); destruct disjoint_extern_local_Src as [H10 | H10]; clean; inv H10).

rewrite orb_false_r.
assert (locBlocksTgt0 b = locBlocksTgt b) by (repeat rewriter; rewrite orb_false_r; auto).
destruct (locBlocksTgt b) eqn:locT; clean;
destruct (pubBlocksTgt b) eqn:pubT; clean;
destruct (extBlocksTgt b) eqn:extT; clean;
destruct (frgnBlocksTgt b) eqn:frgnT; clean; auto;
destruct (pubBlocksTgt0 b) eqn:pubT0, (frgnBlocksTgt0 b) eqn:frgnT0; clean; 
unfold Own_eq; auto; try discr_inj. 
apply H0 in pubT0; simpl in pubT0; clean; inv pubT0.
apply H0 in pubT0; simpl in pubT0; clean; inv pubT0.
apply H0 in pubT0; simpl in pubT0; clean; inv pubT0.
apply H0 in pubT0; simpl in pubT0; clean; inv pubT0.

rewrite orb_true_r;
assert (locBlocksTgt0 b = true) by (repeat rewriter; rewrite orb_true_r; auto);
destruct (locBlocksTgt b) eqn:locT; clean;
destruct (pubBlocksTgt b) eqn:pubT; clean;
destruct (extBlocksTgt b) eqn:extT; clean;
destruct (frgnBlocksTgt b) eqn:frgnT; clean; auto;
destruct (pubBlocksTgt0 b) eqn:pubT0, (frgnBlocksTgt0 b) eqn:frgnT0; clean; 
unfold Lleq; auto; try discr_inj.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
destruct H0; clean;
specialize (disjoint_extern_local_Tgt b); destruct disjoint_extern_local_Tgt as [H10 | H10]; clean; inv H10.
Qed.




Lemma locAllocated_equiv1: forall F st1 st2 F' st1' st2' m1 m2 m1' m2', 
inj_wd F st1 st2 ->
wd_structure st1 m1 ->
wd_structure st2 m2 ->
inj_wd F' st1' st2'->
wd_structure st1' m1' ->
wd_structure st2' m2' ->
st_locally_allocated st1 st1' m1 m1' ->
st_locally_allocated st2 st2' m2 m2' ->
sm_locally_allocated (factor F st1 st2) (factor F' st1' st2') m1 m2 m1' m2'.

intros. unfold sm_locally_allocated.
unfold factor, locBlocks, extBlocks; descend; extensionality b.
destruct (freshloc m1 m1' b) eqn:fresh; simpl;
match goal with
    |H:_ |- _ => apply H in fresh
end.
destruct (st1' b); clean; first [ contra | repeat rewrite orb_true_r; auto].
destruct (st1 b), (st1' b); unfold Own_eq in *; clean; first [discriminate | auto].

destruct (freshloc m2 m2' b) eqn:fresh; simpl;
match goal with
    |H:_ |- _ => apply H in fresh
end.
destruct (st2' b); clean; first [ contra | repeat rewrite orb_true_r; auto].
destruct (st2 b), (st2' b); clean; first [discriminate | auto].

destruct (freshloc m1 m1' b) eqn:fresh; simpl;
assert (fresh':= fresh);
match goal with
    |H:_ |- _ => apply H in fresh
end.
apply andb_true_iff in fresh'; destruct fresh'.
destruct (valid_block_dec m1 b) as [true | false]; simpl in H8; inv H8;
apply H0 in false; rewrite false; rewrite orb_false_r; auto.
destruct (st1' b); clean; try contra; unfold Ldec; auto.
destruct (st1 b), (st1' b); clean; first [discriminate | auto].

destruct (freshloc m2 m2' b) eqn:fresh; simpl;
assert (fresh':= fresh);
match goal with
    |H:_ |- _ => apply H in fresh
end.
apply andb_true_iff in fresh'; destruct fresh'.
destruct (valid_block_dec m2 b) as [true | false]; simpl in H8; inv H8;
apply H1 in false; rewrite false; rewrite orb_false_r; auto.
destruct (st2' b); clean; try contra; auto.
destruct (st2 b), (st2' b); clean; first [discriminate | auto].
Qed.

Print SM_wd.
Print wd_structure.
Print sm_locally_allocated.

(** *Separated *)
Print sm_inject_separated.
Definition st_separated (F F': meminj) (st1 st2: structure):= 
(forall (b1 b2: block) z,
   F b1 = None ->
   F' b1 = Some (b2, z) ->
   st1 b1 = Undf /\ st2 b2 = Undf).

Lemma separated_equiv2: forall mu mu' m1 m2,
SM_wd mu ->
sm_inject_separated mu mu' m1 m2 ->
let (st, F) := de_factor mu in 
let (st1, st2) := st in
let (st', F') := de_factor mu' in 
let (st1', st2') := st in
st_separated F F' st1 st2.
unfold de_factor, SM2structure1, SM2structure2, st_separated; intros.
unfold sm_inject_separated in H;
repeat open_Hyp.
apply H0 in H2; auto; destruct H2 as [DS DT].
unfold DomSrc, DomTgt in *.
apply orb_false_iff in DS; apply orb_false_iff in DT.
repeat open_Hyp. 
destruct (pubBlocksSrc mu b1) eqn:pubS; complete; clean; try discriminate.
destruct (pubBlocksTgt mu b2) eqn:pubT; complete; clean; try discriminate.
destruct mu; clean; auto.
Qed.

Lemma separated_equiv1: forall F F' st1 st2 st1' st2' m1 m2,
inj_wd F st1 st2 ->
wd_structure st1 m1 ->
wd_structure st2 m2 ->
st_separated F F' st1 st2 ->
let mu := factor F st1 st2 in 
let mu' := factor F' st1' st2' in
sm_inject_separated mu mu' m1 m2.
unfold factor, sm_inject_separated, as_inj, join, extern_of, local_of, DomSrc, DomTgt, external_restrict, local_restrict, locBlocks, extBlocks; descend; simpl in *; intros.

destruct (st1 b1) eqn:st1b1; clean; auto;
destruct (st1' b1) eqn:st1'b1; clean; auto; inv H4;
destruct (F b1) eqn:Fb1; try destruct p; clean; inv H3;
destruct (F' b1) eqn:F'b1; try destruct p; clean; inv H6;
apply H2 in F'b1; auto; repeat open_Hyp; clean; try discriminate.

destruct (st1 b1) eqn:st1b1, (F b1) eqn:Fb1; try destruct p; clean; auto; try discriminate; try 
(apply H in st1b1; clean; discriminate);
destruct (st1' b1) eqn:st1'b1, (F' b1) eqn:F'b1; try destruct p; clean; auto; try discriminate;
inv H4;
apply H2 in F'b1; repeat open_Hyp; clean; auto.

apply H0.
destruct (st1 b1); auto; clean; try discriminate.

apply H1.
destruct (st2 b2); auto; clean; try discriminate.

Qed.
