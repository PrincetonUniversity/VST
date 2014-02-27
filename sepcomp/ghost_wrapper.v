Require Import ZArith.

Require Import compcert. Import CompcertCommon. Import Mem.

Require Import msl.eq_dec.

Require Import sepcomp.Address. Import Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.forward_simulations. Import Forward_simulation_eq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This module defines a functor of type                                  *)
(*   (sem : CoreSemantics G C mem) ->                                     *)
(*   (ghostsem : CoreSemantics G (C*ghost_state) mem)                     *)
(* where                                                                  *)
(*   ghost_state                                                          *)
(* is a partial function from addresses to some user-supplied type T.     *)
(*                                                                        *)
(* At the end of the file, we prove one possible erasure theorem:         *)
(* that sem simulates ghostsem.                                           *)

Module GHOST. Section ghost.

(* G is the type of global environments                                   *)
(* C is the type of sem "core" states                                     *)

Variables G C : Type.

Variable sem : CoreSemantics G C mem.

(* ghost state is a partial map from address to values of type T *)         

Variable T : Type.

Definition ghost_state := forall (adr : address), option T.

Arguments ghost_state /.

(* States in our extended core semantics are pairs of a 'core' and a      *)
(* ghost map.  It's also possible to pair the ghost state w/ the memories *)
(* instead of w/ the core state.  In the latter case, you end up with a   *)
(* core semantics of type                                                 *)
(*                                                                        *)
(*   CoreSemantics G C (mem*ghost_state)                                  *)
(*                                                                        *)
(* or perhaps more generally                                              *)
(*                                                                        *)
(*   CoreSemantics G C \phi                                               *)
(*                                                                        *)
(* where \phi is related to mem by some projection function \pi.  This    *)
(* second type is similar to what we use in the VST [see files            *)
(* veric/juicy_extspec.v, veric/juicy_mem.v]                              *)

Record state : Type := 
  mk { core :> C
     ; ghost : ghost_state }.

(* convenience operations for updating ghost state *)                       

Definition updC (c : C) (st : state) :=
  match st with
    | mk _ x => mk c x
  end.

Definition updGhost (x : ghost_state) (st : state) :=
  match st with
    | mk c _ => mk c x
  end.

Definition get_ghost (st : state) (adr : address) : option T := ghost st adr.

Definition set_ghost (st : state) (adr : address) (t : T) : state :=
  updGhost (fun adr' => if eq_dec adr adr' then Some t else get_ghost st adr')  st.

(* now, construct a core semantics for states extended w/ ghost data *)     

Definition initial_core ge v vs := 
  match initial_core sem ge v vs with
    | Some c => Some (mk c (fun _ : address => None))
    | None => None
  end.

Definition at_external st := at_external sem (core st).

Arguments at_external /.

Definition after_external ov st :=
  match after_external sem ov (core st) with
    | Some c => Some (mk c (ghost st))
    | None => None
  end.

Arguments at_external /.

Definition halted st := halted sem (core st).

Arguments halted /.

(* Steps in the new operational semantics are either                      *)
(*   1) steps of the old semantics, or                                    *)
(*   2) "ghost" steps -- updates to ghost state of some form.             *)
(*                                                                        *)
(*      Note that we are parametric here in exactly how/when these        *)
(*      updates are performed (that's what the relation R is doing).      *)
(*                                                                        *)
(*      Also, the wellfounded relation [ord] ensures that we don't        *)
(*      take infinitely many ghost transitions all at once in the         *)
(*      ghost semantics.                                                  *)

Variable R : G -> ghost_state -> C -> mem -> ghost_state -> Prop.

Variable ord : ghost_state -> ghost_state -> Prop.

Variable wf_ord : well_founded ord.

Inductive step : G -> state -> mem -> state -> mem -> Prop :=
| normal_step ge x c m c' m' : 
  corestep sem ge c m c' m' -> 
  step ge (mk c x) m (mk c' x) m'

| ghost_step ge x c m x' :
  at_external c = None -> 
  halted c = None -> 
  R ge x c m x' -> 
  ord x' x -> 
  step ge (mk c x) m (mk c x') m.

Program Definition coresem : CoreSemantics G state mem := 
  Build_CoreSemantics _ _ _ 
  initial_core
  at_external 
  after_external 
  halted 
  step
  _ _ _ _.
Next Obligation.
case H. 
intros ? ? ? ? ? ? step; apply corestep_not_at_external in step; auto.
intros ? ? ? ? ?; case c; simpl; auto.
Qed.
Next Obligation.
case H.
intros ? ? ? ? ? ? step; apply corestep_not_halted in step; auto.
intros ? ? ? ? ? ?; case c; simpl; auto.
Qed.
Next Obligation.
case q; intros c x; simpl.
apply (at_external_halted_excl sem c).
Qed.
Next Obligation.
generalize H; case q; intros c x.
unfold after_external.
case_eq (core_semantics.after_external 
  sem retv {| core := c; ghost := x |}); simpl.
intros c' aft; case (after_at_external_excl sem _ _ _ aft).
inversion 1; subst; auto.
intros; congruence.
Qed.

End ghost. End GHOST.

(* One possible erasure theorem -- "sem" simulates "ghostsem". *)          

Section erasure.

(* F, V are the usual CompCert types.                                     *)
(* C is the type of core states of the parameterized semantics [sem].     *)
(* T is the type of ghost states associated w/ each address.              *)

Variables F V C T : Type.

Notation genv := (Genv.t F V).

Variable sem : CoreSemantics genv C mem.

Variable R : genv -> (GHOST.ghost_state T) -> C -> mem -> (GHOST.ghost_state T) -> Prop.

Variable ord : GHOST.ghost_state T -> GHOST.ghost_state T -> Prop.

Variable wf_ord : well_founded ord.

Notation ghostsem := (GHOST.coresem sem R ord).

Definition match_core (st0 : GHOST.ghost_state T) (st : GHOST.state C T) (c : C) := 
  GHOST.ghost st=st0 /\ GHOST.core st=c.

Variable entry_points : list (val*val*signature).
Variable entry_points_hyp : 
  forall v1 v2 sig, 
  List.In (v1,v2,sig) entry_points -> v1=v2.

Variable ge : genv.

Variable after_external_hyp :
  forall c ef sig vals,
  at_external sem c = Some (ef, sig, vals) ->
  forall ret, exists c', after_external sem (Some ret) c = Some c'.

Lemma erasure : Forward_simulation_equals ghostsem sem ge ge entry_points.
Proof.
apply Build_Forward_simulation_equals 
  with (core_data := GHOST.ghost_state T)
       (match_core := match_core)
       (core_ord := ord); auto.

{ apply mem_lemmas.genvs_domain_eq_refl. }

{ intros st1 m st1' m' step d st2 [eq1 eq2]; subst.
  exists (GHOST.core st1'), (GHOST.ghost st1').
  split; auto.
  split; auto.
  inversion step; subst.
  left. simpl in step |- *.
  exists O; hnf.
  solve[exists c', m'; split; simpl; auto].
  right; split; auto.
  solve[exists O; simpl; auto]. }
  
{ intros until sig.
  intros c vals IN init.
  exists (fun _ => None), (GHOST.core c); simpl.
  assert (eq : v1=v2). solve[apply entry_points_hyp with (sig := sig); auto].
  subst v1.
  inversion init. generalize H0. unfold GHOST.initial_core.
  case (initial_core sem ge v2 vals); try congruence.
  intros c'; simpl; inversion 1; subst; simpl.
  split; auto.
  split; auto. }

{ intros until v; intros [].
  case c1; intros c x; simpl; intros -> ->; simpl.
  unfold GHOST.halted; auto. }

{ intros until ef_sig; intros [].
  case st1; intros c x; simpl; intros -> ->; simpl.
  unfold GHOST.at_external; auto. }

{ intros until ef_sig; intros [].
  case st1; intros c x; simpl; intros -> ->; simpl.
  unfold GHOST.after_external; simpl; intros _ atext.
  case (after_external_hyp atext ret); intros st2' aft.
  exists (GHOST.mk st2' d), st2', d.
  rewrite aft.
  split; auto.
  split; auto.
  split; auto. }  
Qed.

End erasure.