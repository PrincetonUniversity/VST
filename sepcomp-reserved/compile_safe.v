Require Import AST.
Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import Events.

Require Import sepcomp.extspec.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.

Definition is_ptr (v: val) := exists b ofs, v = Vptr b ofs.

(* can't define as a fixpoint because there may be cycles *)

Inductive ptr_closure (b: block) (ofs: Z) (m: mem): block -> Z -> Prop :=
| ptr_closure_base: ptr_closure b ofs m b ofs
| ptr_closure_trans: forall b'' ofs'' b' ofs',
  Mem.load Mint32 m b ofs = Some (Vptr b'' ofs'') -> 
  ptr_closure b'' (Int.intval ofs'') m b' ofs' -> 
  ptr_closure b ofs m b' ofs'.

Definition closure (v: val) (m: mem): val -> Prop :=
  fun v': val => match v, v' with 
                   | Vptr b ofs, Vptr b' ofs' => 
                     ptr_closure b (Int.intval ofs) m b' (Int.intval ofs')
                   | _, _ => False
                 end.

Definition val_not_reserved (v: option val) (m: mem) (r: reserve_map) :=
  match v with Some v' => 
    forall b ofs, closure v' m (Vptr b ofs) -> ~r b (Int.intval ofs)
  | None => True
  end.

Lemma val_not_reserved_base: 
  forall b ofs m r,
  val_not_reserved (Some (Vptr b ofs)) m r -> 
  ~r b (Int.intval ofs).
Proof.
intros b ofs m r NR.
hnf in NR.
specialize (NR b ofs).
intros CONTRA.
destruct NR.
solve[econstructor].
solve[auto].
Qed.

Definition reserve_separated1 (r r': reserve_map) m := 
  forall b ofs, ~r b ofs -> r' b ofs -> ~Mem.valid_block m b.

Section compile_safety.
  Context {G C D Z:Type}.
  Context (Hcore:RelyGuaranteeSemantics G C D).
  Variable (Hspec:external_specification mem external_function Z).

  Variable ge : G.

  Fixpoint compile_safeN (n:nat) (z:Z) (r:reserve_map) (c:C) (m:mem) : Prop :=
    match n with
    | O => True
    | S n' => 
       match at_external Hcore c, safely_halted Hcore c with
       | None, None =>
           forall c' m', 
             corestep Hcore ge c m c' m' -> 
             mem_unchanged_on (guarantee_left Hcore r c) m m' /\ 
             compile_safeN n' z r c' m'
       | Some (e,sig,args), None =>
           forall ret m' z' r' c',
             reserve_map_incr r r' -> 
             reserve_separated1 r r' m -> 
             val_not_reserved ret m' r' -> 
             after_external Hcore ret c = Some c' -> 
             compile_safeN n' z' r' c' m'
       | None, Some ret => val_not_reserved (Some ret) m r
       | Some _, Some _ => False
       end
    end.

  Definition corestep_fun  :=
       forall ge m q m1 q1 m2 q2 ,
       corestep Hcore ge q m q1 m1 -> 
       corestep Hcore ge q m q2 m2 -> 
       (q1, m1) = (q2, m2).

  Lemma compile_safe_corestep_forward:
    corestep_fun -> 
    forall c m c' m' n z r,
    corestep Hcore ge c m c' m' -> 
    compile_safeN (S n) z r c m -> 
    compile_safeN n z r c' m'.
  Proof.
    simpl; intros.
    erewrite corestep_not_at_external in H1; eauto.
    erewrite corestep_not_halted in H1; eauto.
    solve[destruct (H1 c' m') as [H2 H3]; auto].
  Qed.

  Lemma compile_safe_downward1 :
    forall n c m z r,
      compile_safeN (S n) z r c m -> compile_safeN n z r c m.
  Proof.
    induction n; simpl; intros; auto.
    destruct (at_external Hcore c);
      destruct (safely_halted Hcore c).
    destruct p; auto.
    destruct p. destruct p.
    intros.
    exploit H; eauto.
    auto.
    intros.
    exploit H; eauto.
    solve[intros [? ?]; auto].
  Qed.

  Lemma compile_safe_downward: 
    forall n n' c m z r,
      le n' n ->
      compile_safeN n z r c m -> compile_safeN n' z r c m.
  Proof.
    do 7 intro. revert c m z r. induction H; auto.
    intros. apply IHle. apply compile_safe_downward1. auto.
  Qed.
    
End compile_safety.
