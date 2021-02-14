Set Implicit Arguments.

Require Import FCF.FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import FCF.RndInList.
Require Import FCF.HasDups.
Require Import FCF.CompFold.
Require Import FCF.PRF.
Require Import FCF.OracleHybrid.
Require Import List.
Require Import hmacdrbg.PRF_DRBG.        (* note: had to move PRF_DRBG into FCF dir for this *)
Require Import Coq.Program.Wf.
Require Import FCF.OracleCompFold.
Require Import Permutation.
Require Import FCF.Tactics.
Require Import hmacdrbg.map_swap.        (* TODO move to top *)
Require Import FCF.RndInList.
Require Import Lia.

(* Shortcuts for FCF tactics *)
(* TODO remove / inline these *)
Ltac fs := fcf_simp.
Ltac fif := fcf_inline_first.
Ltac s := simpl.
Ltac fsr := fcf_spec_ret.
Ltac fskip := fcf_skip.
Ltac simplify :=
  repeat (try simpl; try fcf_inline_first; try fcf_simp).

Ltac rewrite_r := apply comp_spec_symm; eapply comp_spec_eq_trans_l.
Ltac flip := apply comp_spec_symm.
Ltac prog_equiv := repeat (simplify; fcf_skip_eq); try simplify.

Ltac bv_exist := try apply oneVector.

(* Lemma demonstrating use of `bv_exist` ltac *)
Lemma fcf_skip_admits : forall (n m : nat),
  comp_spec eq
            (x <-$ {0,1}^n;
             ret x)
            (y <-$ {0,1}^n;
             z <-$ {0,1}^n;
             ret y).
Proof.
  intros.
  (* Set Printing All. *)
  simpl.
  fcf_skip; bv_exist.
  fcf_irr_r.
Qed.

(* TODO:

- Blist definitions X
- New for PRF-DRBG etc functions (instantiate, generate, update) X
- Make the correct oracles X
- Fill in the oracles with functions X

- Write the initial game and final game X
- Write the game i X
- Construct PRF adversary X
- Write the theorem statements (final theorem, inductive hypothesis) X

- Prove equivalence of the new Generate_v oracle outputs (moving re-sampling v) to old Generate_v oracle outputs X
- Apply the hybrid argument in G1_G2_close and make sure that theorem can be proven with Gi_adjacent_hybrids_close X
- Move my proof to a separate file? or review it X
- Comment the uncommented games X

- Figure out what's going on with PRF advantage X
- Look at OracleMapHybrid (X)

- Write out all subgames (e.g. involving random functions) X
- Review step 4 and OracleHybrid proofs (X)
- Remove unneeded Generate_v*_oc versions

- Prove G1 = Gi 0 and G2 = Gi q
- Prove Gi_prf (S i) = Gi_prg i
- Prove PRF advantage theorems
- Prove the theorems: (figure out what the main lemmas and difficulties are)
  - Pr[Collisions] = ? (for n+1 calls)
  - Apply Adam's argument

- Prove other things (well-formedness, etc. -- the hypotheses)
  - Deal with actual Instantiate (not just RB)
- Add backtracking resistance and prove that 
- Change to adaptive adversary?? (additional input, etc.)
*)

Local Open Scope list_scope.
Local Opaque evalDist.

(* --- Begin my HMAC-DRBG spec --- *)
Section PRG.

  (* note: the domain of the f is now Blist, not an abstract D
the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)

Variable eta : nat.
Variable (*Hypothesis*) eta_nonzero : eta <> 0%nat.

Definition RndK : Comp (Bvector eta) := {0,1}^eta.
Definition RndV : Comp (Bvector eta) := {0,1}^eta.

Ltac kv_exist := try apply (oneVector eta, oneVector eta).

Variable f : Bvector eta -> Blist -> Bvector eta.

Definition KV : Set := (Bvector eta * Bvector eta)%type.
Variable eqDecState : EqDec KV.
(* Variable eqdbv : EqDec (Bvector eta). *)
Definition eqdbv := Bvector_EqDec eta.
(* Variable eqdbl : EqDec Blist. *)
Definition eqdbl := list_EqDec bool_EqDec.
(* Opaque eqdbl. *)

(* injection is to_list. TODO prove this *)
Definition injD : Bvector eta -> Blist := Vector.to_list.
Lemma injD_correct r1 r2: injD r1 = injD r2 -> r1 = r2.
Proof. apply to_list_eq_inv. Qed.

Definition to_list (A : Type) (n : nat) (v : Vector.t A n) := Vector.to_list v.

(* PRG functions *)

(* TODO does not reflect NIST spec *)
Definition Instantiate : Comp KV :=
  k <-$ RndK;
  v <-$ RndV;
  ret (k, v).

Lemma wf_instantiate : well_formed_comp Instantiate.
Proof. unfold Instantiate. fcf_well_formed. unfold RndK. fcf_well_formed.
       unfold RndV. fcf_well_formed. Qed.
Ltac wfi := apply wf_instantiate.
(*
Print Comp.
SearchAbout Comp.
Locate "<-$". *)

(* save the last v and output it as part of the state *)
Fixpoint Gen_loop (k : Bvector eta) (v : Bvector eta) (n : nat)
  : list (Bvector eta) * Bvector eta :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k (to_list v) in
    let (bits, v'') := Gen_loop k v' n' in
    (v' :: bits, v'')           (* TODO change mine from (v ::) to (v ++), *or* prove indistinguishable (add another game in the beginning) *)
  end.

Theorem Gen_loop_test : forall k v, Gen_loop k v 3 =    (f k (to_list v)
    :: f k (to_list (f k (to_list v)))
       :: f k (to_list (f k (to_list (f k (to_list v))))) :: nil,
   f k (to_list (f k (to_list (f k (to_list v)))))).
Proof.
  reflexivity.
Qed.

(* Generate + Update *)
(* This has oracle type:
state: k, v
input: n
output: list (Bvector eta)
state: k, v *)

(* Spec says "V || 0x00"; here we will use a list of 8 bits of 0 (a byte) *)
Fixpoint replicate {A} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Definition zeroes : list bool := replicate 8 false.

(* oracle 1 *)

(* do not use; here as reference implementation so we can prove 
[Generate, Generate, ...] = [Generate_noV, Generate_v, Genupdate, ...] *)
Definition Generate (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  v'' <- f k' (to_list v');
  ret (bits, (k', v'')).

(* want to change to this, and prove the outputs are the same. 
the other Generate_vs don't use this version *)
Definition Generate_v (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  ret (bits, (k', v'')).

(* use this for the first call *)
Definition Generate_noV (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  ret (bits, (k', v')).

(* --- End my HMAC-DRBG spec --- *)
(* well, this doesn't include the "sequence of executions" business, which happens in the games *)

(* oracle 2: all PRFs replaced with random bits *)
(* TODO: intermediate oracles, each with random functions *)

(* intermediates have unnecessary state and updating of the state to match earlier ones *)
Fixpoint Gen_loop_rb_intermediate (k : Bvector eta) (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n';
    ret (v' :: bits, v'')
  end.

(* final versions (without unnecessary (k, v) updating) *)
Fixpoint Gen_loop_rb (n : nat) : Comp (list (Bvector eta)) :=
  match n with
  | O => ret nil
  | S n' =>
    v' <-$ {0,1}^eta;
    bits <-$ Gen_loop_rb n';
    ret (v' :: bits)
  end.

(* passes the state around to match the types in Oi_oc' *)
(* Old version: did not update v *)
(* Definition Generate_rb_intermediate (state : KV) (n : nat) *)
(*   : Comp (list (Bvector eta) * KV) := *)
(*   bits <-$ Gen_loop_rb n; *)
(*   ret (bits, state). *)

(* New version: updates state vector v to be the last element of bits. Doesn't matter b/c all bits sampled randomly unless n=0 *)
(* New new version: exactly like Generate_v but with f replaced by uniform random sampling *)
(* needs this for the proof of Gi_prog_equiv_rb_oracle *)
Definition Generate_rb_intermediate (state : KV) (n : nat)
  : Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <-$ {0,1}^eta;
  [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n;
  ret (bits, (k, v'')).

Definition Generate_rb_oracle (tt : unit) (n : nat) : Comp (list (Bvector eta) * unit) :=
  bits <-$ Gen_loop_rb n;
  ret (bits, tt).

Definition Generate_rb (n : nat) : Comp (list (Bvector eta)) :=
  bits <-$ Gen_loop_rb n;
  ret bits.

(* TODO: prove well_formed for the oracles *)

(* Non-adaptive adversary. Consequently, does not use OracleComp, because it won't be adjusting its input to the Generate_v oracle (number of blocks requested from Gen_loop) based on the Generate_v oracle's output, because the number of blocks and queries is fixed. *)
Variable A : list (list (Bvector eta)) -> Comp bool.
Hypothesis A_wf : forall ls, well_formed_comp (A ls).

Variable blocksPerCall : nat.       (* blocks generated by GenLoop *)
Variable numCalls : nat.        (* number of calls to Generate_v *)
Variable (*Hypothesis*) H_numCalls : numCalls > 0. (* need this for Generate_v equivalence? *)
Variable (*Hypothesis*) H_blocksPerCall : blocksPerCall > 0.
(* need this hypothesis in oracle-to-RB (oracleMap_oracleCompMap_equiv_modified_calls_gt_i)
and collision bound (Gi_rb_collisions_inner_eq_general_i_eq0) *)
(* TODO do casework on whether blocksPerCall = 0 *)

Definition requestList : list nat := replicate numCalls blocksPerCall.

(* Change to an abstract, nonempty list. *)
(* TODO: change name *)
(* Parameter firstCall : nat. *)
(* Parameter blocksForCalls_2 : list nat. *)
(* Definition requestList : list nat := firstCall :: blocksForCalls_2. *)
(* used with oracleMap: call the oracle numCalls times, each time requesting blocksPerCall blocks *)

(* only first call uses Generate_noV; assumes numCalls > 0 *)
Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ Generate_v state' (tail requestList);
  A (head_bits :: tail_bits).

(* TODO: backtracking resistance? for nonadaptive adversary *)
(* Definition G1_prg_br : Comp bool :=
  blocksForEachCall <- A1; (* implicitly compromises after that # calls *)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate_noV (k, v) (head blocksForEachCall);
  [tail_bits, state''] <-$2 oracleMap _ _ Generate_v state' (tail blocksForEachCall);
  [k', v'] <-$ UpdateV state'';
  A2 (head_bits :: tail_bits, (k', v')). *)

(* rand bits *)
(* Definition G_ideal_br : Comp bool :=
  blocksForEachCall <- A1;
  [bits, state'] <-$2 oracleMap _ _ Generate_rb (k, v) blocksPerCall;
  k <- {0,1}^eta;
  v <- {0,1}^eta;
  A2 (head_bits :: tail_bits, (k, v)). *)

(* --------------------- *)
(* Prove v-update move equivalence *)

(* calling (Generate, Generate, ...) should have the same output
as calling (Generate_noV, Generate_v, Generate_v, ...) which moves the v-update to the beginning of the next oracle call *)
(* proof outline: G_real = G_real_split ~ G1_prg *)

Definition G_real : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ Generate (k, v) requestList;
  A bits.

(* make the form closer to G1_prg by splitting off first call only *)
Definition G_real_split : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ Generate state' (tail requestList);
  A (head_bits :: tail_bits).

(* use version that's better for induction *)

(* oracleMap hardcodes acc for compFold as nil, so generalize it *)
Theorem compFold_acc : forall numCalls0 bits acc state,
   comp_spec
     (fun x y : list (list (Bvector eta)) * KV =>
      hd_error (fst x) = Some bits /\ tl (fst x) = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (bits :: acc, state) (replicate numCalls0 blocksPerCall))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc, state) (replicate numCalls0 blocksPerCall)).
Proof.
  intros. revert bits acc state.
  induction numCalls0; intros.

  - simpl. fcf_spec_ret.
  - simpl.
    fcf_inline_first. fcf_skip.
    remember a0 as bits1. remember b as state'. clear Heqbits1 Heqstate'.
    fcf_simp.
    apply IHnumCalls0.
Qed.

(* do first call of map separately *)
Theorem Generate_v_split_close :
  Pr[G_real] == Pr[G_real_split].
Proof.
  unfold G_real, G_real_split.
  unfold requestList.
  destruct numCalls as [ | numCalls'].
  * inversion H_numCalls.
  * Opaque Generate. 
    simpl.
    fcf_to_prhl_eq.
    fcf_skip.
    fcf_simp.
    remember b as k. remember b0 as v. clear Heqk Heqv.
    remember (replicate numCalls' blocksPerCall) as requestList'.

    unfold oracleMap. simpl.
    fcf_inline_first.
    fcf_skip.
    Opaque getSupport. simpl in *.
    remember a0 as bits. remember b1 as state'. clear Heqbits Heqstate'.

    fcf_skip.
    instantiate (1 := (fun x y => hd_error (fst x) = Some bits /\ tail (fst x) = fst y)).
    - apply compFold_acc.
    - fcf_simp. simpl in H5. inversion H5. clear H5. destruct a1. inversion H6. simpl in *. inversion H6. subst. fcf_reflexivity.
      Transparent Generate.
Qed.

(* generalize acc again. could be generalized further for the function on v but oh well *)
Theorem comp_spec_acc_2 : forall numCalls0 acc k v,
 comp_spec (fun x y : list (list (Bvector eta)) * KV => fst x = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc,
        (k, f k (to_list v)))
        (replicate numCalls0 blocksPerCall))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_v s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc, (k, v))
        (replicate numCalls0 blocksPerCall)).
Proof.
  intros.
  revert v k acc. induction numCalls0 as [ | numCalls0']; intros.
  * simpl. fcf_spec_ret.
  * simpl.
    fcf_inline_first. fcf_simp. apply IHnumCalls0'.
Qed.

(* G_real: calls Generate, then Generate
G1_prg: uses Generate_noV, then Generate_v (v moved) *)
Theorem Generate_move_v_update :
  Pr[G_real] == Pr[G1_prg].
Proof.
  rewrite Generate_v_split_close.
  unfold G_real_split, G1_prg.
  fcf_to_prhl_eq.
  fcf_skip.
  fcf_simp.
  remember b as k. remember b0 as v. clear Heqk Heqv.
  simpl.
  fcf_inline_first.
  fcf_simp.
  remember (to_list b1 ++ zeroes) as v1_pad.
  unfold requestList.

  destruct numCalls as [ | numCalls'].

  * inversion H_numCalls.
  * simpl.
    fcf_skip.
    instantiate (1 := (fun x y => fst x = fst y)).
    unfold oracleMap.

    - apply comp_spec_acc_2.

    - fcf_simp. simpl in *. subst. fcf_reflexivity.
Qed.

(* End proofs of v-update equivalence *)
(* ------------------------------------------------ *)

(* TODO: intermediate games with random functions and random bits *)

(* proving Pr[G_ideal'] == Pr[G_ideal''] could be hard (new intermediate game) *)

Definition G_ideal'' : Comp bool :=
  kv <-$ Instantiate;           (* OK to instantiate them? *)
  [bits, _] <-$2 oracleMap _ _ Generate_rb_intermediate kv requestList;
  A bits.

(* uses simplified RB versions *)
Definition G_ideal' : Comp bool :=
  [bits, _] <-$2 oracleMap _ _ Generate_rb_oracle tt requestList;
  A bits.

(* simpler version of Generate_v only requires compMap. prove the two games equivalent *)
Definition G_ideal : Comp bool :=
  bits <-$ compMap _ Generate_rb requestList;
  A bits.

(* oracle i *)
(* number of calls: first call is 0, last call is (numCalls - 1) for numCalls calls total
G0: PRF PRF PRF
G1: RB  PRF PRF
G2: RB  RB  PRF
G3: RB  RB  RB 
there should be (S numCalls) games, so games are numbered from 0 through numCalls *)
Definition choose_Generate (i : nat) (sn : nat * KV) (n : nat)
  : Comp (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let Generate_v_choose := if lt_dec callsSoFar i (* callsSoFar < i (override all else) *)
                          then Generate_rb_intermediate
                          (* first call does not update v, to make proving equiv. easier*)
                          else if beq_nat callsSoFar O then Generate_noV
                          else Generate_v in
  (* note: have to use intermediate, not final Generate_rb here *)
  [bits, state'] <-$2 Generate_v_choose state n;
  ret (bits, (S callsSoFar, state')).

(* game i (Gi 0 = G1 and Gi q = G2) *)
Definition Gi_prg (i : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ (choose_Generate i) (O, (k, v)) requestList;
  A bits.


(* ------------------------------- *)
(* G1 is equal to first hybrid *)

(* move the non-nil init state inside compFold's init acc. otherwise, same compFold as in oracleMap *)
Definition G1_prg_fold : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate_noV (k, v) blocksPerCall;
  (* unfolding the oracleMap *)
  (* [tail_bits, _] <-$2 oracleMap _ _ Generate_v state' (tail requestList); *)
  [bits, _] <-$2 compFold _
            (fun acc d => [rs, s] <-2 acc;
             [r, s] <-$2 Generate_v s d;
             ret (rs ++ r :: nil, s)) 
            (head_bits :: nil, state') (tail requestList);
  A bits.

Lemma compFold_acc_eq : forall (l : list nat) (a0 : list (Bvector eta)) (b1 : KV) (bits : list (list (Bvector eta))),
   comp_spec eq
     (z <-$
      compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_v s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (bits, b1) l;
      [tail_bits, _]<-2 z; A (a0 :: tail_bits))
     (z <-$
      compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_v s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (a0 :: bits, b1) l;
      [bits, _]<-2 z; A bits).
Proof.
  induction l as [ | call calls]; intros.

  * fcf_simp.
    fcf_reflexivity.
  * simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    apply IHcalls.
Qed.

Lemma G1_G1_acc_equal :
  Pr[G1_prg] == Pr[G1_prg_fold].
Proof.
  fcf_to_prhl_eq.
  unfold G1_prg, G1_prg_fold.
  fcf_skip.
  fcf_simp.
  fcf_skip.
  unfold oracleMap.
  (* maybe induct on numCalls then use equality? *)
  unfold requestList.
  apply compFold_acc_eq.
Qed.

(* compFold with Generate_v is the same as compFold with (choose_Generate 0) and # calls starting >=1 *)
Lemma compFold_Generate_v_choose_Generate :
  forall (calls : list nat) (l : list (list (Bvector eta))) (k v : Bvector eta)
         (callsSoFar : nat),
    beq_nat callsSoFar 0%nat = false ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * KV)
        (y : list (list (Bvector eta)) * (nat * KV)) =>
      x = (fst y, snd (snd y)))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_v s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (l, (k, v)) calls)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ choose_Generate 0 s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (l, (callsSoFar, (k, v))) calls).
Proof.
  induction calls as [ | call calls']; intros.
  * simpl.
    fcf_spec_ret.
  * simpl.
    destruct (beq_nat callsSoFar 0).
    - inversion H.
    - simpl.
      fcf_inline_first.
      fcf_simp.
      apply IHcalls'.
      auto.
Qed.

(* wait what? it needs identical until bad??? *)
(* TODO make sure the numbering is right *)
Lemma G_real_is_first_hybrid :
  Pr[G1_prg] == Pr[Gi_prg O].
Proof.
  rewrite G1_G1_acc_equal.
  fcf_to_prhl_eq.
  unfold G1_prg_fold.
  unfold Gi_prg.

  (* choose_Generate 0 is ~ Generate_noV, Generate_v, Generate_v, ...? *)
  unfold requestList.
  destruct numCalls.

  * inversion H_numCalls.

  * simpl.
    comp_skip.
    unfold oracleMap.
    simpl. (* break up latter oracleMap *)
    fs.
    fif.
    fs.
    (* maybe I can get the l out of the compFold? forgot how it works *)
    fcf_skip.
    instantiate (1 := (fun x y => x = (fst y, snd (snd y)))).
    (* simple generalize + induction *)
    apply compFold_Generate_v_choose_Generate.
    auto.

    simpl in H3.
    inversion H3.
    subst.
    destruct b3.
    simpl.
    fcf_reflexivity.
Qed.

(* ----- G2 is equal to last hybrid. Helper lemmas *)

Open Scope nat.

(* relate map with fold where Generate_rb_oracle is easier to prove things about than choose_Generate numCalls *)
Lemma compMap_compFold_rb_eq :
  forall (calls : list nat) (acc : list (list (Bvector eta))) (u : unit),
    comp_spec (fun x y => x = fst y)
              (ls <-$ compMap (list_EqDec eqdbv) Generate_rb calls; ret (acc ++ ls))
              (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
                        (fun (acc0 : list (list (Bvector eta)) * unit) (d : nat) =>
                           [rs, s]<-2 acc0;
                         z <-$ Generate_rb_oracle s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (acc, u) calls).
 Proof.
   induction calls as [ | call calls']; intros.
   * fcf_simp.
     fcf_spec_ret.
   * simpl.
     fcf_inline_first.
     fcf_skip.
     { instantiate (1 := (fun x y => x = fst y)).
     unfold Generate_rb, Generate_rb_oracle.
     fcf_skip.
     fcf_spec_ret. }
     fcf_inline_first.
     fcf_simp.
     simpl in *. subst.

     (* since fcf_rewrite_expr app_cons_eq doesn't work... *)
     assert (comp_spec eq
                       (a <-$ compMap (list_EqDec eqdbv) Generate_rb calls';
                        ls <-$ ret l :: a; ret acc ++ ls)
                       (a <-$ compMap (list_EqDec eqdbv) Generate_rb calls';
                        ret ((acc ++ l :: nil) ++ a))). fcf_skip.
     fcf_spec_ret.
     apply app_cons_eq.

     eapply comp_spec_eq_trans_l.
     apply H1.
     apply IHcalls'.
Qed.

 (* specific version *)
Lemma compMap_compFold_rb_eq_specific :
  forall (calls : list nat) (u : unit),
    comp_spec (fun x y => x = fst y)
              (compMap (list_EqDec eqdbv) Generate_rb calls)
              (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
                        (fun (acc0 : list (list (Bvector eta)) * unit) (d : nat) =>
                           [rs, s]<-2 acc0;
                         z <-$ Generate_rb_oracle s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (nil, u) calls). 
Proof.
  intros.
  eapply comp_spec_eq_trans_l.
  instantiate (1 := ((ls <-$ compMap (list_EqDec eqdbv) Generate_rb calls; ret nil ++ ls))).
  - fcf_ident_expand_l.
    fcf_skip.
    fcf_spec_ret.
  - pose proof (compMap_compFold_rb_eq calls nil u).
    auto.
Qed.

Lemma G2_oracle_eq :
  Pr[G_ideal] == Pr[G_ideal'].
Proof.
  unfold G_ideal, G_ideal'.
  unfold oracleMap.
  fcf_to_prhl_eq.
  fcf_skip.
  apply compMap_compFold_rb_eq_specific.
  fcf_simp.
  simpl in *.
  subst.
  fcf_reflexivity.
Qed.

Lemma oracleMap_v_sampling_eq : forall blocks k v init tt',
   comp_spec (fun x y => fst x = fst y)
      (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
        (fun (acc : list (list (Bvector eta)) * unit) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_rb_oracle s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (init, tt') blocks)
      (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_rb_intermediate s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (init, (k,v)) blocks).
Proof.
  induction blocks as [ | block blocks']; intros.
  - simplify. fcf_spec_ret.
  - fcf_skip; kv_exist.
    instantiate (1 := (fun x y => fst x = fst y)).
    {
      unfold Generate_rb_oracle. simplify.
      fcf_irr_r.
      simplify.
      fcf_skip; kv_exist.
      (* this goes thru without needing the non-0 block hypothesis *)
      { instantiate (1 := (fun x y => x = fst y)).
        clear H0 (*H0*).               (* ok? *)
        revert block k b.
        induction block as [ | n']; intros.
        - (*Print Gen_loop_rb_intermediate.*)
          simpl. fcf_spec_ret.
        - simpl. fcf_skip_eq. fcf_skip. simplify. fcf_spec_ret.
      }
      simpl in *. destruct b0. simpl in *. subst.
      simplify. fcf_spec_ret.
    }
    simpl in *. destruct b0. simpl in *. subst. fold compFold.
    simplify.
    destruct k0.
    destruct b.
    apply IHblocks'.
Qed.

(* This intermediate game isn't strictly necessary--G_ideal' is also an acceptable definition for the final game.
If we wanted to go with that definition, we would simply replace G_ideal with G_ideal' everywhere *)
Lemma G2_oracle_eq_v_sampling :
  Pr[G_ideal'] == Pr[G_ideal''].
Proof.
  unfold G_ideal', G_ideal''.
  unfold oracleMap.
  fcf_to_prhl_eq.
  fcf_irr_r. wfi.
  fcf_skip.
  destruct b.
  eapply oracleMap_v_sampling_eq.
  simplify. simpl in *. subst.
  fcf_ident_expand_l. fcf_ident_expand_r. fcf_skip.
Qed.

(* Relate Gen_loop_rb_intermediate (newly being used) with Gen_loop_rb *)
Lemma Gen_loop_rb_and_intermediate_eq : forall (n : nat) (k v : Bvector eta),
  comp_spec (fun x y => fst x = y) (Gen_loop_rb_intermediate k v n) (Gen_loop_rb n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip_eq. fcf_skip. fcf_spec_ret.
Qed.

(* TODO use the correct theorem to flip sides *)
Lemma Gen_loop_rb_and_intermediate_eq2 : forall (n : nat) (k v : Bvector eta),
  comp_spec (fun x y => x = fst y) (Gen_loop_rb n) (Gen_loop_rb_intermediate k v n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip_eq. fcf_skip. fcf_simp. fcf_spec_ret.
Qed.

(* pull it out? *)
Lemma length_replicate : forall {A : Type} (n : nat) (x : A),
    length (replicate n x) = n.
Proof.
  induction n; intros.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.  

Open Scope nat.
(* oraclemap with intermediate rb is same as oi_prg with i = numcalls *)
Lemma oracleMap_rb_eq : forall calls k v res n,
    n + length calls = numCalls ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * KV)
        (y : list (list (Bvector eta)) * (nat * KV)) => 
      fst x = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Generate_rb_intermediate s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (res, (k, v))
        calls)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ choose_Generate numCalls s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (res, (n, (k, v))) calls).
Proof.
  induction calls as [ | call calls']; intros.
  - simplify. fcf_spec_ret.
  - (* v-sampling *)
    Opaque Generate_rb_intermediate.
    simplify. simpl in *.
    fcf_skip_eq; kv_exist.
    destruct (lt_dec n (n + S (length calls'))).
    2: lia.
    + Transparent Generate_rb_intermediate.
      repeat (simplify; fcf_skip_eq; simplify).
    + simplify. destruct b.
      eapply IHcalls'.
      lia.
Qed.    
Close Scope nat.

(* G2 is equal to last hybrid *)
(* should be even easier than G1 since no Generate_noV happening? Wrong *)
Lemma G_ideal_is_last_hybrid :
  Pr[G_ideal] == Pr[Gi_prg numCalls].
Proof.
(*  Print G_ideal.*)
  rewrite G2_oracle_eq.
  rewrite G2_oracle_eq_v_sampling.
  fcf_to_prhl_eq.
  unfold G_ideal''.
  unfold Gi_prg.
  fcf_skip_eq. simplify.

  rename b into k. rename b0 into v.
  fcf_skip.
  instantiate (1 := (fun x y => fst x = fst y)).

  (* note: switching between windows is C-x o *)
  - unfold oracleMap.
    apply oracleMap_rb_eq.
    simpl.
    unfold requestList.
    apply length_replicate.

  - simpl in *. subst.
    simplify. fcf_reflexivity.
Qed.

(* ---------------------------------- *)

(* For PRF adversary:

Gen_loop_oc: takes an oracle in place of (f k)

Generate_v_oc: takes an oracle in place of (f k)

choose_Generate_rf: if n > i then query Generate_rb, OC version
           else if n = i then query Gen_loop_oc with the given oracle (RF)
           else query Generate_v, OC version (using PRF)

PRF_Adversary: gives the Oi oracle the (f k) oracle it's given by Gi, and queries the resulting oracle `maxCalls` times, querying `numBlocks` each time. passes the result to the existing (non-adaptive) Generate_v adversary

Gi_rf: gives the PRF_Adversary the random function oracle and returns what PRF_Adversary returns

PRF_Advantage: defined in terms of PRF_Adversary, indexed by i 
(but PRF_Advantage should be the same for all i) *)

(* Versions of Gen_loop and Generate_v with that query the oracle in place of (f k) *)
(* this is slightly different from Adam's version:

  Fixpoint PRF_DRBG_f_G2 (v : D)(n : nat) :
    OracleComp D (Bvector eta) (list (Bvector eta)) :=
    match n with
        | O => $ ret nil
        | S n' => 
          r <--$ (OC_Query _ v);
            ls' <--$ (PRF_DRBG_f_G2 (injD r) n');
                $ ret (r :: ls')
    end. *)
Fixpoint Gen_loop_oc (v : Bvector eta) (n : nat)
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => $ ret (nil, v)
  | S n' =>
    v' <--$ (OC_Query _ (to_list v)); (* ORACLE USE *)
    [bits, v''] <--$2 Gen_loop_oc v' n';
    $ ret (v' :: bits, v'')
  end.

(* TODO trying to figure out dependencies for PRF_DRBG. can i instantiate key D etc.? *)
(*Check dupProb_const.
Check PRF_DRBG_G3_bad_4_small.
Print PRF_DRBG_G3_bad_4.*)

(* takes in key but doesn't use it, to match the type of other Generate_vs *)
Definition Generate_v_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *)
  [bits, v'] <--$2 Gen_loop_oc v n;
  (* TODO what's the state type here? and the global Generate_v_oc return type? *)
  k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *)
  $ ret (bits, (k', v')).

(* should use the oracle and ignore the passed-in k *)
Definition Generate_noV_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta)  (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <--$2 Gen_loop_oc v n;
  (* TODO what's the state type here? and the global Generate_v_oc return type? *)
  k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *)
  $ ret (bits, (k', v')).

(* doesn't use the oracle, uses the PRF *)
Definition Generate_v_PRF_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  $ ret (bits, (k', v'')).

(* doesn't use the state or oracle *)
(* intermediates have unnecessary state and updating of the state to match earlier ones *)
(* old version *)
(* Definition Generate_rb_intermediate_oc (state : KV) (n : nat)  *)
(*   : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) := *)
(*   bits <--$ $ Gen_loop_rb n;    (* promote comp to oraclecomp, then remove from o.c. *) *)
(*   $ ret (bits, state). *)

(* @v new version: uses last v and updates (k,v) anyway *)
Definition Generate_rb_intermediate_oc (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <--$ $ {0,1}^eta;
  [bits, v''] <--$2 $ Gen_loop_rb_intermediate k v' n;    (* promote comp to oraclecomp, then remove from o.c. *)
  $ ret (bits, (k, v'')).

(* same as choose_Generate but each Generate_v in it has been converted to OracleComp *)
(* number of calls starts at 0 and ends at q. e.g.
G1:      RB  PRF PRF
Gi_rf 1: RB  RF  PRF (i = 1 here)
G2:      RB  RB  PRF *)
(* number of calls: first call is 0, last call is (numCalls - 1) for numCalls calls total
G0: PRF PRF PRF <-- Gi_prf 0
    RF  PRF PRF <-- Gi_rf 0
G1: RB  PRF PRF <-- Gi_prf 1
    RB  RF  PRF <-- Gi_rf 1
G2: RB  RB  PRF
w    RB  RB  RF
G3: RB  RB  RB  <-- note that there is no oracle slot to replace here
    RB  RB  RB  <-- likewise
there should be (S numCalls) games, so games are numbered from 0 through numCalls *)
(* there is always an oracle slot to replace until i >= numCalls *)

(* not entirely sure these are all the right cases / in the right order *)
(* i: index for oracle; callsSoFar; n *)
Definition Oi_oc' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let Generate_v_choose :=
      (* this behavior (applied with f_oracle) needs to match that of choose_Generate's *)
      if lt_dec callsSoFar i (* callsSoFar < i (override all else) *)
           then Generate_rb_intermediate_oc (* this implicitly has no v to update *)
      else if beq_nat callsSoFar O (* use oracle on 1st call w/o updating v *)
           then Generate_noV_oc 
      else if beq_nat callsSoFar i (* callsSoFar = i *)
           then Generate_v_oc    (* uses provided oracle (PRF or RF) *)
      else Generate_v_PRF_oc in        (* uses PRF with (k,v) updating *)
  [bits, state'] <--$2 Generate_v_choose state n;
  $ ret (bits, (S callsSoFar, state')).

(* oracleCompMap_inner repeatedly applies the given oracle on the list of inputs (given an initial oracle state), collecting the outputs and final state *)
(* Fixpoint oracleCompMap_inner_acc {D R OracleIn OracleOut : Set}  *)
(*            (e1 : EqDec ((list R) * (nat * KV)))  *)
(*            (e2 : EqDec (list R)) *)
(*            (* this is an oracleComp, not an oracle *) *)
(*            (* the oracle has type (D * R) -> D -> Comp (R, (D * R)) *) *)
(*            (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV)))  *)
(*            (state : (nat * KV)) *)
(*            (init : list R) *)
(*            (inputs : list D) : OracleComp OracleIn OracleOut (list R * (nat * KV)) := *)
(*   match inputs with *)
(*   | nil => $ ret (init, state) *)
(*   | input :: inputs' =>  *)
(*     [res, state'] <--$2 oracleComp state input; (* doesn't use the init *) *)
(*     [resList, state''] <--$2 oracleCompMap_inner_acc _ _ oracleComp state' init inputs'; *)
(*     $ ret (init ++ res :: resList, state'') *)
(*   end. *)

(* Print compFold. *)
(* Print oracleMap. *)
(* Print oc_compMap. *)
(* compare to oc_compMap *)
(* maybe i don't even need to rewrite oracleCompMap_inner. what theorem do i really want? TODO *)

Fixpoint oracleCompMap_inner {D R OracleIn OracleOut : Set} 
           (e1 : EqDec ((list R) * (nat * KV))) 
           (e2 : EqDec (list R))
           (* this is an oracleComp, not an oracle *)
           (* the oracle has type (D * R) -> D -> Comp (R, (D * R)) *)
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV))) 
           (state : (nat * KV)) (* note this state type -- it is EXPLICITLY being passed around *)
           (inputs : list D) : OracleComp OracleIn OracleOut (list R * (nat * KV)) :=
  match inputs with
  | nil => $ ret (nil, state)
  | input :: inputs' => 
    [res, state'] <--$2 oracleComp state input;
    [resList, state''] <--$2 oracleCompMap_inner _ _ oracleComp state' inputs';
    $ ret (res :: resList, state'')
  end.

(* hides the oracle state from the caller. instantates the initial state and does not return the end state. need this, otherwise the PRF adversary has to generate the key and initial value (and can see it, which it shouldn't be able to) *)
Definition oracleCompMap_outer {D R OracleIn OracleOut : Set} 
           (e1 : EqDec ((list R) * (nat * KV))) 
           (e2 : EqDec (list R))
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV)))
           (inputs : list D) : OracleComp OracleIn OracleOut (list R) :=
  [k, v] <--$2 $ Instantiate;   (* generate state inside, instead of being passed state *)
  [bits, _] <--$2 oracleCompMap_inner _ _ oracleComp (O, (k, v)) inputs;
  (* the "_" here has type (nat * KV) *)
  $ ret bits.                    (* don't return the state to the PRF adversary *)

(* see long comment above this section *)
Definition PRF_Adversary (i : nat) : OracleComp Blist (Bvector eta) bool :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) requestList;
  $ A bits.

(* ith game: use RF oracle *)
Definition Gi_rf (i : nat) : Comp bool :=
  [b, _] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret b.

(* ith game: use PRF oracle *)
Definition Gi_prf (i : nat) : Comp bool :=
  k <-$ RndK;
  [b, _] <-$2 PRF_Adversary i _ _ (f_oracle f _ k) tt;
  ret b.

(* Expose the bad events *)

Definition hasInputDups (state : list (Blist * Bvector eta)) : bool :=
  hasDups _ (fst (split state)).

(* ith game: use RF oracle *)
Definition Gi_rf_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret (b, hasInputDups state). 

Definition rb_oracle (state : list (Blist * Bvector eta)) (input : Blist) :=
  output <-$ ({0,1}^eta);
  ret (output, (input, output) :: state).

Definition Gi_rb (i : nat) : Comp bool :=
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  let rbInputs := fst (split state) in
  ret b.

(* adam wrote a new game here -- bad event is repetition in the random INPUTS
INPUTS = v :: (first n of outputs)? *)
(* pass in the RB oracle that records its inputs
what about preceding/following RB and (especially) PRF inputs/outputs? *)
Definition Gi_rb_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  ret (b, hasInputDups state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

(* replace requestList with a list we can evaluate on *)
Definition PRF_Adversary_l (i : nat) (l : list nat) : OracleComp Blist (Bvector eta) bool :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) l;
  $ A bits.

(* also replaced with hasDups: my hypothesis is that adam was right *)
Definition Gi_rf_bad_l (i : nat) (l : list nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary_l i l _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret (b, hasInputDups state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

Definition Gi_rb_bad_l (i : nat) (l : list nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary_l i l _ _ rb_oracle nil;
  ret (b, hasDups _ state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

(* ----------------Begin PRF advantage reduction section *)

Definition PRF_Advantage_Game i : Rat := 
  PRF_Advantage RndK ({0,1}^eta) f eqdbl eqdbv (PRF_Adversary i).

(*   | Pr  [PRF_G_A RndK f eqdbv (PRF_Adversary 0) ] -
   Pr  [PRF_G_B ({ 0 , 1 }^eta) eqdbl eqdbv (PRF_Adversary 0) ] | =
   | Pr  [PRF_G_A RndK f eqdbv (PRF_Adversary i) ] -
   Pr  [PRF_G_B ({ 0 , 1 }^eta) eqdbl eqdbv (PRF_Adversary i) ] | *)

(* TODO: are these lemmas even true? 
PA uses the existing adversary against the output?
here, numCalls = 4

PA 0: using given oracle for call 0
GA: PRF PRF PRF PRF?
GB:  RF PRF PRF PRF 

PA 1: using given oracle for call 1
GA: RB  PRF PRF PRF? 
GB: RB  RF  PRF PRF? 
(do the PRF_advantages add?)

PA n-2: using given oracle for call (n-2) = 2
GA: RB  RB  PRF PRF
GB: RB  RB  RF  PRF

PA n-1: using given oracle for call (n-1) = 3
GA: RB  RB  RB  PRF
GB: RB  RB  RB  RF

PA n: using given oracle for call n = 4
(note: there is no oracle to replace, so PRF_Advantage = 0)
GA: RB  RB  RB  RB
GB: RB  RB  RB  RB

forall i, i != n -> 
PRF_Advantage_Game i = PRF_Advantage_Game j
PRF_Advantage_Game n = 0

thus, forall i, PRF_Advantage_Game i <= PRF_Advantage_Game 0 *)

Open Scope nat.
(* the oracles don't matter (for those two specific oracles) *)
(* could generalize this further to hold for any oracles, instead of f_oracle and RndR_func *)
Lemma Oi_numcalls_oracle_irrelevance : forall calls k v a (numCalls init : nat) acc tt,
    init + length calls = numCalls ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV) * unit)
        (y : list (list (Bvector eta)) * (nat * KV) *
             list (Blist * Bvector eta)) => fst x = fst y)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' numCalls) 
         (init, (k, v)) calls) unit unit_EqDec
        (f_oracle f eqdbv a) tt)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' numCalls) 
         (init, (k, v)) calls) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        (RndR_func ({ 0 , 1 }^eta) eqdbl) acc).
Proof.
(* didn't i do a gnarly proof just like this one earlier?? oh but it wasn't about oraclecompmap_inner. see 'G2 = last hybrid' proof*)
  induction calls as [ | call calls']; intros.
  - simpl.
    fcf_simp.
    fcf_spec_ret.
  - simpl in H.
    simpl.
    fcf_inline_first.
    fcf_skip; kv_exist.

    { instantiate (1 := (fun x y => fst x = fst y)).
      destruct (lt_dec init (init + S (length calls'))).
      * unfold Generate_rb_intermediate_oc.
        simpl.
        fcf_inline_first.
        fcf_skip; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_spec_ret.

     * lia.
    }
    simpl in H2.
    destruct b1.
    simpl in *.
    subst.
    fcf_inline_first.
    simpl.
    fcf_inline_first.
    fcf_simp.
    simpl.
    fcf_skip.
    destruct b0.                (* prevents unification *)
    apply IHcalls'.             (* lol *)
    lia.

    simpl in H3.
    destruct b2.
    simpl in *.
    subst.
    fcf_simp.
    fcf_spec_ret.
Qed.

Close Scope nat.

Lemma PRF_Advantage_0 : 
    PRF_Advantage_Game numCalls == 0.
Proof.
  intros. unfold PRF_Advantage_Game. unfold PRF_Advantage.
  assert (distance_0_eq : forall r1 r2 : Rat, r1 == r2 -> | r1 - r2 | == 0).
  { apply ratIdentityIndiscernables. }
  apply distance_0_eq. clear distance_0_eq.
  
  fcf_to_prhl_eq. (* TODO when should I *not* use this? *)

  (* TODO lemma that PRF_Advantage_Game numCalls always uses random bits and ignores the inputted oracle, so games A and B are on indistinguishable output *)

  unfold PRF_Adversary.
  unfold PRF_G_A.
  unfold PRF_G_B.

  fcf_irr_l. unfold RndK. fcf_well_formed.

  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.

  (* arriving at oracleCompMap_inner: same but the oracles are different *)
  instantiate (1 := (fun x y => fst x = fst y)). (* TODO: forgot why this and not eq *)
  (* TODO: here, theorem about oracleCompMap_inner on requestList not using oracle (forall oracles A B...) *)

  *
    (* do i need induction? are there theorems about oracleCompMap (Adam's version)? *)
    unfold Oi_oc'.
    unfold oracleCompMap_inner.
    apply Oi_numcalls_oracle_irrelevance.
    simpl.
    unfold requestList.
    apply length_replicate.

  * simpl.
    fcf_simp.
    fcf_inline_first.
    simpl.
    fcf_inline_first.
    fcf_simp.
    fcf_inline_first.
    simpl in H4.
    inversion H4.
    subst.
    fcf_skip.
    fcf_simp. (* TODO ltac for this kind of proof *)
    fcf_reflexivity.
Qed.

(* Below can be used to establish a maximum advantage over all constructed adversaries *)
Theorem gtRat_impl_leRat:
  forall a b,
    (a <= b -> False) ->
    b <= a.

    intuition.
    rattac.
    destruct (le_dec (n * x) (n0 * x0))%nat.
    trivial.
    exfalso.
    eapply H.
    rattac.
Qed.

Fixpoint argMax(f : nat -> Rat) (n : nat) :=
  match n with
    | O => O
    | S n' => let p := (argMax f n') in
              if (le_Rat_dec (f (S n')) (f p)) then p else (S n')
                                                             end.

Theorem argMax_correct :
  forall (f : nat -> Rat)(n : nat),
    (forall n', (n' <= n)%nat -> (f n') <= f (argMax f n)).

  induction n; intuition; simpl in *.
  assert (n' = O) by lia; subst.
  intuition.
  destruct (eq_nat_dec n' (S n)).
  subst.
  destruct (le_Rat_dec (f0 (S n)) (f0 (argMax f0 n)));
  intuition.

  assert (n' <= n)%nat by lia.
  destruct (le_Rat_dec (f0 (S n)) (f0 (argMax f0 n))).
  eapply IHn; eauto.
  eapply leRat_trans.
  eapply IHn.
  trivial.
  eapply gtRat_impl_leRat; eauto.
Qed.

Theorem PRF_Advantage_max_exists :
  forall i,
      (i <= numCalls)%nat ->
      PRF_Advantage_Game i <= PRF_Advantage_Game (argMax PRF_Advantage_Game numCalls).

  intuition.
  apply argMax_correct; trivial.

Qed.

Definition PRF_Advantage_Max := PRF_Advantage_Game (argMax PRF_Advantage_Game numCalls).

(* The theorem above can be used in some of the arguments below, replacing 0 with (argMax PRF_Advantage_Game numCalls *)

(* TODO moved to end for testing *)
(* (* Step 1 *)
(* Gi_prf 2: RB RB PRF PRF PRF
   Gi_rf 2:  RB RB RF  PRF PRF 
need to use `Gi_prf i` instead of `Gi_prg i` because this matches the form of 
`Gi_rf` closer so we can match the form of PRF_Advantage*)4
Lemma Gi_replace_prf_with_rf_oracle_i : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Game i.
Proof.
  intros i.
  (* don't need to unfold *)
  unfold Gi_prf.
  unfold Gi_rf.
  unfold PRF_Advantage_Game.
  reflexivity. 
Qed.

Lemma Gi_replace_prf_with_rf_oracle : forall (i : nat),
    (i <= numCalls)%nat ->
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Max.
Proof.
  intros.
  eapply leRat_trans.
  apply Gi_replace_prf_with_rf_oracle_i.
  apply PRF_Advantage_max_exists.
  auto.
Qed. *)

(* ------------------------------- *)

(* Step 2 *)

(* TODO use Adam's existing theorem. not sure if this is the right bound.
should be a function of [blocksPerCall + 1] (for the extra v-update) *)
Definition Pr_collisions := (S blocksPerCall)^2 / 2^eta.

(* may need to update this w/ new proof *)
Definition Gi_Gi_plus_1_bound := PRF_Advantage_Max + Pr_collisions.

(* These are all lemmas to rewrite games so I can apply identical until bad *)

Definition fst3 {A B C : Type} (abc : A * B * C) : A :=
  let (ab, c) := abc in
  let (a, b) := ab in
  a.

Open Scope nat.

(* These examples take a long time to check because of `simplify`. Commented out for now. *)

(* folding on an acc that appends two lists = fold on the first list, use result as acc in fold on second list *)
Lemma fold_app_2 : forall (A0 B : Set) (eqd : EqDec A0) (c : A0 -> B -> Comp A0)
                          (ls1 ls2 : list B) (init0 x : A0) (res : A0),
    comp_spec eq (compFold eqd c init0 (ls1 ++ ls2))
              (init' <-$ compFold eqd c init0 ls1; compFold eqd c init' ls2).
Proof.
  intros.
  revert c ls2 init0 x res; induction ls1 as [| x1 xs1]; intros.
  - simpl. simplify. fcf_reflexivity.
  - simplify.
    fcf_skip_eq.
Qed.


(* new postcondition *)
Definition bitsVEq {A B : Type} (x : A * (nat * KV)) (y : A * (nat * KV) * B) :=
  let (bits_x, state_x) := x in
  let (calls_x, kv_x) := state_x in
  let (k_x, v_x) := kv_x in

  let (bits_y, state_y) := fst y in
  let (calls_y, kv_y) := state_y in
  let (k_y, v_y) := kv_y in
  (* no statement about keys being equal for now *)
  bits_x = bits_y /\ v_x = v_y /\ calls_x = calls_y.

Ltac breakdown x := simpl in x; decompose [and] x; clear x; subst.

(* -------- *)
(* Rewrite gen_loop and updates computationally, and prove equivalence *)

Fixpoint Gen_loop_comp (k : Bvector eta) (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <- f k (to_list v);
    [bits, v''] <-$2 Gen_loop_comp k v' n';
    ret (v' :: bits, v'')
  end.

(* want to change to this, and prove the outputs are the same. 
the other Generate_vs don't use this version *)
Definition Generate_v_comp (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-$2 Gen_loop_comp k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  ret (bits, (k', v'')).

(* use this for the first call *)
Definition Generate_noV_comp (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-$2 Gen_loop_comp k v n;
  k' <- f k (to_list v' ++ zeroes);
  ret (bits, (k', v')).

Lemma Gen_loop_comp_eq : forall n k v,
  comp_spec eq (ret (Gen_loop k v n)) (Gen_loop_comp k v n).
Proof.
  induction n as [ | n']; intros.
  - simpl. fcf_spec_ret.
  - simpl.
    unfold setLet.
    (* You need to apply your induction hypothesis to the first statement of the computation on the right.  The most direct way to do this is to explicitly apply transitivity: *)
    (* eapply comp_spec_eq_trans. *)
(*    Print comp_spec_eq_trans.*)
    eapply
      (@comp_spec_eq_trans _ _ 
           ((ret (let (bits, v'') := Gen_loop k (f k (to_list v)) n' in
                  (f k (to_list v) :: bits, v''))))

           (z <-$ ret Gen_loop k (f k (to_list v)) n';
            [bits, v'']<-2 z;
            ret (f k (to_list v) :: bits, v''))).
        
    comp_simp; reflexivity.
    comp_skip.
    (* this tactic will find the induction hypothesis and apply it *)
Qed.

Lemma Gen_loop_comp_eq_outer : forall n k v,
   comp_spec eq
     ([bits, v']<-2 Gen_loop k v n;
      ret (bits, (f k (to_list v' ++ zeroes), v')))
     (z <-$ Gen_loop_comp k v n;
      [bits, v']<-2 z; ret (bits, (f k (to_list v' ++ zeroes), v'))).
Proof.
  intros. 
  pose proof (Gen_loop_comp_eq n k v).
  eapply comp_spec_eq_trans.
  instantiate (1 := (z <-$ ret Gen_loop k v n;
         [bits, v'']<-2 z; ret (bits, (f k (to_list v'' ++ zeroes), v'')))).
  simplify. fcf_spec_ret.
  fcf_skip_eq.
Qed.

Lemma Generate_v_comp_eq : forall n k v,
  comp_spec eq (Generate_v (k,v) n) (Generate_v_comp (k,v) n).
Proof.
  intros. simpl. unfold setLet. apply Gen_loop_comp_eq_outer.
Qed.

Lemma Gen_loop_oc_eq : forall n k v,
   comp_spec
     (fun (x : list (Bvector eta) * Bvector eta)
        (y : list (Bvector eta) * Bvector eta * unit) =>
      fst x = fst (fst y) /\ snd x = snd (fst y)) 
     (Gen_loop_comp k v n)
     ((Gen_loop_oc v n) unit unit_EqDec (f_oracle f eqdbv k) tt).
Proof.
  induction n as [ | n']; intros.
  - simplify. fcf_spec_ret.
  - simpl.
    unfold setLet.
    prog_ret_r.
    fcf_skip. fcf_simp. simpl in *. subst. fcf_spec_ret.
Qed.

(* ------- *)

(* second induction used to prove the lemma after it. calls = i, then destruct, the induction on calls > i *)
Lemma Gi_prog_equiv_prf_oracle_calls_eq_i :
  forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta) init,
    calls = i ->
    comp_spec
      (fun (c : list (list (Bvector eta)) * (nat * KV))
           (d : list (list (Bvector eta)) * (nat * KV) * unit) => 
         bitsVEq c d)
      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
          z <-$ choose_Generate i s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
         (init, (calls, (k1, v))) l)
      (z <-$
         (oracleCompMap_inner
            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                        (pair_EqDec nat_EqDec eqDecState))
            (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
            (calls, (k2, v)) l) unit unit_EqDec 
         (f_oracle f eqdbv k1) tt;
       [bits, nkv, state']<-3 z; ret (init ++ bits, nkv, state')).
Proof.
  Opaque choose_Generate. Opaque Oi_oc'.
  destruct l as [ | x xs]; intros.

  - simplify. fcf_spec_ret. simpl. repeat (split; auto).
    rewrite app_nil_r; reflexivity.
  -
    simplify.
    fcf_skip; kv_exist.
    instantiate (1 := (fun c d => bitsVEq c d
                                  /\ fst (snd c) = S i /\ fst (snd (fst d)) = S i
                                  (* keys become equal afterward on call i *)
                                  /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
    (* 1 call *)
    {
      Transparent choose_Generate. Transparent Oi_oc'.
      unfold choose_Generate. unfold Oi_oc'.
      simplify.
      (* casework on `i = 0`, `calls = i` and `calls > i` *)
      destruct (lt_dec i i). lia. 
      clear n.
      destruct (beq_nat i 0).
      -
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        simpl. fcf_inline_first.
        eapply comp_spec_eq_trans_l.
        apply Gen_loop_comp_eq_outer.

        fcf_skip. 
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        (* induction *)
        apply Gen_loop_oc_eq.

        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simpl. destruct k. auto.

      - Opaque Generate_v.
        simpl.
        assert (beq_nat i i = true) by apply Nat.eqb_refl.
        destruct (beq_nat i i).
        2: inversion H.
        clear H.
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        Transparent Generate_v. unfold Generate_v. unfold Generate_v_oc.
        simpl. unfold setLet. prog_ret_r.
        eapply comp_spec_eq_trans_l.
        apply Gen_loop_comp_eq_outer.        
        fcf_skip. 

        (* induction *)
        apply Gen_loop_oc_eq.

        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simpl. destruct k. auto.
        Opaque choose_Generate. Opaque Oi_oc'.
    }

    (* rest of calls -- induct on the new list *)
    { simplify. simpl in *. destruct b0. destruct p. destruct k. simpl in *. breakdown H2. 

      clear H1 H3 H0.
      rename b1 into k'. rename b2 into v'.
      remember (S i) as calls.
      assert (H_calls : calls > i) by lia.
      clear Heqcalls k2 v.
      revert x i k1 init l k' v' u calls H_calls.
      induction xs as [ | x' xs']; intros.

      (* xs = nil *)
      + simplify. fcf_spec_ret. simpl. repeat (split; auto).
      (* xs = x' :: xs', use IH *)
      + simplify.
        fcf_skip; kv_exist.

        (* one call with calls > i (calls = S i) *)
        instantiate (1 := (fun c d => bitsVEq c d
                                      (* calls incremented by one *)
                                      /\ fst (snd c) = S calls
                                      /\ fst (snd (fst d)) = S calls
                                      (* keys equal *)
                                      /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
        {
          Transparent choose_Generate. Transparent Oi_oc'.
          unfold choose_Generate. unfold Oi_oc'.
          (* calls > i implies S calls != i *)
          assert (H_false : beq_nat (S calls) i = false).
          { apply Nat.eqb_neq. lia. }
          destruct (beq_nat (S calls) i). inversion H_false.
          clear H_false.
          simplify.
          destruct (lt_dec calls i). lia. (* contradiction *)
          apply not_lt in n.
          assert (beq_nat calls 0 = false).
          { apply Nat.eqb_neq. lia. }
          rewrite H0. Opaque Generate_v.
          simpl.
          assert (beq_nat calls i = false).
          { apply Nat.eqb_neq. lia. }
          rewrite H1.
          Transparent Generate_v. simpl. fcf_inline_first.
          fcf_skip; kv_exist.
          instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
          fcf_simp. 
          fcf_spec_ret.
          simplify. simpl in *. breakdown H4. fcf_spec_ret.
          simpl. destruct k. auto.
          Opaque choose_Generate. Opaque Oi_oc'.          
        }

        simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *. breakdown H2.
        simplify.
        
        eapply comp_spec_eq_trans_r. 
        eapply H; lia.
        
        (* now prove oracleCompMap_inner's eq *)
        { instantiate (1 := k1). 
          fcf_skip_eq; kv_exist.
          simplify. fcf_spec_ret.
          f_equal. f_equal.
          rewrite <- app_cons_eq.
          reflexivity.
        }
    }
Qed.

Theorem Gen_loop_rb_intermediate_keys_diff : forall (n : nat) (k1 k2 v : Bvector eta),
   comp_spec eq (Gen_loop_rb_intermediate k1 v n) (Gen_loop_rb_intermediate k2 v n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip. fcf_skip.
Qed.

Theorem Gi_prog_equiv_prf_oracle_compspec :
  forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta) init,
    calls <= i ->

    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
         bitsVEq x y)

      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
         z <-$ choose_Generate i s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k1, v))) l)

     ([acc', state'] <-$2 ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k2, v)) l) unit unit_EqDec 
        (f_oracle f eqdbv k1) tt);
      [bits, nkv] <-2 acc';
      ret (init ++ bits, nkv, state')).
Proof.
  induction l as [ | x xs]; intros.

  - simpl in *.
    simplify.
    fcf_spec_ret.
    simpl.
    repeat (split; auto).
    rewrite app_nil_r. reflexivity.

  -                             (* l = x :: xs *)
    assert (H_ilen : calls < i \/ calls = i) by lia.
    destruct H_ilen.
    clear H.

    (* calls < i *)
    + Opaque choose_Generate. Opaque Oi_oc'.
      unfold oracleMap.
      simplify.
      fcf_skip; kv_exist.
      (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
      (* also strengthen it again because if calls < i then the keys must still be the same *)
      instantiate (1 := (fun c d => bitsVEq c d
                                    (* calls incremented by 1 *)
                                    /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                    (* output keys are the input keys *)
                                    (* /\ fst (snd (snd c)) = fst (snd (snd (fst d))) )). *)
                                    /\ fst (snd (snd c)) = k1
                                    /\ fst (snd (snd (fst d))) = k2)).
      (* includes calls *)
      (* one call with linked keys TODO *)
      {
        Transparent choose_Generate. Transparent Oi_oc'.
        simpl.
        destruct (lt_dec calls i).
        2: lia.         (* contradiction *)
        clear l.                (* calls < i *)
        unfold Generate_rb_intermediate.
        simplify.
        (* @v *)
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip; kv_exist.
        apply Gen_loop_rb_intermediate_keys_diff.
        subst. simplify.
        fcf_spec_ret.
        unfold bitsVEq. simpl. auto.
      }

      (* use IH *)
      { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *.
        breakdown H2. 
        simplify.

        eapply comp_spec_eq_trans_r.
        eapply IHxs; lia. 

        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq; kv_exist.
          simplify.
          instantiate (1 := k2).
          destruct u.
          fcf_reflexivity.
          simplify.
          fcf_spec_ret. rewrite <- app_assoc. f_equal.
        }
      } 
    
    (* calls = i *)
  + clear IHxs.
    apply Gi_prog_equiv_prf_oracle_calls_eq_i; lia.
Qed.
        
Transparent oracleMap.
Transparent oracleCompMap_inner.
Transparent choose_Generate.
Transparent Oi_oc'.

(* this moves from the normal adversary to the PRF adversary (which depends on the prev.) *)
(* Gi_prg 0: PRF PRF PRF PRF
   Gi_prf 0: PRF PRF PRF PRF
   Gi_prg 2: RB RB PRF PRF
   Gi_prf 2: RB RB PRF PRF *)
Lemma Gi_prog_equiv_prf_oracle : forall (i : nat),
  Pr[Gi_prg i] == Pr[Gi_prf i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_prf.
  unfold PRF_Adversary.

  fcf_to_prhl_eq.
  unfold Instantiate.
  unfold oracleCompMap_outer.
  fcf_inline_first.

  unfold Instantiate.
  comp_skip.
  Opaque oracleMap.
  simpl.
  fcf_inline_first.

  unfold Instantiate.
  fcf_inline_first.
  fcf_irr_r. unfold RndK. fcf_well_formed.
  fcf_inline_first.
  comp_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.

  instantiate (1 := fun x y => bitsVEq x y).
  -
    Transparent oracleMap.
    pose proof Gi_prog_equiv_prf_oracle_compspec as Gi_prf_compspec.
    unfold oracleMap.
    specialize (Gi_prf_compspec requestList i 0 b b0 b1 nil).
    eapply comp_spec_eq_trans_r.
    eapply Gi_prf_compspec; lia.
    simplify.
    fcf_ident_expand_r.
    fcf_skip_eq; kv_exist.

  - simplify.
    simpl in H6. destruct b3. destruct p. destruct k. breakdown H6.
    fcf_ident_expand_l.
    fcf_skip_eq.
    simplify.
    fcf_reflexivity.
Qed.

(* expose the bad event (dups) *)
Lemma Gi_rf_return_bad_eq : forall (i : nat),
    Pr[Gi_rf i] == Pr[x <-$ Gi_rf_bad i; ret fst x].
Proof.
  intros. (* over all i--could be hard? *)
  fcf_to_prhl_eq.
  unfold Gi_rf.
  unfold Gi_rf_bad.
  repeat (simplify; fcf_skip_eq).
  simplify. fcf_spec_ret.
Qed.

Definition randomFunc_withDups (ls : list (Blist * Bvector eta)) (x : Blist) :
                               Comp (Bvector eta * list (Blist * Bvector eta)) :=
  y <-$ 
    (match (arrayLookup _ ls x) with 
     | Some y => ret y 
     | None => {0,1}^eta 
     end); 
  ret (y, (x, y) :: ls).

(* ith game: use RF oracle *)
Definition Gi_rf_dups_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ randomFunc_withDups nil;
  ret (b, hasInputDups state). 

Theorem oracleCompMap_inner_oracle_equiv : 
    forall (A B C D S : Set) (eqdc : EqDec C)(eqdd : EqDec D)(eqds : EqDec S) blocks (inv : S -> S -> Prop) (oc : nat * KV -> A -> OracleComp B C (D * (nat * KV))) s (o1 o2 : S -> B -> Comp (C * S)) s1 s2,
    (forall s1 s2, inv s1 s2 -> (forall a, comp_spec (fun x1 x2 => (fst x1 = fst x2) /\ inv (snd x1) (snd x2)) (o1 s1 a) (o2 s2 a))) ->
    inv s1 s2 ->
    comp_spec (fun x1 x2 => fst x1 = fst x2 /\ inv (snd x1) (snd x2))
   ((oracleCompMap_inner _ _ oc
         s blocks) _ _
        o1 s1)
  ((oracleCompMap_inner _ _ oc
         s blocks) _ _
        o2 s2).
  
  induction blocks; intuition; simpl; fcf_simp.
  apply comp_spec_ret; intuition.

  fcf_simp.
  fcf_skip.
  eapply oc_comp_spec_eq.
  apply H0.
  intuition.
  
  fcf_simp.
  simpl in *.
  intuition.
  pairInv.
  fcf_skip.
  simpl in *.
  destruct b3.
  simpl in *. subst.
  fcf_simp.
  apply comp_spec_ret.
  simpl.
  intuition.

Qed.


Theorem randomFunc_withDups_spec : 
  forall s1 s2 a,
  (forall a, arrayLookup _ s1 a = arrayLookup _ s2 a) ->
  comp_spec
     (fun x1 x2 : Bvector eta * list (Blist * Bvector eta) =>
      fst x1 = fst x2 /\
      (forall a0, 
       arrayLookup _ (snd x1) a0 = arrayLookup _ (snd x2) a0))
     (randomFunc ({ 0 , 1 }^eta) _ s1 a) (randomFunc_withDups s2 a).

  clear f.
  intuition.
  unfold randomFunc_withDups, randomFunc.
  case_eq (arrayLookup _ s1 a); intuition.
  rewrite <- H.
  rewrite -> H0.

  fcf_simp.
  apply comp_spec_ret.
  intuition.
  simpl. 
  case_eq (eqb a0 a); intuition.
  rewrite eqb_leibniz in H1.
  subst. trivial.

  rewrite <- H.
  rewrite H0.
  fcf_skip.
  apply oneVector.
  apply oneVector.
  eapply comp_spec_ret.
  intuition.
  simpl.
  rewrite H. 
  trivial.
Qed.

Lemma oracleCompMap_rf_oracle_irrelevance : forall blocks calls i k v state,
   comp_spec (fun x1 x2 => fst x1 = fst x2 /\ forall a, arrayLookup _ (snd x1) a = arrayLookup _ (snd x2) a)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        (randomFunc ({ 0 , 1 }^eta) eqdbl) state)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) randomFunc_withDups state).
Proof.
  intros.
  eapply comp_spec_consequence.
  eapply (oracleCompMap_inner_oracle_equiv _ _ (fun s1 s2 => forall a, arrayLookup _ s1 a = arrayLookup _ s2 a)); intuition.
   apply randomFunc_withDups_spec; intuition.
  intuition.
Qed.
 
Lemma Gi_rf_dups_return_bad_eq : forall (i : nat),
    Pr[x <-$ Gi_rf_bad i; ret fst x] == Pr[x <-$ Gi_rf_dups_bad i; ret fst x].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rf_bad.
  unfold Gi_rf_dups_bad.

  repeat (simplify; fcf_skip).
  apply oracleCompMap_rf_oracle_irrelevance.
  simpl in *.
  intuition; pairInv.
  eapply comp_spec_eq_refl.
  fcf_simp.
  subst.
  reflexivity.
Qed.

(* expose the bad event (dups) *)
Lemma Gi_rb_return_bad_eq : forall (i : nat),
    Pr[Gi_rb i] == Pr[x <-$ Gi_rb_bad i; ret fst x].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb.
  unfold Gi_rb_bad.
  repeat (simplify; fcf_skip_eq).
  simplify.
  fcf_spec_ret.
Qed.

(* ---------------------------------- *)
(* Assuming the Gi_prog_equiv_rb_oracle stuff starts here *)

(* Used in the below proof: relates Gen_loop_rb_intermediate and Gen_loop_oc *)
Lemma Gen_loop_rb_intermediate_oc_related : forall (n : nat) (k v : Bvector eta) (rb_state : list (Blist * (Bvector eta))),
   comp_spec
     (fun (x : list (Bvector eta) * Bvector eta)
        (y : list (Bvector eta) * Bvector eta * list (Blist * Bvector eta)) =>
      fst x = fst (fst y) /\ snd x = snd (fst y))
     (Gen_loop_rb_intermediate k v n)
     ((Gen_loop_oc v n) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state).
Proof.
  induction n as [ | n']; intros; simplify.
  - fcf_spec_ret.
  - unfold rb_oracle. simplify. fcf_skip_eq. simplify. fold rb_oracle.
    fcf_skip. simpl in *. destruct b0. simpl in *. destruct p. simpl in *. subst.
    simplify. fcf_spec_ret.
Qed.

(* used in Oi_oc''. the difference between this function and Generate_v_oc is that
it hardcodes the oracle to be RB oracle, and moves the k update to be the first line, 
rather than being after the bit generation, because k no longer depends on the new v *)
(* takes in key but doesn't use it, to match the type of other Generate_vs *)
Definition Generate_v_oc_instantiate (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  k' <--$ $ {0,1}^eta;
  v <--$ $ {0,1}^eta;
  [bits, v'] <--$2 Gen_loop_oc v n;
  $ ret (bits, (k', v')).

(* used in Oi_oc''. the difference between this function and Generate_rb_intermediate_oc
is that it now updates v (but still does not update k). 
why do we need to update v in the normal RB cases??? *)
(* okay, i see that we're trying to match the form of Generate_v_oc_instantiate *)
(* at a high level, we're trying to bridge Generate_v_oc_instantiate and Generate_rb_intermediate_oc *)
(* now unused *)
Definition Generate_rb_intermediate_oc_noV (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  
  [bits, v'] <--$2 $ Gen_loop_rb_intermediate k v n;    (* promote comp to oraclecomp, then remove from o.c. *)
  $ ret (bits, (k, v')).

(* does not carry the k state around *)
(* TODO: this function and the next theorem aren't used anywhere?? *)
Fixpoint Gen_loop_rb_intermediate_v (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 Gen_loop_rb_intermediate_v v' n';
    ret (v' :: bits, v'')
  end.

Lemma Gen_loop_rb_intermediate_nok_eq : forall k v x any_v,
    x <> 0 ->
    comp_spec eq (Gen_loop_rb_intermediate k v x)
              (Gen_loop_rb_intermediate_v any_v x).
Proof.
  destruct x as [ | x']; intros.
  - lia.
  - revert k v any_v.                           (* any_v is used here only *)
    induction x' as [ | x'']; intros.
    + simpl. fcf_skip_eq.
    + remember (S x'') as S_x''.
      simpl. fcf_skip_eq. fcf_skip.
Qed.

(* used in Oi_oc''. the difference between this function and Generate_noV is that
1. we assume the oracle passed in is the RB oracle
2. because we make that assumption, k is independent of v, so we resample it
before the bits are generated (for ease of skipping) rather than after *)
(* note oracle state won't be the same as Generate_noV_oc *)
Definition Generate_noV_oc_k (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta)  (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  k' <--$ $ {0,1}^eta;
  [bits, v'] <--$2 Gen_loop_oc v n;
  $ ret (bits, (k', v')).
(*
Print Oi_oc'.
Print Gen_loop_oc.*)

(* (let Generate_v_choose := *)
(*    if lt_dec callsSoFar i *)
(*    then Generate_rb_intermediate_oc *)
(*    else *)
(*     if beq_nat callsSoFar 0 *)
(*     then Generate_noV_oc *)
(*     else if beq_nat callsSoFar i then Generate_v_oc else Generate_v_PRF_oc in *)
(*  z <--$ Generate_v_choose state n; *)
(*  [bits, state']<-2 z; $ ret (bits, (S callsSoFar, state'))) *)

(* hardcode oracle everywhere to be RB oracle *)
(* moves k sampling to the beginning of each relevant function *)
Definition Oi_oc'' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let Generate_v_choose :=
      if lt_dec callsSoFar i
      then Generate_rb_intermediate_oc (* CHANGE: uses the last v *)
      else if beq_nat callsSoFar O
           then Generate_noV_oc_k (* CHANGE: k pulled to beginning; does use last v *)
           else if beq_nat callsSoFar i (* callsSoFar = i *)
                then Generate_v_oc_instantiate   (* CHANGE: kv pulled to beginning; does use last v *)
                else Generate_v_PRF_oc in
  [bits, state'] <--$2 Generate_v_choose state n;
    $ ret (bits, (S callsSoFar, state')).

(* uses genupdate rb on any call <= i *)
(* removes the extra k or k,v sampling before bit gen *)
Definition Oi_oc''' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let Generate_v_choose :=
      if lt_dec callsSoFar i
      then Generate_rb_intermediate_oc
      else if beq_nat callsSoFar O
           then Generate_rb_intermediate_oc_noV (* no k-sampling or v-sampling *)
           (* CHANGE: diff b/t Generate_v_oc_k and this fn is, this one removes the k sampling before bit gen *)
           else if beq_nat callsSoFar i (* callsSoFar = i *)
                then Generate_rb_intermediate_oc (* no k-sampling, only v-sampling *)
                (* diff b/t Generate_v_oc_instantiate and this fn is, this one removes the k sampling before bit gen *)
                else Generate_v_PRF_oc in
  [bits, state'] <--$2 Generate_v_choose state n;
    $ ret (bits, (S callsSoFar, state')).


Lemma Gen_loop_oc_states_diff : forall x state2 state1 v ,
   comp_spec
     (fun
        x0 y : list (Bvector eta) * Bvector eta * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((Gen_loop_oc v x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2)
     ((Gen_loop_oc v x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1).
Proof.
    clear f.
    induction x as [ | x']; intros; simplify.
    - fcf_spec_ret.
    - unfold rb_oracle. simplify. fold rb_oracle.
      fcf_skip_eq. simplify.
      fcf_skip. simplify. fcf_spec_ret.
      simpl in *. inversion H1. f_equal.
Qed.  

(* used below the below thm *)
Lemma Generate_v_swap_k_loop_eq : forall state1 state2 k v x,
   comp_spec
     (fun x0 y : list (Bvector eta) * KV * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((Generate_noV_oc (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((Generate_noV_oc_k (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  intros.
  unfold Generate_noV_oc.
  unfold Generate_noV_oc_k.

  simplify.
  (* it's not updating the state?? probably bc i'm NOT using an oracle, just {0,1}^n? *)

  (* swap the k-sampling with gen_loop on the right *)
  rewrite_r.
  (* well, are the states going to be equal?? should i get rid of states first and add ANOTHER intermediate game? *)
  instantiate (1 :=
                 (* Check ( *)
                 (z1 <-$
                     (Gen_loop_oc v x) (list (Blist * Bvector eta))
                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                  a <-$ { 0 , 1 }^eta;
                  [z2, state3]<-2 z1;
                  ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                            (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
  {
    (* Print Ltac prog_swap_r. *)
    rewrite_r.
    instantiate (1 :=
                   (a <-$ { 0 , 1 }^eta;
                    z1 <-$
                       (Gen_loop_oc v x) (list (Blist * Bvector eta))
                       (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                    [z2, state3]<-2 z1;
                    ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
    eapply comp_spec_eq_swap.
    fcf_skip_eq; kv_exist. simplify.
    fcf_skip_eq. simplify. fcf_spec_ret.
  }

  fcf_skip. instantiate (1 := (fun x y => fst x = fst y)).
  apply Gen_loop_oc_states_diff.

  simplify. unfold rb_oracle. simplify. fcf_skip_eq. simplify. simpl in *. inversion H2. subst.
  fcf_spec_ret.
Qed.

(* similar to the above lemma, but w/ v-updates *)
Lemma Generate_v_swap_k_loop_equiv_v_update : forall state1 state2 k v x,
   comp_spec
     (fun x0 y : list (Bvector eta) * KV * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((Generate_v_oc (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((Generate_v_oc_instantiate (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  intros.
  unfold Generate_v_oc.
  unfold Generate_v_oc_instantiate.
  simplify.

 (* swap the k-sampling under v-sampling and gen_loop on the right *)
  rewrite_r.
  (* well, are the states going to be equal?? should i get rid of states first and add ANOTHER intermediate game? *)
  instantiate (1 :=
                 (* Check ( *)
                 (res <-$ (v' <-$ {0,1}^eta;
                           z1 <-$
                              (Gen_loop_oc v' x) (list (Blist * Bvector eta))
                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                           ret (v', z1));
                  a <-$ { 0 , 1 }^eta;
                  [v', z1] <-2 res;
                  [z2, state3]<-2 z1;
                  ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                            (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
  {
    (* Print Ltac prog_swap_r. *)
    rewrite_r.
    instantiate (1 :=
                   (a <-$ { 0 , 1 }^eta;
                    res <-$ (v' <-$ {0,1}^eta;
                             z1 <-$
                                (Gen_loop_oc v' x) (list (Blist * Bvector eta))
                                (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                             ret (v', z1));
                    [v', z1] <-2 res;
                    [z2, state3]<-2 z1;
                    ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
    eapply comp_spec_eq_swap.
    fcf_skip_eq; kv_exist. simplify.
    fcf_skip_eq; kv_exist. simplify. fcf_skip_eq. simplify. fcf_spec_ret.
  }

  simplify. unfold rb_oracle. simplify. fold rb_oracle. fcf_skip_eq; kv_exist. simplify.
  fcf_skip; kv_exist.

  instantiate (1 := (fun x y => fst x = fst y)).
  apply Gen_loop_oc_states_diff.

  simpl in *. destruct b1. simpl in *. destruct p. inversion H2. subst.
  simplify. unfold rb_oracle. simplify. fcf_skip_eq. simplify.
  fcf_spec_ret.
Qed.

(* Oi_oc' to Oi_oc'' *)
Lemma oracleCompMap_rb_instantiate_inner : forall l i k v calls state1 state2,
    comp_spec (fun x y => fst x = fst y) (* rb state might not be equal *)
              ((oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                  (calls, (k, v)) l) (list (Blist * Bvector eta))
                                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)

              ((oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                  (* note the double prime here: this replaces OC_Query w Instantiate *)
                  (* also in Generate_noV_oc_k the one k call is moved up *)
                  (calls, (k, v)) l) (list (Blist * Bvector eta))
                                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  induction l as [ | x xs]; intros.
  - simplify; fcf_spec_ret.
  - simplify.
    (*  "(list (Bvector eta) * (nat * KV) * list (Blist * Bvector eta))%type" with
 "(list (Bvector eta) * KV * list (Blist * Bvector eta))%type". *)
    fcf_skip; kv_exist.
    (* might need casework on calls = i *)
    (* one call: Oi_oc' to Oi_oc'' *)
    +
      instantiate (1 := (fun x y => fst x = fst y)). (* rb state might not be equal *)
      simplify. Transparent Oi_oc'. Transparent Oi_oc''. simpl.
      destruct (beq_nat calls i).
      (* calls = i *)
      { destruct (lt_dec calls i).
        { (* calls < i *)
          simplify.
          fcf_skip; kv_exist.
          {
            simplify.
            fcf_skip; kv_exist.
            simplify.
            fcf_spec_ret.
            (* @v hey this works now due to the v-updating changing. also i started redoing the bottom cases *)
          }
        }
        (* calls >= i *)
        apply not_lt in n.
        destruct (beq_nat calls 0). 
        (* calls = 0 *)
        - apply Generate_v_swap_k_loop_eq.
        - (* calls != 0 *)
          apply Generate_v_swap_k_loop_equiv_v_update.
      } 
      (* calls != i *)
      { (* same computations, but with different rb_state *)
        (* fcf_skip; kv_exist. *)
        (* instantiate (1 := (fun c d => fst c = fst d)). *)
        {
          destruct (lt_dec calls i).
          - simplify. fcf_skip_eq; kv_exist. simplify.
            fcf_skip; kv_exist.
            simplify.
            fcf_spec_ret.
          - assert (beq_dec : calls = 0 \/ calls <> 0) by lia.
            destruct beq_dec as [beqtrue | beqfalse ].
            apply not_lt in n.
            apply beq_nat_true_iff in beqtrue.
            rewrite beqtrue.

            (* same case as above with k-sampling-swapping *)
             apply Generate_v_swap_k_loop_eq.

            (* SearchAbout (beq_nat _ _). *)
            apply beq_nat_false_iff in beqfalse. rewrite beqfalse.
            simplify. fcf_spec_ret.
        } 

        (* simplify. fcf_spec_ret. simpl in *. inversion H1. subst. f_equal. *)
      } 
    + simpl in H1. destruct b0. destruct b1. destruct p. simpl in *. destruct k0. inversion H1. subst.
      fcf_skip; kv_exist.
      simplify.
      instantiate (1 := (fun x y => fst x = fst y)).
      fcf_spec_ret.
      (* apply IHxs. *) (* ??? *)

      simpl in H4. destruct b2. destruct p. destruct p. simpl in *. inversion H4. subst.
      simplify.
      fcf_skip. destruct k0. apply IHxs.
      simplify. simpl in *. destruct p. inversion H7. subst.
      fcf_spec_ret.
Qed.
(* note i switched the order of k and v in Generate_v_oc_instantiate *)

Notation "A = B = C" := (A = B /\ B = C).

(* Oi_oc'' to Oi_oc''', case: calls > i *)
Lemma Oi_ocs_eq_calls_gt_i : forall l k v state1 state2 calls i,
    calls > i ->
   comp_spec (fun x y => fst x = fst y)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  induction l as [ | x xs]; intros.
  - simplify. fcf_spec_ret.
  - simplify.
    destruct (lt_dec calls i). lia.
    assert (calls_neq_i : calls <> i) by lia.
    apply beq_nat_false_iff in calls_neq_i.
    rewrite calls_neq_i. 
    assert (calls_neq_0 : calls <> 0) by lia.
    apply beq_nat_false_iff in calls_neq_0.
    rewrite calls_neq_0.
    simplify. fcf_skip; kv_exist.
    simplify. simpl in *. destruct l1. destruct p. inversion H2. subst.
    fcf_spec_ret.
    destruct p. inversion H2. subst.
    fcf_spec_ret.
Qed.

(* Oi_oc'' to Oi_oc''', case: i = 0 *)
Lemma oracleCompMap_rb_instantiate_outer_i_eq_0 : forall l i state,
    beq_nat i 0 = true ->                                        (* separate theorem *)
    comp_spec (fun x y => fst (fst x) = fst (fst y)) (* weaker precondition--just k's equal? *)
              ([k, v] <-$2 Instantiate;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                    (* note Oi_oc': need to rewrite w first theorem in outer *)
                    (O, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a)
              ([k, v] <-$2 Instantiate;
               k <-$ RndK;    (* instead of Instantiate, to deal with noV *)
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                    (O, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a).
Proof.
  intros.
  (* rename H into calls_leq_i. *)
  rename H into i_eq_0.
  (* swap kv in latter as in the mask thm above *)
  destruct l as [ | x xs].
  - simplify. unfold Instantiate. simplify. fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify. rewrite_r.
    { instantiate
      (1 :=
         (k0 <-$ RndK;
          a <-$ RndV;
          z <-$ ret (b, a);
          [_, v]<-2 z;
          a0 <-$ (x <-$ ret (nil, (O, (k0, v))); ret (x, state)); ret a0)).
    fcf_swap fcf_right. fcf_skip_eq; kv_exist. fcf_skip_eq; kv_exist. simplify.
    fcf_spec_ret. }
    fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_spec_ret.
  -
    (* calls = 0 and i = 0 *)
    Opaque Oi_oc''. Opaque Oi_oc'''.
    simplify.
    (* Skip the two initial Instantiates *)
    fcf_skip_eq; kv_exist. simplify.
    Transparent Oi_oc''. Transparent Oi_oc'''.
    simpl. apply beq_nat_true in i_eq_0. subst. simplify.
    (* Generate_noV_oc_k is inlined in first, Generate_rb_intermediate_oc_v in second *)
(*    Print Generate_noV_oc_k.*)
(*    Print Generate_rb_intermediate_oc.*) (* like the above but with no k sampling *)

    (* Skip the lined-up a-sampling (inline k-sampling) and k-sampling *)
    fcf_skip_eq; kv_exist.
    simplify. fcf_skip; kv_exist.

    (* Gen_loop_oc ~ Gen_loop_rb_intermediate *)
    { instantiate (1 := (fun x y => fst x = y)).
      revert b0 a state. induction x as [ | x']; intros.
      - simplify. fcf_spec_ret.
      - simplify. unfold rb_oracle. simplify. fold rb_oracle.
        fcf_skip_eq. fcf_skip. simplify. fcf_spec_ret.
    } 
    simpl in H1. destruct b3. inversion H1. subst.
    simplify. fcf_skip; kv_exist.

(* separate lemma for induction on rest of list, show calls > i *)
    { instantiate (1 := (fun x y => fst x = fst y)).
      apply Oi_ocs_eq_calls_gt_i; lia. }
    { simplify. simpl in H4. destruct p. inversion H4. subst. fcf_spec_ret. }
Qed.

Ltac rewrite_l := apply comp_spec_symm; eapply comp_spec_eq_trans_l.
  
(* this isn't actually used in the below thm because i can't get it to unify, so i inlined the proof *)
Lemma k_loop_swap_after : forall (i : nat) (xs : list nat)
                                 (state : list (Blist * Bvector eta)) (x : nat) (calls : nat) (k : Bvector eta),
   comp_spec eq
     (k0 <-$ RndK;
      a <-$
      (z0 <-$
       (z0 <-$
        (z0 <-$ (x0 <-$ { 0 , 1 }^eta; ret (x0, state));
         [z, s']<-2 z0;
         z1 <-$ (x0 <-$ Gen_loop_rb_intermediate k0 z x; ret (x0, s'));
         [z2, s'0]<-2 z1;
         ([bits, v'']<-2 z2; $ ret (bits, (k0, v'')))
           (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
           rb_oracle s'0);
        [z, s']<-2 z0;
        ([bits, state']<-2 z; $ ret (bits, (S calls, state')))
          (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
          rb_oracle s');
       [z, s']<-2 z0;
       ([res, state']<-2 z;
        z1 <--$
        oracleCompMap_inner
          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
             (pair_EqDec nat_EqDec eqDecState))
          (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) state' xs;
        [resList, state'']<-2 z1; $ ret (res :: resList, state''))
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s'); ret a)

     (v' <-$ {0,1}^eta;
      res <-$ Gen_loop_rb_intermediate k v' x; (* k0,v0 are swapped after, so just use any k,v in env *)
      k0 <-$ RndK;
      [bits, last_bv] <-2 res;
      a <-$
        (oracleCompMap_inner
           (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                       (pair_EqDec nat_EqDec eqDecState))
           (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (S calls, (k0, last_bv)) xs)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle state;
      a0 <-$
         ([z, s']<-2 a;
          ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
            (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
            rb_oracle s'); ret a0).
Proof.
  intros.
  rewrite_l.
  instantiate (1 :=
    (inter <-$ (v' <-$ { 0 , 1 }^eta;
      res <-$ Gen_loop_rb_intermediate k v' x;
      ret (v', res));
      k0 <-$ RndK;
      [v', res] <-2 inter;
      [bits, last_bv]<-2 res;
      a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
         (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
      a0 <-$
      ([z, s']<-2 a;
       ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s'); ret a0)).
  { simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. }
  apply comp_spec_symm.

  rewrite_l.
  instantiate (1 :=
      k0 <-$ RndK;
     (inter <-$
      (v' <-$ { 0 , 1 }^eta;
       res <-$ Gen_loop_rb_intermediate k v' x; ret (v', res));
      (let '(_, (bits, last_bv)) := inter in
            a <-$
            (oracleCompMap_inner
               (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                  (pair_EqDec nat_EqDec eqDecState))
               (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
               (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
            a0 <-$
            ([z, s']<-2 a;
             ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
               (list (Blist * Bvector eta))
               (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s'); 
            ret a0))).
  { eapply comp_spec_eq_swap. }

  apply comp_spec_symm.

  (* now k is at the top of both *)
  fcf_skip_eq; kv_exist.
  simplify.
  fcf_skip_eq; kv_exist.
  simplify.
  fcf_skip_eq; kv_exist.

  { revert a a0 k.
    induction x as [ | x']; intros; simpl.
    - fcf_spec_ret. 
    - fcf_skip_eq. fcf_skip_eq. }

  simplify.
  fcf_skip_eq; kv_exist.
Qed.

(* Oi_oc'' to Oi_oc''', third (and last) case: calls <= i and i != 0 *)
(* states same or different? going to have same so i can do eq (diff might let IH apply) *)
Lemma oracleCompMap_rb_instantiate_outer_i_neq_0 : forall l calls i state,
    calls <= i ->
    beq_nat i 0 = false ->                                        (* separate theorem *)
    comp_spec (fun x y => fst (fst x) = fst (fst y)) (* weaker precondition *)
              ([k, v] <-$2 Instantiate;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                    (* note Oi_oc': need to rewrite w first theorem in outer *)
                    (calls, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a)
              ([k, v] <-$2 Instantiate;
               k <-$ RndK;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                    (calls, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a).
Proof.
  intros.
  rename H0 into i_neq_0.
  fcf_skip_eq; kv_exist. simplify.
  (* fcf_irr_r. wfi. simplify. *)
  (* calls < i: kv don't matter *)
  (* calls = i: there's an extra instantiate inside *)

  rename b into k. rename b0 into v.
  revert calls i state H k v i_neq_0.
  induction l as [ | x xs]; intros. (* there isn't an induction in the i_eq_0 version, only a destruct *)
  (* base case *)
  - fcf_irr_r. unfold RndK. fcf_well_formed. simplify. fcf_spec_ret.

  (* induction: l = x :: xs *)
  - assert (H_ilen : calls < i \/ calls = i) by lia.
    destruct H_ilen.
    clear H.

    (* calls < i: apply induction hypothesis *)
    (* maybe i don't need induction? induct separately on inside *)
    (* this case might be hard because I need to "push" the extra instantiate on the right inside *)

    + Opaque Oi_oc''. Opaque Oi_oc'''.
      simplify. Transparent Oi_oc''. simplify.
      (* intuitively, what should the calls < i proof look like? *)
      destruct (lt_dec calls i). 2: lia.

      (* calls < i *)
      Transparent Oi_oc'''. simplify. destruct (lt_dec calls i). 2: lia.
      simplify.

      rewrite_r.
      (* eapply k_loop_swap_after. *)
      instantiate (1 :=      (v' <-$ {0,1}^eta;
      res <-$ Gen_loop_rb_intermediate k v' x; (* k0,v0 are swapped after, so just use any k,v in env *)
      k0 <-$ RndK;
      [bits, last_bv] <-2 res;
      a <-$
        (oracleCompMap_inner
           (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                       (pair_EqDec nat_EqDec eqDecState))
           (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (S calls, (k0, last_bv)) xs)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle state;
      a0 <-$
         ([z, s']<-2 a;
          ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
            (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
            rb_oracle s'); ret a0)).

      (* eapply k_loop_swap_after. *)
      (* pose proof (k_loop_swap_after i xs state x calls k) as k_loop_swap_after_init. *)
      (* apply k_loop_swap_after_init. *)

      (* ------ *)
      (* INLINE k_loop_swap_after PROOF (because eapply above can't unify... *)

      {
        rewrite_l.
        instantiate (1 :=
                       (inter <-$ (v' <-$ { 0 , 1 }^eta;
                                   res <-$ Gen_loop_rb_intermediate k v' x;
                                   ret (v', res));
                        k0 <-$ RndK;
                        [v', res] <-2 inter;
                        [bits, last_bv]<-2 res;
                        a <-$
                          (oracleCompMap_inner
                             (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                         (pair_EqDec nat_EqDec eqDecState))
                             (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
                             (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
                          (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                        a0 <-$
                           ([z, s']<-2 a;
                            ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
                              (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                              rb_oracle s'); ret a0)).
        { simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. }
        apply comp_spec_symm.

        rewrite_l.
        instantiate (1 :=
                       k0 <-$ RndK;
                     (inter <-$
                            (v' <-$ { 0 , 1 }^eta;
                             res <-$ Gen_loop_rb_intermediate k v' x; ret (v', res));
                      (let '(_, (bits, last_bv)) := inter in
                       a <-$
                         (oracleCompMap_inner
                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                        (pair_EqDec nat_EqDec eqDecState))
                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
                            (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
                         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                       a0 <-$
                          ([z, s']<-2 a;
                           ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
                             (list (Blist * Bvector eta))
                             (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s'); 
                       ret a0))).
        { eapply comp_spec_eq_swap. }

        apply comp_spec_symm.

        (* now k is at the top of both *)
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.

        { revert a a0 k.
          induction x as [ | x']; intros; simpl.
          - fcf_spec_ret. 
          - fcf_skip_eq. fcf_skip_eq. }

        simplify.
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_spec_ret.
      }

      (* END SWAP PROOF *)
      (* ----- *)

      apply comp_spec_symm.
      fcf_skip_eq; kv_exist.
      simplify.

      (* get the right side 2 lines together to apply IH *)
      fcf_skip_eq; kv_exist.
      simplify.
      eapply comp_spec_eq_trans_r.
      2:{ instantiate (1 :=
                     (* Check ( *)
                         (res <-$ (k0 <-$ RndK;
                                       a0 <-$
                                         (oracleCompMap_inner
                                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                                        (pair_EqDec nat_EqDec eqDecState))
                                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                                            (S calls, (k0, b)) xs) (list (Blist * Bvector eta))
                                         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                                       ret a0
                                      );
                              a2 <-$
                                 ([z, s']<-2 res;
                                  ([resList, state'']<-2 z; $ ret (a1 :: resList, state''))
                                    (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                                    rb_oracle s'); ret a2)).
          simplify. fcf_skip; kv_exist. simplify. fcf_skip_eq; kv_exist. } 

      fcf_skip; kv_exist.
      fcf_ident_expand_l.

      instantiate (1 := (fun
              x0
               y : list (list (Bvector eta)) * (nat * KV) *
                   list (Blist * Bvector eta) => fst (fst x0) = fst (fst y))).
      assert (Hcalls : S calls <= i) by lia.
      pose proof (IHxs (S calls) i state Hcalls k b i_neq_0) as IHxs_inst.
      apply IHxs_inst. 

      simpl in H2. destruct b1. destruct p. simpl in *. subst. simplify.
      fcf_spec_ret.
      
    (* ------------------ *)

    (* this just seems to work out of the box after changes *)
    (* calls = i *)
    + Opaque Oi_oc''. Opaque Oi_oc'''.
      simplify.
      (* this doesn't seem to be true. there's an extra instantiate in Oi_oc'' *)
      (* fcf_irr_l. wfi. simplify. *)
      Transparent Oi_oc''. Transparent Oi_oc'''.
      simpl.
      assert (beq_nat calls i = true).
      { apply Nat.eqb_eq. auto. }
      rewrite H1.
      destruct (lt_dec calls i). lia. (* we have calls = i *)
      (* need a diff oracle.
in i != 0: in the latter, there's an extra instantiate in front and no kv updating, so everything's in sync
in i = 0: in the former, there's only k updating inside. in the latter, there's an extra instantiate in front (k,v). so the v's are not in sync *)
      (* separate theorem for i = 0? seems easier -- destruct -- on first call, k update, then afterward, easy induction? 
that would work but would that still apply to prove the top-level theorem??
       *)
      rewrite <- H0 in i_neq_0.
      destruct (beq_nat calls 0).
      { inversion i_neq_0. }

      (* i != 0 *)
      { (*Print Generate_v_oc_instantiate.*)
        unfold Instantiate. simplify.
        (* now we have instantiate at the head of both, we can skip it, and the kv going into the loop  *)
        fcf_skip_eq; kv_exist.
        simplify. fcf_skip_eq; kv_exist. simplify.
        (* in fact only the k-update matters?? not true, we need the v's going in to be the same *) 
        (* loops are related *)
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = y)).
        (* both start with same v and x so postcondition holds *)
        { revert a a0 state. induction x as [ | x']; intros; simpl.
          - simplify. fcf_spec_ret.
          - unfold rb_oracle. simplify. fold rb_oracle. fcf_skip_eq.
            fcf_skip. simplify. fcf_spec_ret.
        }

        simpl in H3. destruct b1. inversion H3. subst.
        simplify.
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst y)).
        apply Oi_ocs_eq_calls_gt_i. lia.
        (* kv same AND calls > i! *)
        (* we're past RB and oracle, just PRFs here means oracles the same *)
        (* another induction w different states *)

        simplify. fcf_spec_ret. simpl in H6. destruct p. inversion H6. subst.
        simpl. reflexivity. }
Qed.

(* the oracleMap using choose_Generate (original computation) is equivalent to oracleCompMap using Oi_oc''' (the final one) 
for the second case of calls = i (leading to calls > i) *)
(* did this proof work? why did it break? *)
Lemma oracleMap_oracleCompMap_equiv_modified_calls_gt_i : forall l k v i state calls init,
   calls = i ->
   Forall (fun n => n > 0) l ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) *
             list (Blist * Bvector eta)) => x = fst y)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ choose_Generate (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k, v))) l)
     (z <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
      [bits, nkv, state']<-3 z; ret (init ++ bits, nkv, state')).
Proof.
  (* modeled off Gi_prog_equiv_rb_oracle_calls_eq_i *)
  Opaque choose_Generate. Opaque Oi_oc'''.
  destruct l as [ | x xs]; intros; rename H0 into blocks_neq_0.
  (* why am I destructing l instead of inducting? *)

  - simplify. fcf_spec_ret. simpl. repeat (split; auto).
    rewrite app_nil_r; reflexivity.
  -
    simplify.
    eapply comp_spec_seq.
    (* avoid fcf_skip, it will subst calls = i, which i don't want to link. TODO why? *)

    apply (nil, (0, (oneVector eta, oneVector eta))).
    apply ((nil, (0, (oneVector eta, oneVector eta)), nil)).

    (* when calls = i, one is Gen_loop_rb and the other is Gen_loop_oc using the rb_oracle *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  /\ fst (snd c) = S i /\ fst (snd (fst d)) = S i
                                  (* changed the postcondition; the keys now remain the same *)
                                  /\ fst (snd (snd c)) = fst (snd (snd (fst d))) )). (* TODO deleted =k, is that ok? *)
    (* 1 call: calls = i. why do i have to do the calls = i case again? shouldn't the other theorem cover it? *)
    { subst.
      Transparent choose_Generate. Transparent Oi_oc'''.
      unfold choose_Generate. unfold Oi_oc'''.
      simplify.
      (* casework on `i = 0`, `calls = i` and `calls > i` *)
      destruct (lt_dec i i). lia. 
      clear n.
      destruct (lt_dec i (S i)).
      2: lia. clear l.
      assert (idec : i = 0 \/ i <> 0) by lia.
      destruct idec as [ itrue | ifalse].
      apply beq_nat_true_iff in itrue.
      rewrite itrue.
      (* i = 0? shouldn't matter whether the v is updated an additional time in the latter *)
      (* TODO wait, i might need to pass the i=0 and i!=0 hypotheses down here? *)
      -
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (snd (fst y))
                    /\ fst (snd x) = fst (snd (fst y)) = k)).
        (* can we weaken the postcondition? *)
        unfold Generate_rb_intermediate. unfold Generate_rb_intermediate_oc_noV.
        simplify.
        fcf_irr_l.
        fcf_skip_eq; kv_exist.
        (* TODO factor out *)
        { 
          revert a k H0.
          induction x as [ | x']; intros; simplify.
          - (* using hypothesis that number of blocks is not 0 *)
            apply Forall_inv in blocks_neq_0. lia.
          - fcf_skip_eq.
        }
        (* hmm this saves the v, meaning the v gets updated... *)
        (* instantiate (1 := (fun x y => x = fst y)). *)
        (* unfold Gen_loop_rb. unfold Gen_loop_rb_intermediate. *)
        simplify. fcf_spec_ret.
        simpl in *. breakdown H1. simplify. fcf_spec_ret.
        destruct b. simpl in *. destruct k0. simpl in *. subst. auto.
      -
        (* presumably now `i <> 0`? what assumptions hold here? *)
        assert (H_i_eq : beq_nat i i = true) by apply Nat.eqb_refl.
        rewrite H_i_eq.
        apply beq_nat_false_iff in ifalse.
        rewrite ifalse. simplify.
        fcf_skip; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify. fcf_spec_ret. simpl. auto.
    }

    (* rest of calls -- induct on the new list *)
    { intros.
      (* don't do subst--there's an annoying link between calls and `i` that i don't want in my IH *)
      simplify. simpl in *. destruct p0. destruct p. destruct k1. simpl in *. destruct k0. simpl in H2. decompose [and] H2.
      rewrite H5. rewrite H3. rewrite H7. rewrite H9.
      clear H5 H3 H7 H9.
      clear H2 H1 H0.

      assert (n_eq : n = n0) by lia.
      rewrite <- H in H6.
      rewrite <- H in H4.
      rewrite n_eq.
      rename n0 into calls'.
      assert (H_calls : calls' > i) by lia.

      clear k v.
      rename b1 into k. rename b2 into v. rename l0 into rb_state.
      clear H6 n_eq H4 H. (* i cleared a lot of hypotheses here. might need them later? *)
      revert init k v rb_state i calls' H_calls l1.
      
      induction xs as [ | x' xs']; intros.

      (* xs = nil *)
      + simplify. fcf_spec_ret. 
      (* xs = x' :: xs', use IH *)
      + simplify.
        (*  "(list (Bvector eta) * KV * list (Blist * Bvector eta))%type" with
 "(list (Bvector eta) * KV)%type". *)
        fcf_skip; kv_exist.

        (* one call with calls > i (calls = S i) *)
        (* PRF oracle only *)
        clear calls. rename calls' into calls.

        instantiate (1 := (fun c d => c = fst d)).

        (* instantiate (1 := (fun c d => bitsVEq c d *)
        (*                               (* calls incremented by one *) *)
        (*                               /\ fst (snd c) = S calls *)
        (*                               /\ fst (snd (fst d)) = S calls *)
        (*                               (* KV equal *) *)
        (*                               /\ fst (snd (snd c)) = fst (snd (snd (fst d))))). *)
        {
          Transparent choose_Generate. Transparent Oi_oc'''.
          (* unfold choose_Generate. unfold Oi_oc'''. *)
          (* simplify. *)
          destruct (lt_dec calls (S i)). lia. (* calls > i, so ~(calls < S i) *)
          destruct (lt_dec calls i). lia.     (* calls > i, so ~(calls < i) *)
          assert (beq_nat calls 0 = false) as calls_neq_0.
          { apply Nat.eqb_neq. lia. }
          rewrite calls_neq_0. Opaque Generate_v.
          assert (beq_nat calls i = false) as calls_neq_i.
          { apply Nat.eqb_neq. lia. }
          rewrite calls_neq_i.
          Transparent Generate_v.
          simplify.
          fcf_spec_ret. 
          Opaque choose_Generate. Opaque Oi_oc'''.
        }

        simpl in H1. destruct b2. destruct p. simpl in *. inversion H1. subst.
        simplify.
        
        eapply comp_spec_eq_trans_r.
        destruct k0.
        eapply IHxs'. clear IHxs'.
        (* prove Forall on smaller list--though where is the middle element? *)
        { inversion blocks_neq_0. subst.
        inversion H5. subst.
        apply Forall_cons; auto. }
        
        lia. 
        
        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq.
          simplify. fcf_spec_ret.
          f_equal. f_equal.
          rewrite <- app_cons_eq.
          reflexivity.
        }
    } 
Qed.

(* TODO have to expand this with the fold and acc/++ *)
(* first case of the main proof (and the hardest case / main lemma): 
the original computation (oracleMap using choose_Generate) is equivalent to oracleCompMap Oi_oc'''
but only for the first case (calls <= i). is this induct, THEN destruct?
(TODO check the postcondition!) *)
Lemma oracleMap_oracleCompMap_equiv_modified : forall l k v i state calls init,
    calls <= i ->
    Forall (fun n => n > 0) l ->
    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) *
                list (Blist * Bvector eta)) => x = fst y)
      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
          z <-$ choose_Generate (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
         (init, (calls, (k,v))) l)
      ([acc', state'] <-$2 ((oracleCompMap_inner
                               (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                           (pair_EqDec nat_EqDec eqDecState))
                               (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                               (calls, (k, v)) l) (list (Blist * Bvector eta))
                                                  (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state);
       [bits, nkv] <-2 acc';
       ret (init ++ bits, nkv, state')).
Proof.
  (* modeled off Gi_prog_equiv_rb_oracle_compspec *)
  (* induct, then destruct *)
  induction l as [ | x xs]; intros; rename H0 into blocks_neq_0.
  - simplify. fcf_spec_ret. simpl. rewrite app_nil_r. repeat (split; auto).
  - assert (H_ilen : calls < i \/ calls = i) by lia.
    destruct H_ilen.
    clear H.

    (* calls < i *)
    Opaque choose_Generate. Opaque Oi_oc'''.
    simplify.
    fcf_skip; kv_exist.
    (* case: call on first element of list *)
    (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
    (* also strengthen it again because if calls < i then the keys must still be the same *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  (* calls incremented by 1 *)
                                  /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                  (* output keys are the input keys *)
                                  /\ fst (snd (snd c)) = k
                                  /\ fst (snd (snd (fst d))) = k)).
    (* includes calls *)
    (* one call with linked keys TODO *)
    {
      Transparent choose_Generate. Transparent Oi_oc'''.
      simpl.
      destruct (lt_dec calls i).
      2: lia.         (* contradiction *)
      clear l.                (* calls < i *)
      assert (H_calls_lt : calls < S i) by lia.
      destruct (lt_dec calls (S i)).
      2: lia. 
      fcf_skip; kv_exist.   (* Generate_rb_intermediate(_oc) *)
      (* postcondition: output keys are unchanged from input *)
      instantiate (1 := (fun x y => x = fst y /\ fst (snd x) = fst (snd (fst y)) = k)).
      unfold Generate_rb_intermediate.
      simplify.
      fcf_skip_eq; kv_exist.
      simplify.
      fcf_skip_eq; kv_exist.
      simplify.
      fcf_spec_ret.

      simpl in *. inversion H2. destruct b0. simpl in *. destruct b. destruct p. simpl in *. destruct k0. simpl in *.
      inversion H4. inversion H3. subst. simplify. fcf_spec_ret. simpl. auto.
      } 


    (* use IH *)
    { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k0. simpl in *.
      breakdown H2. 
      simplify.

      eapply comp_spec_eq_trans_r.
      eapply IHxs. lia.
      inversion blocks_neq_0; subst; auto.

      instantiate (1 := l).
      (* now prove oracleCompMap_inner's eq *)
      { fcf_skip_eq; kv_exist.
        simplify.
        fcf_spec_ret. f_equal. f_equal. rewrite <- app_assoc. f_equal.
      }
    } 
    
    (* calls = i *)
    + clear IHxs.
      clear H.
      apply oracleMap_oracleCompMap_equiv_modified_calls_gt_i; auto.
      (* apply Gi_prog_equiv_rb_oracle_calls_eq_i; lia. *) 
Qed.

Lemma maxBlocksAndCalls_all_nonzero : Forall (fun n : nat => n > 0) requestList.
Proof.
  clear H_numCalls.
  unfold requestList.
  induction numCalls as [ | calls'].
  - simpl. apply Forall_nil.
  - simpl. apply Forall_cons. apply H_blocksPerCall. apply IHcalls'.
Qed.   

Transparent choose_Generate.
Lemma Gi_prog_equiv_rb_oracle : forall (i : nat),
    Pr[Gi_prg (S i)] == Pr[Gi_rb i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_rb.
  unfold PRF_Adversary.
  unfold oracleCompMap_outer.
  fcf_to_prhl_eq.
  simplify.

  (* apply first theorem *)
  rewrite_r.
  (* replace Oi_oc' with Oi_oc'' *)
  instantiate
    (1 :=
         (a <-$ Instantiate;
      a0 <-$ ret (a, nil);
      a1 <-$
      ([z, s']<-2 a0;
       ([k, v]<-2 z;
        z0 <--$
        oracleCompMap_inner
          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
             (pair_EqDec nat_EqDec eqDecState))
          (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
          (0, (k, v)) requestList; [bits, _]<-2 z0; $ ret bits)
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s');
      z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)). 
  { fcf_skip_eq. simplify. fcf_skip. apply oracleCompMap_rb_instantiate_inner.
    simplify. simpl in *. destruct p. inversion H1. subst. fcf_skip_eq.
    simplify. fcf_reflexivity. }

  (* casework on i, apply second or third theorems *)
  flip. 
  assert (i_cases: beq_nat i 0 = true \/ beq_nat i 0 = false).
  { destruct i; auto. }
  destruct i_cases.

  (* i = 0 *)
  - rewrite_r.                  (* replace Oi_oc'' with Oi_oc''' *)
    instantiate
      (1 :=
         ([k,v] <-$2 Instantiate;
          k <-$ RndK;
          a0 <-$ ret ((k,v), nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k, v]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (* note triple prime *)
                  (0, (k, v)) requestList; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)).
    {
    (* need to isolate first 4 lines of each, rewrite with each, prove each equiv, then rewrite with oracleCompMap_rb_instantiate_outer_i_eq_0 *)
      flip. rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                  a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
                         (0, (k, v)) requestList) 
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil;
                 ret a);
            z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                 k <-$ RndK;
                 a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                         (0, (k, v)) requestList
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil);
                 ret a);
                z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      fcf_skip. flip. apply oracleCompMap_rb_instantiate_outer_i_eq_0. auto.

      simpl in H2. destruct b0. destruct a. simpl in *. destruct p. simpl in *. subst.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.

      simpl in H2. destruct p. destruct l1. simpl in *. rewrite H2.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.

      simpl in H2. rewrite H2.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.
    } 
    flip.
    unfold Instantiate. simplify.
    fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify.
    rewrite_r.
    instantiate
      (1 :=
         (k0 <-$ RndK;
          a <-$ RndV;
          z1 <-$ ret (b, a);
          [_, v]<-2 z1;
          a0 <-$ ret (k0, v, nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k1, v0]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                  (0, (k1, v0)) requestList; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b0, _]<-2 z; ret b0)).
    { fcf_swap fcf_right. prog_equiv. }
    flip.
    prog_equiv.
    (* factor out lemma and apply it to both cases *)
    fcf_skip. instantiate (1 := (fun x y => x = fst y)).
    (* they have the same k and v, former is S i, latter is i without updates in RB, so i hope this works! *)
    unfold oracleMap.
    pose proof oracleMap_oracleCompMap_equiv_modified.
    eapply comp_spec_eq_trans_r. apply H1. lia.
    apply maxBlocksAndCalls_all_nonzero.

    instantiate (1 := nil). fcf_ident_expand_r. fcf_skip_eq; kv_exist.
    simpl. fcf_spec_ret.

    simpl in H3. destruct b0. repeat destruct p. simpl in *. inversion H3. subst.
    fcf_ident_expand_l. simplify. prog_equiv. fcf_spec_ret.
  (* looks like the i=0 case is fully proved *)

  (* i != 0 *)
  - rewrite_r.
    instantiate
      (1 :=
         ([k,v] <-$2 Instantiate;
          (* [k,v] <-$2 Instantiate; *)
          k <-$ RndK;
          a0 <-$ ret ((k,v), nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k, v]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (* note triple prime *)
                  (0, (k, v)) requestList; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)).
    {
    (* need to isolate first 4 lines of each, rewrite with each, prove each equiv, then rewrite with oracleCompMap_rb_instantiate_outer_i_eq_0 *)
      flip. rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                  a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
                         (0, (k, v)) requestList) 
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil;
                 ret a);
            z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                 (* [k,v] <-$2 Instantiate; *)
                 k <-$ RndK;
                 a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                         (0, (k, v)) requestList
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil);
                 ret a);
                z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }

     fcf_skip. flip. 

      apply oracleCompMap_rb_instantiate_outer_i_neq_0.
      lia. auto.

      simpl in H2. destruct b0. destruct a. simpl in *. destruct p. simpl in *. subst.
      prog_equiv. fcf_spec_ret.

      simpl in H2. destruct p. destruct l1. simpl in *. rewrite H2.
      prog_equiv. fcf_spec_ret.

      simpl in H2. rewrite H2.
      prog_equiv. fcf_spec_ret.
    } 
    flip.
    unfold Instantiate. simplify.
    fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify.

    rewrite_r.
    instantiate (1 := 
                   (k0 <-$ RndK;
                    a <-$ RndV;
                    z1 <-$ ret (b, a);
                    [_, v]<-2 z1;
                    a0 <-$ ret (k0, v, nil);
                    a1 <-$
                       ([z, s']<-2 a0;
                        ([k1, v0]<-2 z;
                         z0 <--$
                            oracleCompMap_inner
                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                        (pair_EqDec nat_EqDec eqDecState))
                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                            (0, (k1, v0)) requestList; [bits, _]<-2 z0; $ ret bits)
                          (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                          rb_oracle s');
                    z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b0, _]<-2 z; ret b0) ).
    { fcf_swap fcf_right. prog_equiv. }

    fcf_skip_eq. simplify.
    fcf_skip_eq. simplify.
    apply comp_spec_symm.

    (* factor out lemma and apply it to both cases *)
    fcf_skip. 
    (* instantiate (1 := (fun x y => x = fst y)). *)
    unfold oracleMap.
    pose proof oracleMap_oracleCompMap_equiv_modified as om_ocm_equiv.
    eapply comp_spec_eq_trans_r. apply om_ocm_equiv. lia. apply maxBlocksAndCalls_all_nonzero.
    instantiate (1 := nil). fcf_ident_expand_r. fcf_skip_eq; kv_exist.
    simpl. fcf_spec_ret.

    simpl in H3. destruct b0.
    simpl in *. destruct p. destruct p. inversion H3. subst.
    simplify.
    fcf_ident_expand_l. simplify. prog_equiv. fcf_reflexivity.
Qed.

(* ----------------------- *Identical until bad section *)

Theorem Gen_loop_rb_intermediate_wf:
  forall a b c,
     well_formed_comp (Gen_loop_rb_intermediate b c a).

  clear f.
  induction a; intuition; simpl; fcf_well_formed.

Qed.

Theorem Generate_rb_intermediate_oc_wf :
  forall b a,
    well_formed_oc (Generate_rb_intermediate_oc b a).

    intros.
    unfold Generate_rb_intermediate_oc.
    fcf_simp.
    fcf_well_formed.
    apply Gen_loop_rb_intermediate_wf.
Qed.

Theorem Gen_loop_oc_wf : 
  forall a b0,
     well_formed_oc (Gen_loop_oc b0 a).
  clear f.
  induction a; intuition; simpl; fcf_well_formed.
Qed.

Theorem Generate_noV_oc_wf : 
  forall b a,
    well_formed_oc (Generate_noV_oc b a).

  intros.
  unfold Generate_noV_oc.
  fcf_simp.
  fcf_well_formed.
  apply Gen_loop_oc_wf.

Qed.

Theorem Generate_v_oc_wf : 
  forall b a,
     well_formed_oc (Generate_v_oc b a).
  clear f.
  intros.
  unfold Generate_v_oc.
  fcf_simp.
  fcf_well_formed.
  apply Gen_loop_oc_wf.
Qed.

Theorem Generate_v_PRF_oc_wf : 
  forall b a,
     well_formed_oc (Generate_v_PRF_oc b a).
  intros.
  unfold Generate_v_PRF_oc.
  fcf_simp.
  fcf_well_formed.

Qed.

Theorem oracleCompMap_inner_wf : 
  forall inputs s i,
  well_formed_oc
     (oracleCompMap_inner
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
        s inputs).

  induction inputs; intuition; simpl;
  fcf_well_formed.
  destruct (lt_dec a0 i).
  apply Generate_rb_intermediate_oc_wf.
  
  destruct (beq_nat a0 0).
  apply Generate_noV_oc_wf.
  destruct (beq_nat a0 i).
  apply Generate_v_oc_wf.
  eapply Generate_v_PRF_oc_wf.

Qed.


(* SAME PROOF AS PRF_A_randomFunc_eq_until_bad (with the computation order switched) *)
Theorem oracleCompMap__oracle_eq_until_bad_dups : forall (i : nat) b b0,
    comp_spec
     (fun y1 y2 : list (list (Bvector eta)) * list (Blist * Bvector eta) =>
        (* TODO fix args *)
        (* let (bits_rb, state_rb) := y1 in *)
        (* let (bits_rf, state_rf) := y2 in *)
        (* let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in *)
        (* let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in *)
        hasDups _ (fst (split (snd y1))) = hasDups _ (fst (split (snd y2))) /\
        (hasDups _ (fst (split (snd y1))) = false ->
         snd y1 = snd y2 /\ fst y1 = fst y2))

     ((z <--$
       oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (O, (b, b0)) requestList; [bits, _]<-2 z; $ ret bits)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil)
     ((z <--$
       oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (O, (b, b0)) requestList; [bits, _]<-2 z; $ ret bits)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        randomFunc_withDups nil).
Proof.
  intros.
  (* TODO review this *)
  eapply (fcf_oracle_eq_until_bad
            (fun x => hasDups _ (fst (split x)))
            (fun x => hasDups _ (fst (split x))) eq); intuition.

  - fcf_well_formed. 
  apply oracleCompMap_inner_wf.

  - intros. unfold rb_oracle. fcf_well_formed.
  - intros. unfold randomFunc_withDups. destruct (arrayLookup _ a b1); fcf_well_formed.
  - 
    subst.
    unfold randomFunc_withDups, rb_oracle.

    (* x2 is the list, a is the element. change variable names *)
    case_eq (arrayLookup _ x2 a); intuition.

      (* is a duplicate (a is in x2) *)
      (* now we need to prove that, given that a is in x2,
         the postcondition holds: 
         note that they both have state x2
       *)
    * fcf_irr_l.
      fcf_simp.
      (* note the simplified state here *)
      (*  (ret (b, (a, b) :: x2))
          (ret (b0, (a, b0) :: x2)) 
         - we know a is in x2 for both
         - b0 is some random bitvector, b is whatever the lookup returns for a *)
      fcf_spec_ret; simpl.

      (* note the 3 new goals *)
      (* obviously hasDups (thing1 :: x2) = hasDups (thing2 :: x2), since `hasDups x2` *)
      + remember (split x2) as z.
        destruct z.
(*        Print hasDups.*)
        (* Print in_dec. *) (* looks gnarly *)
        (* hasDups added and removed here! :^) *)
        simpl in *.
        trivial.

      (* snd y1 = snd y2 (if there are no dups in the whole state, then the states are the same. but we know there are dups in x2, the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec _) a l); intuition.
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite <- Heqz in H4; auto.

      (* fst y1 = fst y2 (exactly the same as above! if there are no dups in the whole state... but we know there are dups in the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec _) a l).
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite <- Heqz in H4; auto.

    * (* not a duplicate -- behaves like RB -- a is not in x2 *)
      fcf_skip.
      fcf_spec_ret.

    - unfold rb_oracle in *.
      fcf_simp_in_support.      (* 6 *)
      simpl in *.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec _) d l).
      intuition.
      intuition.

    - (* want to prove: for both oracles, if the state starts bad, it stays bad *)
      (* dups in c0 inputs, and when randomFunc_withDups is run with that state it returns output a and state b, there are dups in the inputs of that state *)
      unfold randomFunc_withDups in *. (* 5 *)
      (* NOTE this is a useful tactic *)
      fcf_simp_in_support.
      simpl.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec _) d l).
      intuition.             (* first element is dup *)
      intuition. (* by H -- the existing state has dups *)
Qed.

Theorem PRF_Adv_eq_until_bad : forall (i : nat),
   comp_spec 
     (fun a b : bool * list (Blist * Bvector eta) =>
        let (adv_rb, state_rb) := a in
        let (adv_rf, state_rf) := b in
        let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in
        let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in
        hasDups _ inputs_rb = hasDups _ inputs_rf /\
        (hasDups _ inputs_rb = false ->
         (* true -- if there are no duplicates, then the random function behaves exactly like RB, so the key is randomly sampled AND the v (going into the PRF) is also randomly sampled. so the outputs should be the same.
in fact, if there are no dups, PRF_Adv rf i = PRF_Adv rb i.
so, this means the comp_spec above is true?
does PRHL act like giving each the same "tape" of randomness for equality? *)
         state_rb = state_rf /\ adv_rb = adv_rf))
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil)
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        randomFunc_withDups nil).
Proof.
  intros.
  unfold PRF_Adversary.
  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  fcf_skip.
  apply oracleCompMap__oracle_eq_until_bad_dups.

  (* ------ *)
  fcf_simp.
  intuition.
  rename b1 into state_rb_.
  rename l0 into state_rf_.
  rename a0 into bits_rb_.
  rename l into bits_rf_.

  (* case_eq shows up in both *)
(*  Print Ltac case_eq.*)
(*  Locate Ltac case_eq.*)
  (* TODO what is this? *)

  (* case_eq (hasInputDups state_rb_); intuition. *)
  case_eq (hasDups _ (fst (split (state_rb_)))); intuition.

  (* duplicates exist, computations are irrelevant *)
  - 
    fcf_irr_l.
    fcf_irr_r.
    rename a into adv_rb_.
    rename b1 into adv_rf_.
    fcf_spec_ret.
    (* true=false in hypotheses *)
    (* hasInputDups state_rb_ = true (by case_eq) and false (by assumption in postcondition) *)
    congruence.

  (* no duplicates, equality is preserved *)
  (* automatically applied dups = false to get that the states and outputs are the same *)
  - simpl in *.
    subst.
    fcf_skip.
    fcf_spec_ret.
Qed.

(* First assumption for id until bad: the two games have the same probability of returning bad *)
(* uses provided oracle on call number i
   i = 2
                      0  1  2   3   4
   Gi_rf_bad i =     RB RB RF PRF  PRF
   Gi_rb_bad i =     RB RB RB PRF PRF
   bad event = duplicates in input on call number i *)
Lemma Gi_rb_rf_return_bad_same : forall (i : nat),
    Pr  [x <-$ Gi_rb_bad i; ret snd x ] ==
    Pr  [x <-$ Gi_rf_dups_bad i; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad. unfold Gi_rf_dups_bad.
  fcf_to_prhl_eq.
  fcf_inline_first.
  fcf_skip.
  (* different spec if you do `fcf_to_prhl` only, and in this location *)
  *
    apply PRF_Adv_eq_until_bad.
  *
    destruct b0.
    intuition.
    fcf_simp.
    unfold hasInputDups.
    rewrite H2.
    simpl.
    fcf_reflexivity.
Qed.

(* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" -- the two are basically the same if the bad event doesn't happen, so it's true.
         differences: 1. PRF re-keyed using RF vs. randomly sampled. but PRF re-keyed using something of length > eta, so it is effectively randomly sampled.
         2. the v going into the next call (if it exists) is randomly sampled vs. resulting from a RF call, but it doesn't matter *)

(* TODO: both of these proofs (in PRF_DRBG) rely on the PRF_Adv comp_spec lemma, which is proven by a bunch of casework. need another comp_spec lemma here on genupdate/prfadv? that adversary isn't even here anymore... *)

Theorem Gi_rb_rf_no_bad_same : forall (i : nat) (a : bool),
   evalDist (Gi_rb_bad i) (a, false) == evalDist (Gi_rf_dups_bad i) (a, false).
Proof.
  intros.
  fcf_to_prhl.                  (* note the auto-specification here *)
  (* it's NOT fcf_to_prhl_eq *)
  unfold Gi_rb_bad.
  unfold Gi_rf_dups_bad.
  fcf_skip.
  *
    apply PRF_Adv_eq_until_bad.
    (* but is this the right specification? *)
  *
    fcf_simp.
    intuition.
    fcf_spec_ret.

    pairInv.
    unfold hasInputDups.
    apply H3 in H6.
    intuition.
    subst.
    reflexivity.

    pairInv.
    unfold hasInputDups in *.
    rewrite H2.
    rewrite <- H2 in H6.
    apply H3 in H6.
    intuition.
    subst.
    fcf_reflexivity.
Qed.

Close Scope nat.
(* Applying the fundamental lemma here *)
Lemma Gi_rb_rf_identical_until_bad : forall (i : nat),
| Pr[x <-$ Gi_rf_dups_bad i; ret fst x] - Pr[x <-$ Gi_rb_bad i; ret fst x] | <=
                                              Pr[x <-$ Gi_rb_bad i; ret snd x].
Proof.
  intros. rewrite ratDistance_comm.

  fcf_fundamental_lemma.

  (* TODO: confirm if these assumptions seem true *)
  (* first assumption: they have same probability of returning bad *)
  - apply Gi_rb_rf_return_bad_same.

  (* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" *)
  - apply Gi_rb_rf_no_bad_same.
Qed.

(* ----------- End identical until bad section *)
(* ---------- Begin collision probability bound section *)

(* bad event is repetition in the random INPUTS. INPUTS = v :: (first n of outputs)? *)
(* modified PRF_Adversary to just return bits *)
Definition callMapWith (i : nat) : OracleComp Blist (Bvector eta) (list (list (Bvector eta))) :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) requestList;
  $ ret bits.

(* throw away the first input and the adversary, focus on bad event only *)
Definition Gi_rb_bad_no_adv (i : nat) : Comp bool :=
  [_, state] <-$2 callMapWith i _ _ rb_oracle nil;
  ret (hasInputDups state).

(* remove adversary (easy) *)
Lemma Gi_rb_bad_eq_1 : forall (i : nat),
    Pr [x <-$ Gi_rb_bad i; ret snd x] == Pr [Gi_rb_bad_no_adv i].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad.
  unfold Gi_rb_bad_no_adv.
  prog_equiv.
  fcf_irr_l.
  prog_equiv.
  fcf_spec_ret.
Qed.

Close Scope nat.

(* match the form in dupProb_const *)
Definition compMap_v (ls : list nat) (v : Bvector eta) :=
  x <-$ compMap _ (fun _ => {0,1}^eta) ls;
  ret hasDups _ (v :: x).

(* match the general form in Gi_rb_collisions_inner_eq_general_induct_irr_l's induction *)
Definition compMap_v_init (ls : list nat) (v : Bvector eta) (init : list (Blist * Bvector eta)) :=
  x <-$ compMap _ (fun _ => {0,1}^eta) ls;
  ret hasDups _ ((map (@to_list _ _) (v :: x)) ++ (map (@fst _ _ ) init)).

(* generalized version of case_on_i for induction hyp *)
Definition case_on_i_gen (i listLen callsSoFar nblocks : nat) (init : list (Blist * Bvector eta)) (v : Bvector eta) := 
  if ge_dec i (listLen + callsSoFar) then (ret (hasInputDups init))
  (* i = 0, so the last v is not an input. this case is exactly equivalent to adam’s gen_loop *)
  else if zerop i then (compMap_v_init (forNats (pred nblocks)) v init)
  else (compMap_v_init (forNats nblocks) v init).

Definition case_on_i (i ncalls nblocks : nat) (v : Bvector eta) := 
  if ge_dec i ncalls then (ret false)
  (* i = 0, so the last v is not an input. this case is exactly equivalent to adam’s gen_loop *)
  else if zerop i then (compMap_v (forNats (pred nblocks)) v)
  else (compMap_v (forNats nblocks) v).

Open Scope nat.

(* TODO split this out into a separate module (CompMap_v_equiv.v) *)
(* Transparent hasDups. *)

(*Require Import FCF.CompMap_v_equiv.*)

(* this is used *)
Lemma simplify_hasDups : forall (listLen i callsSoFar blocks : nat) (k v : Bvector eta) (l : list (Bvector eta))
                                rb_state1,
  comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec (Bvector_EqDec eta)))
         (Oi_oc' i) (callsSoFar, (k, v))
         (replicate listLen blocks)) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle rb_state1;
      a0 <-$
      ([z, s']<-2 a;
       ([resList, state'']<-2 z; $ ret (l :: resList, state''))
         (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle s');
      [_, rb_state2]<-2 a0; ret hasInputDups rb_state2)
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec (Bvector_EqDec eta)))
         (Oi_oc' i) (callsSoFar, (k, v))
         (replicate listLen blocks)) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle rb_state1;
      [_, rb_state2] <-2 a;
      ret hasInputDups rb_state2).
Proof. intros. prog_equiv. fcf_spec_ret. Qed.

Lemma rb_oracle_state_same_after_i : forall (listLen i callsSoFar blocks : nat) (k v : Bvector eta) left_state,
   callsSoFar > i ->
   comp_spec eq
     (a0 <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec (Bvector_EqDec eta))) 
         (Oi_oc' i) (callsSoFar, (k, v)) (replicate listLen blocks))
        (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle
        left_state;
      [_, left_state']<-2 a0; ret hasInputDups left_state')
     (ret hasInputDups left_state).
Proof.
  induction listLen as [ | listLen']; intros; rename H into calls_gt_i.
  - simplify. fcf_spec_ret.
  - simplify.
    destruct (lt_dec callsSoFar i). lia.
    assert (nonzero : callsSoFar <> 0) by lia.
    apply beq_nat_false_iff in nonzero.
    rewrite nonzero.
    assert (neq_i : callsSoFar <> i) by lia.
    apply beq_nat_false_iff in neq_i.
    rewrite neq_i.
    simplify.
    
    eapply comp_spec_eq_trans_r.
    apply simplify_hasDups.
    eapply comp_spec_eq_trans_r.
    eapply IHlistLen'.
    lia. fcf_spec_ret.
Qed.

(* TODO see if I can prove a more general version of compmap_v_eq using compMap_v_eq_h *)
(* From email: See compMap_v_eq_h in the file I attached on Apr 22. I think this is what you want. Note that this fact only holds if v and w are both not in init (you can also prove it when both are in init by removing the compMap statements with fcc_irr). *)

(* adding init on the right *)

Opaque hasDups.

Lemma split_map_fst : forall A B (l : list (A * B)), fst (split l) = map (@fst _ _) l.
Proof.
  induction l as [ | x xs]; intros; simpl; try reflexivity.
  destruct x. simpl. destruct (split xs). simpl in *. subst. reflexivity.
Qed.

(* simplify Generate_v_oc or Generate_noV_oc into the simpler compMap version that just samples a list of random bvectors *)
(* this lemma is a more general version that applies to both i=0 and i<>0 cases (Generate_noV_oc or Generate_v_oc) (after some simplification in the former) *)
Lemma Gi_rb_collisions_inner_eq_general_irr_l : forall (blocks : nat) (v : Bvector eta) (init : list (Blist * Bvector eta)),
   Forall (fun x : list bool * Bvector eta => length (fst x) = eta) init ->
   comp_spec eq
     (a <-$ { 0 , 1 }^eta;
      a0 <-$ ret (a, (to_list v, a) :: init);
      a1 <-$
      ([z, s']<-2 a0;
       z0 <-$
       (Gen_loop_oc z blocks) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
         (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
          output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
         s';
       [z1, s'0]<-2 z0;
       ([bits, v']<-2 z1;
        k' <--$ query to_list v' ++ zeroes; $ ret (bits, (k', v')))
         (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
         (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
          output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
         s'0); [_, init']<-2 a1; ret hasInputDups init')
     (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks);
      ret hasDups eqdbl
            (to_list v
             :: map (to_list (n:=eta)) x ++ map (fst (B:=Bvector eta)) init)).
Proof.
  clear f.
  induction blocks as [ | blocks']; intros v init inputs_len.
  - simplify.
    fcf_irr_l. rename a into key_input. simplify.
    fcf_irr_l. rename a into key_output. simplify.
    fcf_spec_ret. unfold hasInputDups. simpl.
    remember (split init) as z. destruct z. simpl.
    pose proof split_map_fst as split_map. rewrite <- split_map. rewrite <- Heqz. simpl.

    (* prove that key-input-extended cannot collide with rest of oracle inputs *)
    Transparent hasDups.
    unfold Blist. (* type synonym was interfering with rewrite *)
    remember (to_list v :: l) as rest.
    unfold hasDups at 1. fold hasDups. subst.
    Opaque hasDups.
    destruct (in_dec (EqDec_dec eqdbl) (to_list key_input ++ zeroes)) as [ is_in | not_in ].
    + assert (not_in : ~ In (to_list key_input ++ zeroes) (to_list v :: l)).
      {
        simpl. unfold not. intros not_in.
        destruct not_in as [ is_first_elem | in_fixed_len_list ].
        {
          assert (len_eq : length (to_list v) = length (to_list key_input ++ zeroes)).
          f_equal; trivial.
          rewrite app_length in *.
          
          repeat rewrite to_list_length in *.
          unfold zeroes in *.
          rewrite length_replicate in len_eq.
          rewrite plus_comm in len_eq.
          simpl in *.
          lia.
        }

        (* every element of l has length eta, and zeroes is nonempty *)
        {
          assert (l_eq : l = fst (split init)).
          { rewrite <- Heqz. reflexivity. }
          subst.
          rewrite Forall_forall in inputs_len.
          destruct (in_split_l_if init _ in_fixed_len_list). eauto.

          unfold to_list in *.
          apply inputs_len in H1; simpl in *; rewrite app_length in H1;
            unfold zeroes in H1; rewrite length_replicate in H1;
              rewrite plus_comm in H1; simpl in *.
          rewrite to_list_length in *. lia.
          
          (* match goal with  *)
          (*   | [ H1:  In (to_list key_input ++ zeroes, _) init |- _ ] =>  *)
          (*      apply inputs_len in H1; simpl in *; rewrite app_length in H1; *)
          (*      unfold zeroes in H1; rewrite length_replicate in H1; *)
          (*      rewrite plus_comm in H1; simpl in *; discriminate *)
          (* end. *)
        }
      }
      contradiction.
    + reflexivity.

  - simplify.
    fcf_skip. rename b into skip_v. simplify.
    specialize (IHblocks' skip_v ((to_list v, skip_v) :: init)).
    eapply comp_spec_eq_trans_r.
    (* clean up left side of IH *)
    instantiate (1 := 
       (a <-$ { 0 , 1 }^eta;
         a0 <-$ ret (a, (to_list skip_v, a) :: (to_list v, skip_v) :: init);
         a1 <-$
         ([z, s']<-2 a0;
          z0 <-$
          (Gen_loop_oc z blocks') (list (Blist * Bvector eta))
            (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
            (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
             output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
            s';
          [z1, s'0]<-2 z0;
          ([bits, v']<-2 z1;
           k' <--$ query to_list v' ++ zeroes; $ ret (bits, (k', v')))
            (list (Blist * Bvector eta))
            (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
            (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
             output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
            s'0); [_, init']<-2 a1; ret hasInputDups init')).
    { prog_equiv. fcf_spec_ret. }
    (* right side of H *)
    eapply comp_spec_eq_trans_l.
    apply IHblocks'.
    (* prove ind hyp on init *)
    {
      apply Forall_cons.
      simpl. apply to_list_length. auto.
    }

    simplify. prog_equiv. fcf_spec_ret.
    
    apply Permutation_hasDups.

    eapply perm_trans. 
    2:{ instantiate (1 := (to_list skip_v
           :: to_list v
           :: map (to_list (n:=eta)) a ++ map (fst (B:=Bvector eta)) init)).
        apply perm_swap. } 
    constructor.

    eapply perm_trans.
    instantiate (1 :=      ((map (to_list (n:=eta)) a ++
         (to_list v :: nil)) ++ map (fst (B:=Bvector eta)) init) ).
    { rewrite <- app_assoc. apply Permutation_app_head. simpl. reflexivity. }

    rewrite app_comm_cons.
    apply Permutation_app.
    apply Permutation_sym.
    apply Permutation_cons_append.
    reflexivity.
Qed.

(* apply above theorem for i <> 0, Generate_v_oc *)
Lemma Gi_rb_collisions_inner_eq_general_i_neq0 : forall (blocks : nat) (k v : Bvector eta) (init : list (Blist * Bvector eta)),
    Forall (fun x => length (fst x) = eta) init ->
  comp_spec eq
     (a <-$
      (Generate_v_oc (k, v) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle init;
      [_, init']<-2 a; ret hasInputDups init') 
      (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks); 
        ret hasDups _ ((map (@to_list _ _) (v :: x)) ++ (map (@fst _ _ ) init))).
Proof.
  intuition; simpl. 
  rename H0 into inputs_len.
  unfold rb_oracle.
  fcf_inline_first.
  revert k v init inputs_len. (*clear H.*)
  intros k_irr.
  apply Gi_rb_collisions_inner_eq_general_irr_l.
Qed.

(* apply theorem for i=0, Generate_noV_oc *)
Lemma Gi_rb_collisions_inner_eq_general_i_eq0 : forall (blocks : nat) (k v : Bvector eta)
                                                                   (init : list (Blist * Bvector eta)),
    Forall (fun x => length (fst x) = eta) init ->
    blocks > 0 ->
    comp_spec eq
              (a <-$
                 (Generate_noV_oc (k, v) blocks) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle init;
               [_, init']<-2 a; ret hasInputDups init')
              (x <-$
                 compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
                 (forNats (pred blocks));
               ret hasDups eqdbl
                   (map (to_list (n:=eta)) (v :: x) ++ map (fst (B:=Bvector eta)) init)).
Proof.
  intuition; simpl.
  rename H0 into inputs_len. rename H1 into blocks_neq_0.
  unfold rb_oracle.
  fcf_inline_first.
  destruct blocks as [ | blocks']. 
  - lia.
  - simplify. clear blocks_neq_0.
    (* blocks <> 0 -> reduces to lemma on i <> 0 *)
    (* clean up left side *)
    eapply comp_spec_eq_trans_l.

    instantiate (1 := 
                   (a <-$ { 0 , 1 }^eta;
                    a0 <-$ ret (a, (to_list v, a) :: init);
                    a1 <-$
                       ([z, s']<-2 a0;
                        z0 <-$
                           (Gen_loop_oc z blocks') (list (Blist * Bvector eta))
                           (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
                           (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
                              output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
                           s';
                        [z1, s'0]<-2 z0;
                        ([bits, v']<-2 z1;
                         k' <--$ query to_list v' ++ zeroes; $ ret (bits, (k', v')))
                          (list (Blist * Bvector eta))
                          (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta)))
                          (fun (state : list (Blist * Bvector eta)) (input : Blist) =>
                             output <-$ { 0 , 1 }^eta; ret (output, (input, output) :: state))
                          s'0); [_, init']<-2 a1; ret hasInputDups init')).
    { prog_equiv. fcf_spec_ret. }

    revert k v init inputs_len. (*clear H. *)rename blocks' into blocks.
    intros k_irr. 
    apply Gi_rb_collisions_inner_eq_general_irr_l. 
Qed.

Lemma to_list_injective : forall (T : Set) (n : nat) (a1 a2 : Vector.t T n), @to_list T n a1 = @to_list T n a2 -> a1 = a2.
Proof.
  intros.
  induction n as [ | n'].
  - pose proof vector_0 as nil_a1. specialize (nil_a1 T a1).
    pose proof vector_0 as nil_a2. specialize (nil_a2 T a2).
    subst. reflexivity.
  - pose proof vector_S as cons_a1. specialize (cons_a1 T n' a1). destruct cons_a1 as [ x1 cons_a1 ].
    destruct cons_a1 as [ v1 cons_a1 ]. subst.

    pose proof vector_S as cons_a2. specialize (cons_a2 T n' a2). destruct cons_a2 as [ x2 cons_a2 ].
    destruct cons_a2 as [ v2 cons_a2 ]. subst.

    unfold to_list in *. Transparent Vector.to_list. simpl in *. unfold Vector.to_list in H.
    fold (@Vector.to_list T) in *.
    inversion H. subst. clear H.
    f_equal.
    apply IHn'.
    apply H2.
    Opaque Vector.to_list.
Qed.


(* more general version of compMap_v_eq and compMap_v_eq_h, closer to the form of the induction *)
Lemma compMap_v_eq_init_list_placeholder : forall (a b : Bvector eta) init blocks,
    (* these two assumptions come from compMap_v_eq_init_list_h *)
    list_pred
      (fun x y : list bool =>
         x = y /\ x <> to_list a /\ x <> to_list b \/
                                    to_list a = x /\ to_list b = y \/ to_list b = x /\ to_list a = y)
      (map (fst (B:=Bvector eta)) init) (map (fst (B:=Bvector eta)) init) ->

    (In (to_list a) (map (fst (B:=Bvector eta)) init) <-> In (to_list b) (map (fst (B:=Bvector eta)) init)) ->

   comp_spec eq 
     (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks);
      ret hasDups eqdbl
            (map (to_list (n:=eta)) (a :: x) ++
             map (fst (B:=Bvector eta)) init))
     (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks);
      ret hasDups eqdbl
            (map (to_list (n:=eta)) (b :: x) ++
             map (fst (B:=Bvector eta)) init)).
Proof.
  intros.
  pose proof compMap_v_eq_init_list_h as compMap_v_eq_init_list.
  specialize (compMap_v_eq_init_list eta a b (map (fst (B:=Bvector eta)) init) blocks).
  Transparent map.
  simpl.
  Opaque map.
  Transparent eqdbl.
  unfold eqdbl.
  apply compMap_v_eq_init_list; auto.
Qed.

Lemma split_out_oracle_call_forall : 
    forall (listLen : nat) (k v v_prev : Bvector eta) (callsSoFar i blocks : nat) (init : list (Blist * Bvector eta)) ,
      callsSoFar <= i ->
   Forall (fun x : list bool * Bvector eta => length (fst x) = eta) init ->
   blocks > 0 ->

    (* these two assumptions come from compMap_v_eq_init_list_h *)
   (forall (a b : Bvector eta),
       list_pred
      (fun x y : list bool =>
         x = y /\ x <> to_list a /\ x <> to_list b \/
                                    to_list a = x /\ to_list b = y \/ to_list b = x /\ to_list a = y)
      (map (fst (B:=Bvector eta)) init) (map (fst (B:=Bvector eta)) init)) ->

    (forall (a b : Bvector eta),
                   (In (to_list a) (map (fst (B:=Bvector eta)) init) <-> In (to_list b) (map (fst (B:=Bvector eta)) init))) ->

   comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec (Bvector_EqDec eta))) 
         (Oi_oc' i) (callsSoFar, (k, v)) (replicate listLen blocks))
        (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle init;
      [_, state]<-2 a; ret hasInputDups state)
     (case_on_i_gen i listLen callsSoFar blocks init v_prev).
Proof.
  unfold case_on_i_gen.
  induction listLen as [ | listLen']; intros; rename H0 into oracle_input_lengths; rename H1 into blocks_neq_0;
  rename H2 into list_pred_init; rename H3 into in_same_init.

   (* base case: empty *)
  - simplify.
    destruct (ge_dec i callsSoFar). { fcf_spec_ret. } { lia. }

  (* inductive case *)
  - Opaque Oi_oc'. Opaque Generate_noV_oc. Opaque Generate_v_oc.
    rename H into calls_leq_i.
    Opaque zerop.
    simplify.
    assert (calls_size : callsSoFar < i \/ callsSoFar = i) by lia.
    destruct calls_size as [ calls_lt_i | calls_eq_i ].
    (* callsSoFar < i -> after this call, S callsSoFar <= i *)
    + clear calls_leq_i.
      Transparent Oi_oc'.
      simplify.

      (* clean up left side *)
      destruct (lt_dec callsSoFar i). 2: lia.
      clear l.

      (* strip off first call on left side, since it doesn't use the oracle *)
      unfold Generate_rb_intermediate_oc.
      simplify.
      fcf_irr_l. simplify.
      fcf_irr_l.
      {
        (* SearchAbout well_formed_comp. *)
        (* unfold Gen_loop_rb_intermediate. *)
        (* TODO *)
        apply Gen_loop_rb_intermediate_wf.
      }
      (* note the k doesn't change *)
      simplify.
      rename b into v'.

      eapply comp_spec_eq_trans_r.
      apply simplify_hasDups.
      rewrite plus_n_Sm.
      eapply IHlistLen'; try lia; try auto.

    (* calls = i *)
    + (* what's the form of the lemma i should apply here? *)
      clear calls_leq_i.
      (* here, the calls should both be skipped (since calls = i, the oracle is used) *)
      (* then induct on the rest *)
      Transparent Oi_oc'.
      simplify.
      subst.
      (* clean up left side *)
      destruct (lt_dec i i). lia.
      (* clean up right side *)
      destruct (ge_dec i (S (listLen' + i))). lia.

      (* depends on whether i = 0, so destruct on that *)
      destruct (zerop i) as [ i_eq_0 | i_gt_0 ].
      (* i = 0 *)
      {
        subst. simplify.

        (* replace v_prev with v, since the const vector in front doesn't matter *)
        eapply comp_spec_eq_trans_r.
        2: eapply (compMap_v_eq_init_list_placeholder v v_prev); auto.

        eapply comp_spec_eq_trans_r.
        (* can get rid of following oracleCompMap *)
        instantiate (1 :=
                       (a <-$
      (Generate_noV_oc (k, v) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle init;
                        [_, init'] <-2 a;
                        ret hasInputDups init')).
        { fcf_skip_eq.
          simplify.
          eapply comp_spec_eq_trans_r.
          + destruct b0.
            eapply simplify_hasDups.
          + destruct b0.
            eapply rb_oracle_state_same_after_i.
            lia.
        }
        clear n n0 IHlistLen'.
        
        (* apply lemma for i=0 *)
        (* there's probably a nicer way to do it with a lower bound for Gi_rb_collisions_inner_eq_general_induct_irr_l *)
        apply Gi_rb_collisions_inner_eq_general_i_eq0; auto.
      }
      (* i <> 0 *)
      { assert (i_neq_0 : i <> 0) by lia.
        apply beq_nat_false_iff in i_neq_0.
        rewrite i_neq_0.
        pose proof (beq_nat_refl i) as i_refl.
        rewrite <- i_refl.
        clear i_neq_0 i_refl.

        (* replace v_prev with v, since the const vector in front doesn't matter *)
        eapply comp_spec_eq_trans_r.
        2:{ unfold compMap_v_init.
            eapply (compMap_v_eq_init_list_placeholder v v_prev); auto. }

        (* pose proof (compMap_v_eq_init_list v v_prev init blocks nil) as compMap_v_eq_inner. *)
        (* destruct compMap_v_eq_inner as [ l_init compMap_v_eq_inner ]. *)
        (* eapply compMap_v_eq_inner. *)
        (* eapply (compMap_v_eq_inner v v_prev init blocks). *)
        
        (* should I replace Generate_v_oc with something else that doesn't use to_list?? *)
        (* maybe i should replace oracleCompMap inner with hasInputDups (state from Genupdate_oc) first *)
        simpl.

        eapply comp_spec_eq_trans_r. clear n n0 IHlistLen'.
        instantiate (1 :=
                       (a <-$
      (Generate_v_oc (k, v) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle init;
                        [_, init'] <-2 a;
                        ret hasInputDups init')).
        { fcf_skip_eq. 
          destruct b0.
          + eapply comp_spec_eq_trans_r.
          instantiate(1:= (a0 <-$
           (oracleCompMap_inner
              (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
                 (pair_EqDec nat_EqDec eqDecState))
              (list_EqDec (list_EqDec (Bvector_EqDec eta))) 
              (Oi_oc' i) (S i, (b0, b1)) (replicate listLen' blocks))
             (list (Blist * Bvector eta))
             (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle b;
           [_, rb_state2]<-2 a0; ret hasInputDups rb_state2)).
           simplify. apply simplify_hasDups.
          eapply rb_oracle_state_same_after_i. 
          lia.
        }
        clear n n0 IHlistLen'.
        
        apply Gi_rb_collisions_inner_eq_general_i_neq0.
        auto.
      } 
Qed.

Lemma Gi_rb_bad_eq_2' : forall (i : nat) (v : Bvector eta),
    Pr [Gi_rb_bad_no_adv i] == Pr[case_on_i i numCalls blocksPerCall v].
Proof.
  intros i v.

  fcf_to_prhl_eq.
  unfold Gi_rb_bad_no_adv.
  simplify.
  fcf_irr_l. wfi.
  simplify.
  (* clean up left *)
  eapply comp_spec_eq_trans_r.
  (* apply simplify_hasDups. *)
  instantiate (1 :=
                      (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec (Bvector_EqDec eta))) 
         (Oi_oc' i) (0%nat, (b, b0)) requestList)
        (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl (Bvector_EqDec eta))) rb_oracle nil;
                       [_, state] <-2 a;
                       ret hasInputDups state)).
  { prog_equiv. fcf_spec_ret. }

  eapply comp_spec_eq_trans_r.
  eapply split_out_oracle_call_forall; auto. lia.

  (* list_pred holds on (nil, nil) for any a, b, P *)
  { constructor. }

  (* In is same for any (nil, nil) *)
  { intros. Transparent map. simpl. constructor; intros; contradiction. Opaque map. }

  instantiate (1 := v).
  unfold case_on_i_gen.
  unfold case_on_i.
  unfold hasInputDups.
  Transparent hasDups.          (* init=nil *)
  simpl. Opaque hasDups.
  rewrite plus_comm. simpl.
  Opaque map.

  (* preemptively discharge the two last equality cases *)
  assert (hasDups_map_equiv : forall a, hasDups eqdbl (map (to_list (n:=eta)) (v :: a) ++ map (fst (B:=Bvector eta)) nil) =
                                        hasDups (Bvector_EqDec eta) (v :: a)).
  { intros. rewrite app_nil_r.
    pose proof hasDups_inj_equiv as hasDups_inj.
    specialize (hasDups_inj _ _ _ _ (v :: a) (to_list (n := eta))).
    rewrite hasDups_inj.
    reflexivity.
    apply to_list_injective. }

  destruct (ge_dec i numCalls); destruct (zerop i); try fcf_spec_ret; unfold compMap_v; prog_equiv; fcf_spec_ret.
Qed.

(* probability of bad event happening in RB game is bounded by the probability of collisions in a list of length (n+1) of randomly-sampled (Bvector eta) *)


Theorem hasDups_cons_orb : 
  forall (A  : Set)(eqd : EqDec A)(ls : list A)(a : A),
    hasDups _ (a :: ls) = (if (in_dec (EqDec_dec _) a ls) then true else false) || hasDups _ ls. 
 
   intuition.
   Transparent hasDups.
   simpl.
   destruct (in_dec (EqDec_dec eqd) a ls); intuition.
Qed.
 
Theorem compMap_hasDups_cons_orb : 
  forall (A : Set)(ls : list A) x,
    Pr[lb <-$ compMap _ (fun _ => {0,1}^eta) ls; ret hasDups _ (x :: lb)] ==
    Pr[lb <-$ compMap _ (fun _ => {0,1}^eta) ls; ret (if (in_dec (EqDec_dec _) x lb) then true else false) || hasDups _ lb].

  clear f.
  intuition.
  fcf_skip.
  rewrite hasDups_cons_orb.
  intuition.

Qed.

Theorem compMap_hasDups_cons_prob :
  forall (A : Set)(ls : list A) x, 
    (Pr[lb <-$ compMap _ (fun _ => {0,1}^eta) ls; ret hasDups _ (x :: lb)] <= S (length ls) ^ 2 / 2 ^ eta)%rat.

  intuition.
  rewrite compMap_hasDups_cons_orb.
  rewrite evalDist_orb_le.
  rewrite FixedInRndList_prob.
  rewrite dupProb.
  remember (length ls) as a.
  rewrite <- ratAdd_den_same.
  eapply leRat_terms; trivial.
  simpl.
  apply le_S.
  apply plus_le_compat; try lia.
Qed.

Close Scope nat.
Lemma Gi_Pr_bad_event_collisions : forall (i : nat) (v : Bvector eta),
   Pr  [x <-$ Gi_rb_bad i; ret snd x ] <= Pr_collisions.
Proof.
  intros.
  rewrite Gi_rb_bad_eq_1.
  pose proof Gi_rb_bad_eq_2' as select_call.
  specialize (select_call i v).
  (* sort of weird to have that v quantified but not mentioned in the theorem statement *)
  rewrite select_call. clear select_call.
  unfold case_on_i.
  destruct (ge_dec i) as [ i_ge_nc | i_nge_nc ].
  (* i out of bounds *)
  - Transparent evalDist. 
  fcf_compute.
  apply rat0_le_all.

  (* i in bounds *)
  - destruct (zerop i).
    (* i = 0 *)
    + unfold PRG.compMap_v.
      rewrite compMap_hasDups_cons_prob.
      rewrite forNats_length.
      unfold Pr_collisions.
      eapply leRat_terms; intuition.
      eapply Nat.pow_le_mono; lia.
    + unfold PRG.compMap_v.
      rewrite compMap_hasDups_cons_prob.
      rewrite forNats_length.
      reflexivity.
Qed.

(* Main theorem (modeled on PRF_DRBG_G3_G4_close) *)
(* Gi_rf 0:  RF  PRF PRF
Gi_prg 1:    RB PRF PRF

Gi_rf  1:    RB  RF PRF
Gi_prg 2:    RB  RB  PRF

Gi_rf  2:    RB  RB  RF
Gi_prg 3:    RB  RB  RB *)
Lemma Gi_replace_rf_with_rb_oracle : forall (i : nat), (* not true for i = 0 (and not needed) *)
  | Pr[Gi_rf i] - Pr[Gi_prg (S i)] | <= Pr_collisions. 
Proof.
  intros.
(*  Print Gi_rf.*)
  (* Gi_prg uses oracleMap, Gi_rb and Gi_rf both use oracleCompMap (oracle box) *)
  rewrite Gi_prog_equiv_rb_oracle. (* put Gi_prg into the same form using RB oracle *)
  (* TODO this might be wrong, maybe Gi_prg (S i) = Gi_rb (S i) *)
  (* shouldn't we be relating
     RB RB RF PRF with  <- Gi_rf 2
     RB RB RB PRF ? <-- Gi_prg 3 = Gi_rb 2
 *)

  rewrite Gi_rf_return_bad_eq. 
  rewrite Gi_rb_return_bad_eq. 
  rewrite Gi_rf_dups_return_bad_eq.

  (* NOTE still parametrized by i, so the hybrid matters *)
  rewrite Gi_rb_rf_identical_until_bad.
  apply Gi_Pr_bad_event_collisions.
  bv_exist.
Qed.

(* ---- PRF advantage *)
(* Step 1 *)
(* Gi_prf 2: RB RB PRF PRF PRF
   Gi_rf 2:  RB RB RF  PRF PRF 
need to use `Gi_prf i` instead of `Gi_prg i` because this matches the form of 
`Gi_rf` closer so we can match the form of PRF_Advantage*)

Lemma Gi_replace_prf_with_rf_oracle_i : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Game i.
Proof.
  intros i.
  (* don't need to unfold *)
  unfold Gi_prf.
  unfold Gi_rf.
  unfold PRF_Advantage_Game.
  reflexivity. 
Qed.

Open Scope nat.
Lemma comp_same_after_numCalls : forall (len n callsSoFar : nat) (k v : Bvector eta) init,
    (n > numCalls)%nat ->
    (callsSoFar + len = numCalls)%nat ->

    comp_spec eq
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ choose_Generate n s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (callsSoFar, (k, v))) (replicate len blocksPerCall))
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec (Bvector_EqDec eta)))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ choose_Generate (S n) s d; [r, scallsSoFar]<-2 z; ret (rs ++ r :: nil, scallsSoFar))
        (init, (callsSoFar, (k, v))) (replicate len blocksPerCall)).
Proof.
  induction len as [ | len']; intros; rename H into n_gt_len; rename H0 into len_invar.
  - simplify. fcf_spec_ret.
  - simpl. 
    simplify.
    destruct (lt_dec callsSoFar n) as [calls_lt_n | calls_gte_n].
    2: lia. 
    destruct (lt_dec callsSoFar (S n)) as [calls_lt_Sn | calls_gte_Sn].
    2: lia.
    fcf_skip_eq; kv_exist.
    simplify. destruct b.
    apply IHlen'. auto. lia.
Qed.

Theorem Gi_adjacent_hybrids_close_outofbounds :
  forall (i : nat),
    (i > numCalls)%nat ->
   Pr[Gi_prg i] == Pr[Gi_prg (S i)].
Proof.
  intros.
  unfold Gi_prg.
  fcf_to_prhl_eq.
  prog_equiv. rename b into k. rename b0 into v.
  (* unfold choose_Generate. *)
  (* TODO generalize and pull out *)
  unfold requestList.
  unfold oracleMap.
(* it should always be PRF on both sides *)
  apply comp_same_after_numCalls; auto.
Qed.
Close Scope nat.

Lemma Gi_replace_prf_with_rf_oracle : forall (i : nat),
    (i <= numCalls)%nat ->
| Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Max.
Proof.
  intros.
  eapply leRat_trans.
  apply Gi_replace_prf_with_rf_oracle_i.
  apply PRF_Advantage_max_exists.
  auto.
Qed.

(* TODO prove theorem for all n *)

(* Inductive step *)
(* let i = 3. 
Gi_prg i:      RB RB RB PRF PRF
Gi_prg (S i):  RB RB RB RB  PRF 

Gi_prg 0: PRF PRF PRF
Gi_rf  0:  RF PRF PRF
Gi_prg 1:  RB PRF PRF
Gi_rf  1:  RB  RF PRF *)
Theorem Gi_adjacent_hybrids_close :
  (* TODO: constructed PRF adversary *)
  forall (n : nat),
  | Pr[Gi_prg n] - Pr[Gi_prg (S n)] | <= Gi_Gi_plus_1_bound.
Proof.
  intros n.
  assert (n_dec : (n <= numCalls)%nat \/ (n > numCalls)%nat) by lia.
  destruct n_dec as [ n_lte | n_gt ].

  -  unfold Gi_Gi_plus_1_bound. intros.
     eapply ratDistance_le_trans. (* do the PRF advantage and collision bound separately *)
     rewrite Gi_prog_equiv_prf_oracle.    (* changed this *)
     apply Gi_replace_prf_with_rf_oracle; auto.        (* Basically already proven via PRF_Advantage magic *)
     apply Gi_replace_rf_with_rb_oracle.

  - rewrite Gi_adjacent_hybrids_close_outofbounds.
    assert (Heq : | Pr  [Gi_prg (S n) ] - Pr  [Gi_prg (S n) ] | == 0).
    { rewrite <- ratIdentityIndiscernables. reflexivity. }
    rewrite Heq.
    unfold Gi_Gi_plus_1_bound. unfold PRF_Advantage_Max. unfold Pr_collisions.
    apply rat0_le_all.
    auto.
Qed.

(* ------------------------------- *)

Definition hybrid_argument := distance_le_prod_f.

(* final theorem *)
Theorem G1_G2_close :
  | Pr[G_real] - Pr[G_ideal] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  rewrite Generate_move_v_update.
  rewrite G_real_is_first_hybrid.
  rewrite G_ideal_is_last_hybrid.
  specialize (hybrid_argument (fun i => Pr[Gi_prg i]) Gi_adjacent_hybrids_close numCalls).
  intuition.
Qed.

End PRG.

(* ------------------------------- *)
(* 
(* Backtracking resistance, using indistinguishability proof *)
(* this proof is invalid, see thesis for revised proof *)

(* Adversary, split into two *)
Parameter A1 : Comp nat.        (* currently unused *)
Parameter A2 : list (list (Bvector eta)) -> KV -> Comp bool.
(* Also the adversary is slightly different from the one above. How do we re-use the adv? *)

Definition G_real_dup : Comp bool := (* copy of G_real *)
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ Generate (k, v) requestList;
  A bits.

Definition G1_br_original : Comp bool :=
  (* blocksForEachCall <-$ A1; (* implicitly compromises after that # calls *) *)
  [k, v] <-$2 Instantiate;
  [bits, state'] <-$2 oracleMap _ _ Generate (k, v) requestList;
  A2 bits state'.

(* real world -- v-update move equivalence. need to prove that we need UpdateV -- needs an extra game at end of v-update equiv proof *)
Definition G1_br : Comp bool :=
  (* blocksForEachCall <-$ A1; (* implicitly compromises after that # calls *) *)
  (* TODO: not using this parameter yet, implicitly compromise after max calls (hardcoded)*)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate_noV (k, v) numCalls;
  [tail_bits, state''] <-$2 oracleMap _ _ Generate_v state' (tail requestList);
  (* again, don't need tail here *)
  (* v update moved to beginning of each Generate_v *)
  [k', v'] <-2 state'';
  v'' <- f k' (to_list v');      (* update v *)
  A2 (head_bits :: tail_bits) (k', v''). 

(* in general, how do we relate different adversaries in FCF? *)

(* A2 still cannot distinguish *)
(* how do I reuse the previous work? it depended on the adversary result, it wasn't an equivalence rewriting on the inside two lines *)
(* how would i even do this proof from scratch? would have to prove that PRF -> RF and RF -> RB yield equivalence etc. for A2 bits (k, v') <-- state *)
(* also, what about the extra UpdateV probabilities? *)

(* we don't know that Pr[G1_br] == Pr[G1_prg_dup]; that would be like assuming the state gives the adversary no extra info, which is like assuming what we want to prove? *)
(* all of our proof about G1_prg depended on the *adversary*, not the computations (but maybe they should have). *)
(* can we do the PRF_Advantage step in G1_br and reuse the RF->RB work from G1_prg? need to rephrase in terms of PRF_Adversary *)
Definition G1_prg_dup : Comp bool := (* copy of G1_prg *)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 Generate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ Generate_v state' (tail requestList);
  A (head_bits :: tail_bits).

(* TODO change this because I changed G_ideal *)
Definition G_ideal_dup : Comp bool := (* copy of G_ideal *)
  bits <-$ compMap _ Generate_rb requestList;
  A bits.

(* ideal world *)
(* 1a and 2: v ~ {0,1} -> f v ~ {0,1}? maybe assume it *)
(* or add an extra PRF_Advantage (random k -> f k v yields random v') *)
Definition G2_br : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ Generate_rb requestList;
  A2 bits (k, v).
(*
Lemma G_ideal_br_eq :
  Pr[G2_br] <= Pr[G_ideal_dup].
Proof.
  unfold G_ideal_dup, G2_br.
  unfold Instantiate.
  simplify. 
  fcf_irr_l. unfold RndK. fcf_well_formed.
  simplify.
  fcf_irr_l. unfold RndV. fcf_well_formed.
  simplify.
  fcf_skip.
  unfold RndK, RndV in *.
  (* should A2 be somehow constructed from A? *)
  (* also this isn't necessarily true unless A2 is constructed from A. A2 could just do dumb things. certainly Pr[best A2] == Pr[best A] (actually could it improve the adversary to give it more randomness?? probably not, if you're giving it a constant amt) *)
  (* Print Notation (Pr [ _ ]). *)
Admitted.
*)
(* 2 and 2a are clearly equivalent? (k,v) gives no information about bits, so remove k, v *)
(* this is where the indistinguishability proof ends -- don't know how to use this as an intermediate stage. is it possible to do G1_br ->(?) G1_prg -> G_ideal -> G2_br?
or somehow interleave so that we know the probability is "squeezed" to be small?
G1_br ->(?) G1_prg -> G2_br -> G_ideal *)

(* TODO other equivalence/bounding theorems *)

Theorem G1_G2_close_b2 :
  | Pr[G1_br_original] - Pr[G2_br] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  unfold G1_br.
  unfold G2_br.
Admitted.

(* ------------------------------- *)

  (* Notes on our proof: (might be outdated as of 1/1/16)

Show Generate_v's output indistinguishable from the output of this version, with v updated first: 

  v' <- f k v;
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (v'' ++ zeroes);
  ret (bits, (k', v'')).

(won't be exactly the same since v is updated an extra time in the beginning (first call to Generate_v) -- unless we have the 1st Generate_v oracle not update the v at all, then change all Generate_v oracles after the first one to update v in the first line, according to i in the ith game)

---

G1: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with PRF.

G2: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with random sampling.

P P P P P P
R R R R R R

Gi i: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want (q). the first i calls are done with random sampling, the rest are done normally, with PRF.

R R P P P P

Gi_0: the game as-is (PRF)

R R P P P P

in ith oracle call:
Gi_1: replace all calls to PRF, updating K with a random function 
      replace all calls to PRF, updating V with a random function 

R R F P P P

Gi_2: replace all calls to RF, updating K with randomly-sampled bits
      replace all calls to RF, updating V with randomly-sampled bits

R R R P P P

---

Oi: Generate+Update: modified version of PRG that does Generate n + Update with random sampling if < i, and PRF otherwise

G_i_si_close: 

Show
R R P P P P and
R R R P P P close
(there's no induction on q. we have that the ith oracle call uses the oracle with random bits, so just show that the (i+1)th oracle calls in G_i and G_{i+1} are close)

| Pr[G_i] - Pr[G_{i+1}] | <= PRF_advantage + Pr[collisions]
(note that the randomly sampled V is first updated AGAIN in the new version of Generate_v)

Pr[collisions] = 
"probability that /given the maximum input size n to any call/, the RF will be called on two identical inputs within the same oracle call"

the RF used both within the Generate loop and outside to generate the key?
but K <- RF(K, V || 0x00) so there can't be any collision within this call? *)

(* ----------------------------------- *)
(* Scratch work section -- ignore *)

Parameter A_t : Bvector eta -> bool.

Definition g1_test :=
  x <-$ {0,1}^eta;
  ret (A_t x).

Definition g2_test :=
  x <-$ {0,1}^eta;
  ret (A_t x).

Theorem g1_g2_eq : Pr[g1_test] == Pr[g2_test].
Proof.
  unfold g1_test. unfold g2_test.
  comp_skip.
  (* this also works, but you don't have to translate to prhl *)
  (* not clear on exactly what comp_skip is doing *)
  (* fcf_to_prhl_eq. *)
  (* comp_skip. *)
Qed.

(* ------ *)
(* How to get the state from an OracleComp: need to fully apply it with type params, oracle, and initial state *)

(* Definition Generate_v_oc_test (state : KV) (n : nat) : *)
(*   OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) := *)
(*   [k, v_0] <-2 state; *)
(*   v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *) *)
(*   [bits, v'] <--$2 Gen_loop_oc v n; *)
(*   k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *) *)
(*   $ ret (bits, (k', v')). *)

Definition getState_test (n : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [x1, x2] <-$2 Gen_loop_oc v n _ _ rb_oracle nil; (* note here *)
  ret true.

Parameter v_0 : Blist.
Check (OC_Query _ Blist).       (* ? *)

Parameter v : Bvector eta.
Parameter n : nat.
Check (Gen_loop_oc v n).
(* Gen_loop_oc v n
     : OracleComp (list bool) (Bvector eta)
         (list (Bvector eta) * Bvector eta) *)
*) 