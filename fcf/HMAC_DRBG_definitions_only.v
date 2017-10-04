Set Implicit Arguments.

Require Import fcf.FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import fcf.RndInList.
Require Import fcf.HasDups.
Require Import fcf.CompFold.
Require Import fcf.PRF.
Require Import fcf.OracleHybrid.
Require Import List.
Require Import fcf.PRF_DRBG.        (* note: had to move PRF_DRBG into FCF dir for this *)
Require Import Coq.Program.Wf.
Require Import fcf.OracleCompFold.

Local Open Scope list_scope.

(* Spec for HMAC-DRBG only, excluding theorems and proofs. 

   NIST standard: http://csrc.nist.gov/publications/nistpubs/800-90A/SP800-90A.pdf 
   In the NIST standard, HMAC-DRBG is described starting at page 44 (Section 10.1.2). 

   Thesis: https://www.cs.cmu.edu/~kqy/resources/thesis.pdf 
   In my thesis, see Section 2.1 for the HMAC-DRBG overview and Appendix B for descriptions of the Coq definitions. 

   See G1_prg (the initial game) for a "full run" of the DRBG. *)

Section PRG.

  (* note: the domain of the f is now Blist, not an abstract D
the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)
Variable eta : nat.

(* K and V are uniformly sampled from {0,1}^eta. *)
Definition RndK : Comp (Bvector eta) := {0,1}^eta.
Definition RndV : Comp (Bvector eta) := {0,1}^eta.

(* f is the (assumed) PRF (left abstract), that takes a key bitvector, an input list, and returns an output bitvector. *)
Variable f : Bvector eta -> Blist -> Bvector eta.

Definition KV : Set := (Bvector eta * Bvector eta)%type.

Definition to_list (A : Type) (n : nat) (v : Vector.t A n) := Vector.to_list v.

(* PRG functions *)

(* Instantiate the PRG's internal state (k,v). *)
(* This particular idealized Instantiate function does not reflect the NIST spec *)
Definition Instantiate : Comp KV :=
  k <-$ RndK;
  v <-$ RndV;
  ret (k, v).

(* Corresponds to the HMAC-DRBG Generate function (p48): given an internal state (k,v) and a number of requested blocks n,
returns a list of generated bits, along with the last bitvector. *)
(* It saves the last v and output it as part of the state *)
Fixpoint Gen_loop (k : Bvector eta) (v : Bvector eta) (n : nat)
  : list (Bvector eta) * Bvector eta :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k (to_list v) in
    let (bits, v'') := Gen_loop k v' n' in
    (v' :: bits, v'')           (* TODO change mine from (v ::) to (v ++), *or* prove indistinguishable (add another game in the beginning) *)
  end.

(* Demonstrates what the output of Gen_loop looks like. *)
Theorem Gen_loop_test : forall k v, Gen_loop k v 3 = (f k (to_list v)
    :: f k (to_list (f k (to_list v)))
       :: f k (to_list (f k (to_list (f k (to_list v))))) :: nil,
   f k (to_list (f k (to_list (f k (to_list v)))))).
Proof.
  reflexivity.
Qed.

(* Helper function for `zeroes` below. *)
(* Spec says "V || 0x00"; here we will use a list of 8 bits of 0 (a byte) *)
Fixpoint replicate {A} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

(* Corresponds to '0x00' in the HMAC-DRBG spec. *)
Definition zeroes : list bool := replicate 8 false.

(* For ease of proving, we combine the HMAC-DRBG Generate and Update functions into a function that generates the bits, then updates the state. *)
(* This is the original definition that mirrors the spec, which we do *not* use in G1_prg. 
It's here as reference implementation so we can prove that we can move each v-update to the first line of the next GenUpdate: 
[GenUpdate_original, GenUpdate_original, ...] = [GenUpdate_noV, GenUpdate, Genupdate, ...]  (proof omitted). *)
Definition GenUpdate_original (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  v'' <- f k' (to_list v');
  ret (bits, (k', v'')).

(*
(* This function is used for the first call (note that it has *no* v-updating) *)
Definition GenUpdate_noV (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  ret (bits, (k', v')).

(* Note this starts with a v-update, and does not end with one. *)
Definition GenUpdate (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);        (* new *)
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  ret (bits, (k', v'')).
*)
(* HMAC-DRBG takes as input an initial state (k,v) and a list of natural numbers, where each number is the number of blocks (bitvectors) requested for that call (e.g. [1,3,0]).

HMAC-DRBG returns a list of lists of bitvectors with the correct number of generated blocks in each list (e.g. [[b1], [b2, b3, b4], []]). *)

(* Crypto-related variables for the first game, defining the type of the adversary. It takes an input (a list of lists of blocks) and returns a probabilistic boolean computation attempting to distinguish the DRBG output from uniformly randomly sampled output.

 Non-adaptive adversary. Consequently, does not use OracleComp, because it won't be adjusting its input to the GenUpdate oracle (number of blocks requested from Gen_loop) based on the GenUpdate oracle's output, because the number of blocks and queries is fixed. *)
Variable A : list (list (Bvector eta)) -> Comp bool.
Hypothesis A_wf : forall ls, well_formed_comp (A ls).

(* For ease of proving, we assume (and hard-code) that the adversary has queried HMAC-DRBG with a list of nats, where each nat is the maximum number of blocks it is allowed to request. *)
Variable blocksPerCall : nat.       (* blocks generated by GenLoop *)
Variable numCalls : nat.        (* number of calls to GenUpdate *)
(*Hypothesis H_numCalls : numCalls > 0. (* need this for GenUpdate equivalence? *)*)
Definition maxCallsAndBlocks : list nat := replicate numCalls blocksPerCall.

(* Real-world crypto game.
Full run of the DRBG (splitting it into GenUpdate_noV for the first call, and passing that output to GenUpdate).
We can do this because we assume numCalls > 0. *)(*
Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;

  (* Generate blocks *)
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);

  (* Pass all blocks to adversary *)
  A (head_bits :: tail_bits).*)

Definition G1_prg_original : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_original (k, v) maxCallsAndBlocks;
  A bits.

End PRG.