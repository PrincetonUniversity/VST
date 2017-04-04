
Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.HasDups.
Require Import fcf.RndInList.
Require Import fcf.CompFold.
Require Import fcf.Tactics.

(* Indistinguishability definition for DRBGs *)
Section DRBG.

  (* The type of random seeds. *)
  Variable S : Set.
  Hypothesis S_EqDec : EqDec S.
  Variable RndS : Comp S.
  
  (* The type of DRBG outputs. *)
  Variable R : Set.
  Hypothesis R_EqDec : EqDec R.
  Variable RndR : Comp R.

  (* The DRBG *)
  Variable f : S -> R.

  Variable A : R -> Comp bool.

  Definition DRBG_G0 :=
    s <-$ RndS ;
    A (f s).

  Definition DRBG_G1 :=
    r <-$ RndR;
    A r.

  Definition DRBG_Advantage := | Pr[DRBG_G0] - Pr[DRBG_G1] |.

End DRBG.

Require Import fcf.PRF.

(* To keep things simple, we will assume that PRF outputs are bit vectors, and the DRBG output is a list of these bit vectors.  This setup can be generalized, if necessary.  *)

(* We need an adaptively-secure PRF because we use the PRF output to produce the next input, and therefore this input is unpredictable. *)

Local Open Scope list_scope.
Local Opaque evalDist.

Section PRF_DRBG.

  Variable Key D : Set.
  (* The range of the PRF is a bit vector of length eta. *)
  Variable eta : nat.
  Hypothesis D_EqDec : EqDec D.

  Variable RndKey : Comp Key.

  (* f is an adaptively-secure PRF. *)
  Variable f : Key -> D -> Bvector eta.

  (* For this construction, we need an injection from the range of the PRF to the domain.  This allows us to use the previous PRF output to compute the next one. *)
  Variable injD : Bvector eta -> D.
  Hypothesis injD_correct : 
    forall r1 r2, (injD r1) = (injD r2) -> r1 = r2.

  (* The length (in PRF output blocks) of the DRBG output is l.  This value must be positive. *)
  Variable l : nat.
  Hypothesis l_pos : l  > 0.

  (* Because the DRBG is constructed using feedback from the previous iteration, we need an initial value.  We assume an arbitrary bit vector and then inject it into the domain of the PRF.  This arrangement was chosen for simplicity, and it could easily be modified or generalized. *)
  Variable r_init : Bvector eta.
  Definition v_init := injD r_init.
  
  (* The computation used to obtain uniform random values in the range of the DRBG.  This computation is used only in the security definition. *)
  Definition RndOut := compMap _ (fun _ => {0, 1}^eta) (forNats l).
  
  (* We model the DRBG using a function that uses the previous output value (injected into the domain) as the current input value of the PRF. *)
  Fixpoint PRF_DRBG_f (v : D)(n : nat)(k : Key) :=
    match n with
        | O => nil
        | S n' => 
          r <- (f k v);
            r :: (PRF_DRBG_f (injD r) n' k)
    end.
  
  Definition PRF_DRBG (k : Key) :=
    PRF_DRBG_f v_init l k.
  
  (* The adversary against the DRBG. *)
  Variable A : list (Bvector eta) -> Comp bool.
  Hypothesis A_wf : forall c, well_formed_comp (A c).

  (* Step 1: inline definitions and simplify. *)
  Definition PRF_DRBG_G1 :=
    s <-$ RndKey ;
    A (PRF_DRBG_f v_init l s).

  (* This game is equivalent to the first game in the DRBG security definition. *)
  Theorem PRF_DRBG_G1_equiv : 
    Pr[DRBG_G0 RndKey PRF_DRBG A] == Pr[PRF_DRBG_G1].

    reflexivity.

  Qed.

  (* Step 2: use the PRF as an oracle.  This will allow us to apply the security definition and replace it in the next step.*)
  Fixpoint PRF_DRBG_f_G2 (v : D)(n : nat) :
    OracleComp D (Bvector eta) (list (Bvector eta)) :=
    match n with
        | O => $ ret nil
        | S n' => 
          r <--$ (OC_Query _ v);
            ls' <--$ (PRF_DRBG_f_G2 (injD r) n');
                $ ret (r :: ls')
    end.

  (* The constructed adversary against the PRF.
(takes something of type D -> Bvector eta, tries to guess whether it's RF or PRF)
the adversary can know the initial v, but not the K   *)
  Definition PRF_A : OracleComp D (Bvector eta) bool :=
    ls <--$ PRF_DRBG_f_G2 v_init l;
    $ A ls.

  (* return type Comp (bool * list (D * Bvector eta)) <-- tracks the state, and it's not even done explicitly (e.g. by oracleMap) *)

Check A.                        (* A : list (Bvector eta) -> Comp bool *)
(* TODO A isn't an OracleComp here but for mine it should probably be an oracle b/c of the hidden K,V state *)

  Theorem PRF_DRBG_f_G2_wf : 
    forall n v,
      well_formed_oc (PRF_DRBG_f_G2 v n).

    induction n; intuition; simpl in *;
    fcf_well_formed.
  Qed.

  Theorem PRF_A_wf : well_formed_oc PRF_A.

    unfold PRF_A; fcf_well_formed.
    apply PRF_DRBG_f_G2_wf.

  Qed.

  Definition PRF_DRBG_G2 :=
    s <-$ RndKey ;
    [b, _] <-$2 PRF_A unit _ (f_oracle f _ s) tt;
    ret b.

  (* In an intermediate step, put the construction in the form of a (deterministic) computation.  Then we can more easily change it to an oracle interaction in the following step. *)
  Fixpoint PRF_DRBG_f_G1_1 (v : D)(n : nat)(k : Key) :=
    match n with
        | O => ret nil
        | S n' => 
          r <-$ ret (f k v);
          ls <-$ (PRF_DRBG_f_G1_1 (injD r) n' k);
            ret (r :: ls)
    end.

  Definition PRF_DRBG_G1_1 :=
    s <-$ RndKey ;
    ls <-$ PRF_DRBG_f_G1_1 v_init l s;
    A ls.

  (* only difference: PRF_DRBG_f_G1_1 wraps everything in ret/comp *)
  (* TODO: if i prove that two things are comp_spec relation, how do i use that elsewhere? *)
  Theorem  PRF_DRBG_f_G1_1_eq_ret : 
    forall k n v,
       comp_spec eq (PRF_DRBG_f_G1_1 v n k) (ret (PRF_DRBG_f v n k)).

    induction n; intuition; simpl in *.
    
    (* comp_spec eq is registered as a setoid, so intuition will discharge simple goals. *)
    fcf_reflexivity.
    
    fcf_simp.
    (* rewrite IHn. *)
    fcf_transitivity.
    (* TODO how would I do this manually again? *)
    fcf_skip_eq.                (* this pulls in IHn, note it turns into PRF_DRBG_f *)
    fcf_reflexivity.
    fcf_simp.
    fcf_reflexivity.
  Qed.

  Theorem PRF_DRBG_G1_1_equiv :
    Pr[PRF_DRBG_G1] == Pr[PRF_DRBG_G1_1].
    
    unfold PRF_DRBG_G1, PRF_DRBG_G1_1.
    
     fcf_skip.
     fcf_to_prhl_eq.
     fcf_symmetry.
     fcf_transitivity.
     fcf_with PRF_DRBG_f_G1_1_eq_ret fcf_skip_eq. (* fcf_skip_eq with the comp_spec fact *)
     fcf_reflexivity.

     fcf_simp.
     fcf_reflexivity.

   Qed.

   Theorem PRF_DRBG_f_G1_1_G2_equiv :
     forall k n v,
     comp_spec (fun x1 x2 => x1 = fst x2) (PRF_DRBG_f_G1_1 v n k)
     ((PRF_DRBG_f_G2 v n) unit unit_EqDec
        (f_oracle f (Bvector_EqDec eta) k) tt).
       (* throw away snd tuple elem, also f oracle *)

     induction n; intuition; simpl in *.

     fcf_simp.
     fcf_spec_ret.

     fcf_skip.
     unfold f_oracle.           (* * *)

     (* we are left with a unification variable for the specification, we can supply a value for it by specializing the appropriate theorem. *)
     eapply (comp_spec_ret _ _ (fun x1 x2 => x1 = fst x2)).
     trivial.

     (* rest of proof *)
     simpl in *.
     intuition.
     subst.

     fcf_skip.                  (* uses induction hypothesis *)
     fcf_simp.
     fcf_spec_ret.
   Qed.

  Theorem PRF_DRBG_G1_G2_equiv : 
    Pr[ PRF_DRBG_G1 ] == Pr[ PRF_DRBG_G2 ].

    (* equality for rational numbers is a setoid, so we can rewrite with it. *)
    rewrite PRF_DRBG_G1_1_equiv.
    unfold  PRF_DRBG_G1_1,  PRF_DRBG_G2.
    unfold PRF_A.
    simpl.
    fcf_skip.

    fcf_inline_first.
    fcf_to_prhl_eq.

    (* unfold PRF_DRBG_f_G2. *)

    (* it showed the first two lines were equivalent, then skipped them *)
    (* rewrite PRF_DRBG_f_G1_1_G2_equiv. *)
    fcf_with PRF_DRBG_f_G1_1_G2_equiv fcf_skip.

    fcf_simp.
    simpl.
    fcf_inline_first.

    fcf_ident_expand_l.
    fcf_skip.
    fcf_simp.
    fcf_reflexivity.

  Qed.

  Print Ltac fcf_skip.
  Print Ltac dist_skip.
  Print Ltac prog_skip.

  (* Step 3: replace the PRF with a random function *)
  Definition PRF_DRBG_G3 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc ({0,1}^eta) _) nil;
    ret b.

Print PRF_DRBG_G2.

Check (randomFunc ({0,1}^eta)).
Print randomFunc.

Print PRF_A.
Check PRF_A.

Check (PRF_A _ _ (randomFunc ({0,1}^eta) _) nil).

(* PRF_Advantage RndKey ({ 0 , 1 }^eta) f D_EqDec (Bvector_EqDec eta) PRF_A *)

  Theorem PRF_DRBG_G2_G3_close : 
    | Pr[PRF_DRBG_G2] - Pr[PRF_DRBG_G3] | <= PRF_Advantage RndKey ({0,1}^eta) f _ _ PRF_A.
  Proof.
    (* all the work was done in getting game 1 to look like game 2 with f_oracle (oracle b/c randomfunc is an oracle b/c it has state). so now this proof is easy *)
    reflexivity.
  Qed.

  
  (* Step 4 : Replace the random function with random values.  This is the same as long as there are no duplicates in the list of random function inputs. *)
  Definition PRF_DRBG_G4 :=
    [b, _] <-$2 PRF_A _ _ (fun _ _ => x <-$ {0, 1}^eta; ret (x, tt)) tt;
    ret b.

  (* Step 3.1: Preserve duplicate inputs using an oracle that keeps track of all the queries. *)
  Definition randomFunc_withDups ls x :=
    y <-$ 
      (match (arrayLookup _ ls x) with 
        | Some y => ret y 
        | None => {0,1}^eta 
       end); 
    ret (y, (x, y) :: ls).

  Definition PRF_DRBG_G3_1 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc_withDups) nil;
    ret b.
  
  (* randomFunc_withDups behaves the same as randomFunc, even though the state information is different. *)
  Theorem randomFunc_withDups_spec : 
    forall x1 x2 a, 
      (forall x, arrayLookup _ x1 x = arrayLookup _ x2 x) ->
    comp_spec
     (fun y1 y2 : Bvector eta * list (D * Bvector eta) =>
      fst y1 = fst y2 /\
      (forall a0 : D,
       arrayLookup D_EqDec (snd y1) a0 = arrayLookup D_EqDec (snd y2) a0))
     (randomFunc ({ 0 , 1 }^eta) D_EqDec x1 a) (randomFunc_withDups x2 a).

    intuition.
    unfold randomFunc, randomFunc_withDups.
    rewrite H.
    case_eq (arrayLookup D_EqDec x2 a); intuition.
    fcf_simp.
    fcf_spec_ret.
    simpl.
    case_eq (eqb a0 a); intuition.
    rewrite eqb_leibniz in H1.
    subst.
    rewrite H.
    trivial.

    fcf_skip.
    fcf_spec_ret.
    simpl.
    rewrite H.
    trivial.

  Qed.

  Theorem PRF_DRBG_G3_1_eq : 
    Pr[PRF_DRBG_G3] == Pr[PRF_DRBG_G3_1].
    
    unfold PRF_DRBG_G3, PRF_DRBG_G3_1.
    fcf_to_prhl_eq.

    fcf_skip.

    eapply (fcf_oracle_eq (fun x1 x2 => forall a, arrayLookup _ x1 a = arrayLookup _ x2 a)); intuition.
    apply randomFunc_withDups_spec; intuition.

    fcf_simp.
    simpl in H1; intuition; subst.
    fcf_reflexivity.

  Qed.

  (* Expose the bad event to the game. *)
  Definition PRF_DRBG_G3_2 : Comp (bool * bool) :=
    [b, ls] <-$2 PRF_A _ _ (randomFunc_withDups) nil;
    ret (b, hasDups _ (fst (split ls))).

Check PRF_A. (* : OracleComp D (Bvector eta) bool *)
Check randomFunc_withDups.

  (* to get the state, you have to 2-tuple-comp-deconstruct an OracleComp in something
that is NOT an OracleComp (maybe?) AND give it the two type parameters, an oracle, and a start state *)

  (* ls : list (D * Bvector eta) <-- whether the list of INPUTS of the RF has dups  *)

  Theorem PRF_DRBG_G3_1_2_eq : 
    Pr[PRF_DRBG_G3_1] == Pr[x <-$ PRF_DRBG_G3_2; ret (fst x)].

    unfold PRF_DRBG_G3_1, PRF_DRBG_G3_2.
    simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    simpl.
    fcf_reflexivity.
  Qed.

  (* Obtain a new random value for all inputs.  This game is only equal to the previous game when there are no duplicates in the inputs. *)
  Definition PRF_DRBG_G3_3 :=
    [b, ls] <-$2 PRF_A _ _  (fun ls a => x <-$ {0, 1}^eta; ret (x, (a, x)::ls)) nil;
    ret (b, hasDups _ (fst (split ls))).

  (* proved equivalent to this *)
  (*   Definition PRF_DRBG_G4 :=
    [b, _] <-$2 PRF_A _ _ (fun _ _ => x <-$ {0, 1}^eta; ret (x, tt)) tt;
    ret b. *)

Check (PRF_A _ _ (fun _ _ => x <-$ {0, 1}^eta; ret (x, tt)) tt).
(* also unit *)
Print PRF_A.
Print PRF_DRBG_f_G2.

  (* ------- identical until bad section *)

  (* The "equal until bad" specification for randomFunc_withDups and the oracle that always produces a new random value.  This specification forms the core of the proofs of the two parts of the fundamental lemma in the following two theorems. *)
(* spec meaning "what function relates their outputs" or "what is the postcondition" *)
  Theorem PRF_A_randomFunc_eq_until_bad : 
    comp_spec
      (* they are equal when this function is applied to one of the results? both of them?
       or the function is true on the both of them? *)
      (* also this isn't computational? *)
      (fun y1 y2 : bool * (list (D * Bvector eta)) =>
      (*    let adv1 := fst y1 in *)
      (*    let adv2 := fst y2 in *)
      (*    let cache1 := snd y1 in *)
      (*    let cache2 := snd y2 in *)
      (*    let inputs1 := fst (split cache1) in *)
      (*    let inputs2 := fst (split cache2) in *)
      (*    (* the inputs should be the same anyway *) *)
      (*    hasDups _ inputs1 = *)
      (*    hasDups _ inputs2 /\ *)
      (*    (hasDups _ inputs1 = false -> *)
      (*     cache1 = cache2 /\ adv1 = adv2)) *)
      (*    (* randomFunc_withDups has no dups in its inputs -> its inputs and outputs are exactly the same as the one for random inputs and outputs & adversary cannot distinguish them. *) *)
         (* TODO how was this proved? *)
         (* same probability of bad *)
         hasDups _ (fst (split (snd y1))) =
         hasDups _ (fst (split (snd y2))) /\
         (* no bad -> identical output distributions *)
         (hasDups _ (fst (split (snd y1))) = false ->
          snd y1 = snd y2 /\ fst y1 = fst y2))
      (PRF_A _ _ randomFunc_withDups nil)
      (PRF_A _ _ 
             (fun (ls : list (D * Bvector eta)) (x : D) =>
         r <-$ { 0 , 1 }^eta; ret (r, (x, r) :: ls)) nil).
  Proof.
    (* oracles both start out in "good" state of `nil` *)
    (* TODO what is the next line? comment each assumption/conclusion in english *)
    (* Check fcf_oracle_eq_until_bad. *)
    Locate fcf_oracle_eq_until_bad.
    (* why this predicate? *)
    eapply (fcf_oracle_eq_until_bad
              (fun x => hasDups _ (fst (split x)))
              (fun x => hasDups _ (fst (split x))) eq);
      (* why was it applied with these arguments? *)
    intuition.
    (* what are the remaining obligations?? 
1. prove that the oraclecomp (PRF_A) is well formed
2. prove that the oracles (RF and RB) are well formed
3. prove that that the comp_spec holds on the two oracles
   ^ i don't see why this is useful or why the conclusion is useful
4. RF: if it starts out bad, it stays bad
5. RB: if it starts out bad, it stays bad 

so, how come we didn't have to reason about PRF_A? *)
    (* before:

   comp_spec
     (fun y1 y2 : bool * list (D * Bvector eta) =>
      hasDups D_EqDec (fst (split (snd y1))) =
      hasDups D_EqDec (fst (split (snd y2))) /\
      (hasDups D_EqDec (fst (split (snd y1))) = false ->
       snd y1 = snd y2 /\ fst y1 = fst y2))
     (PRF_A (list (D * Bvector eta))
        (list_EqDec (pair_EqDec D_EqDec (Bvector_EqDec eta)))
        randomFunc_withDups nil)
     (PRF_A (list (D * Bvector eta))
        (list_EqDec (pair_EqDec D_EqDec (Bvector_EqDec eta)))
        (fun (ls : list (D * Bvector eta)) (x : D) =>
         r <-$ { 0 , 1 }^eta; ret (r, (x, r) :: ls)) nil)

after:

subgoal 4 (ID 4424) is:
 comp_spec
   (fun y1 y2 : Bvector eta * list (D * Bvector eta) =>
    hasDups D_EqDec (fst (split (snd y1))) =
    hasDups D_EqDec (fst (split (snd y2))) /\
    (hasDups D_EqDec (fst (split (snd y1))) = false ->
     snd y1 = snd y2 /\ fst y1 = fst y2)) (randomFunc_withDups x1 a)
   (r <-$ { 0 , 1 }^eta; ret (r, (a, r) :: x2))

^ PRF_A went away!

subgoal 5 (ID 4465) is:
 hasDups D_EqDec (fst (split b)) = true <-- this is true now? can we use subgoal 4?
subgoal 6 (ID 4578) is:
 hasDups D_EqDec (fst (split b)) = true *)

    - apply PRF_A_wf.           (* 1 *)

    - unfold randomFunc_withDups. (* 2 *)
    destruct (arrayLookup D_EqDec a b);
    fcf_well_formed.

    - fcf_well_formed.          (* 3 *)

    - subst.                    (* 4 *)
      (* x1 = x2: oracle state 1 = oracle state 2 *)
    unfold randomFunc_withDups.
    Print randomFunc_withDups.
    (* x2 is the list, a is the element. change variable names *)
    case_eq (arrayLookup _ x2 a); intuition.

      (* is a duplicate (a is in x2) *)
      (* now we need to prove that, given that a is in x2,
         the postcondition holds: 
         note that they both have state x2
       *)
    * fcf_irr_r.
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
        Print hasDups.
        (* Print in_dec. *) (* looks gnarly *)
        (* hasDups added and removed here! :^) *)
        simpl in *.
        trivial.

      (* snd y1 = snd y2 (if there are no dups in the whole state, then the states are the same. but we know there are dups in x2, the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec D_EqDec) a l0); intuition.
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite unzip_eq_split in H3.
        remember (split x2) as z.
        destruct z.
        pairInv.
        simpl in *.
        intuition.

      (* fst y1 = fst y2 (exactly the same as above! if there are no dups in the whole state... but we know there are dups in the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec D_EqDec) a l0).
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite unzip_eq_split in H3.
        remember (split x2) as z.
        destruct z.
        pairInv.
        simpl in *.
        intuition.
    
    * (* not a duplicate -- behaves like RB -- a is not in x2 *)
      fcf_skip.
      fcf_spec_ret.

    - (* want to prove: for both oracles, if the state starts bad, it stays bad *)
      (* dups in c0 inputs, and when randomFunc_withDups is run with that state it returns output a and state b, there are dups in the inputs of that state *)
      unfold randomFunc_withDups in *. (* 5 *)
      (* NOTE this is a useful tactic *)
      fcf_simp_in_support.
      simpl.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec D_EqDec) d l0).
      intuition.             (* first element is dup *)
      intuition. (* by H -- the existing state has dups *)

    (* same proof *)
    - fcf_simp_in_support.      (* 6 *)
      simpl in *.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec D_EqDec) d l0).
      intuition.
      intuition.
  Qed.

  Theorem PRF_DRBG_G3_2_3_badness_same : 
    Pr  [x <-$ PRF_DRBG_G3_2; ret snd x ] ==
    Pr  [x <-$ PRF_DRBG_G3_3; ret snd x ].
  Proof.    
    unfold PRF_DRBG_G3_2, PRF_DRBG_G3_3.
    (* the dups stuff is in the game, not the adversary call *)
    fcf_inline fcf_left.
    fcf_inline fcf_right.
    fcf_to_prhl_eq.
    fcf_skip.

    unfold PRF_A.
    (* TODO: this theorem gets used in BOTH identical until bad assumptions *)
    apply PRF_A_randomFunc_eq_until_bad. (* identical until bad spec (I have a similar one on oracleCompMap_inner *)

    simpl in H1.
    inversion H1. clear H1.
    fcf_simp.
    simpl.
    (* simpl in *.  *) (* yields b = l0 *)
    (* we're using H2 -- first postcondition of comp_spec, unqualified -- eq probability of returning bad *)
    fcf_spec_ret.
  Qed.

  Theorem PRF_DRBG_G3_2_3_eq_until_bad : 
    forall a : bool,
      evalDist PRF_DRBG_G3_2 (a, false) == evalDist PRF_DRBG_G3_3 (a, false).
  Proof.
    intuition.
    unfold PRF_DRBG_G3_2, PRF_DRBG_G3_3.
    fcf_to_prhl.                (* proved via moving to comp_spec with iff, note the spec *)
    fcf_skip.
    apply PRF_A_randomFunc_eq_until_bad.
    (* nested identical until bad -- this is the big comp_spec above. has (bad = false) as an assumption *)
    fcf_simp.
    fcf_spec_ret.               (* note what this tactic does -- escapes the comp_spec, splits the tuple into equality *)

    simpl in *; pairInv; intuition; subst;
    trivial.
    
    simpl in *.
    pairInv.
    rewrite H2.
    rewrite <- H2 in H6.
    edestruct H3; intuition; subst.
    trivial.
  Qed.
  
  Theorem PRF_DRBG_G3_2_3_close : 
  | Pr[x <-$ PRF_DRBG_G3_2; ret (fst x)] - Pr[x <-$ PRF_DRBG_G3_3; ret (fst x)] | <=
                                           Pr[x <-$ PRF_DRBG_G3_3; ret (snd x)].
    
    rewrite ratDistance_comm.
    (* turns inequality to two equaliites *)
    fcf_fundamental_lemma.      (* * TODO *)
    (* TODO ask adam how he proved this (did he use "coins"?) *)
    (* what are the assumptions we need to prove? *)
    (* so these two games AREN'T identical until bad in the sense that there's no "code is the same before bad" and "after bad we can do whatever" *)

    symmetry.
    (* probability that they return bad is the same *)
    apply PRF_DRBG_G3_2_3_badness_same.

    intuition.
    symmetry.
    (* ? *)
    Print evalDist.
    Print Distribution.
    Locate evalDist.
    (* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" -- how to prove this? esp b/c the two games aren't in exactly the "identical until bad" form *)
    apply PRF_DRBG_G3_2_3_eq_until_bad.    
  Qed.

  (* ------- end identical until bad section *)

  Theorem PRF_DRBG_G3_3_G4_eq :
    Pr[ x <-$ PRF_DRBG_G3_3; ret (fst x) ] == Pr[ PRF_DRBG_G4 ].
    
    unfold PRF_DRBG_G3_3, PRF_DRBG_G4.
    simpl.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_skip.
    eapply (fcf_oracle_eq (fun x1 x2 => True)); intuition.    
    fcf_skip.
    fcf_spec_ret.
    simpl in H1.
    intuition; subst.
    fcf_simp.
    fcf_inline_first.
    simpl.
    fcf_skip.
    simpl; fcf_simp.
    fcf_reflexivity.
    
  Qed.

  
  (* Now we need to compute the probability of the "bad" event.  First we will simplify the game defining this event.*)

  (* The state of the random function is no longer necessary.  We can simplify things by changing the oracle interaction into a standard (recursive) computation. *)
  Fixpoint PRF_DRBG_f_bad (v : D)(n : nat) : Comp (list D) :=
    match n with
      | O =>  ret nil
      | S n' => 
          r <-$ {0,1}^eta;
          (* this is just a list of n random inputs starting with v; f is removed *)
          ls' <-$ (PRF_DRBG_f_bad (injD r) n');
          ret (v :: ls')
    end.

  Print PRF_DRBG_f.

Check PRF_DRBG_f_bad.

  Definition PRF_DRBG_G3_bad_1 :=
    ls <-$ PRF_DRBG_f_bad v_init l;
    ret (hasDups _ ls).
  
   Require Import Permutation.
   
   (* The relational specification on the new computation that produces the bad event.  We prove that the list of values produced by this computation is a permutation of the list produced by the oracle interaction in game 3.  Perhaps this could be an equality of we adjust the model, but a permutation works fine for our purposes, since the only thing that matters is the presence/absence of duplicates in the list. *)  
   (* not sure why ls is needed, why not []? needed for induction? *)
   (* don't we have to reason about injD in the latter? *)
   Theorem PRF_DRBG_f_bad_spec : 
     forall n v (ls : list (D * Bvector eta)), (* ls is the initial oracle state *)

       (* x1 : outputs * state, where state = inputs * outputs *)
     comp_spec (fun (x1 : list (Bvector eta) * list (D * Bvector eta)) (x2 : list D) =>
                  (* Perm (inputs_x1 (implicitly using init state)) (inputs in init oracle state ++ inputs_x2) whatever those are *)
                  Permutation (fst (split (snd x1))) ((fst (split ls)) ++ x2))
     ((PRF_DRBG_f_G2 v n) _ _
                          (* don't understand this -- PRF_DRBG_f_G2 returns oraclecomp?
                           what is this function doing? is it an oracle? *)
                          (* ok, this is the f oracle that just returns random values but keeps the state *)
        (fun (ls : list (D * Bvector eta)) (a : D) =>
         x <-$ { 0 , 1 }^eta; ret (x, (a, x) :: ls))
        ls)
     (PRF_DRBG_f_bad v n).

       Proof.
Print PRF_DRBG_f_G2.            (* OracleComp D (Bvector eta) (list (Bvector eta)) *)
Check (PRF_DRBG_f_G2 v_init O) _ _.
(*  : (D -> D -> Comp (Bvector eta * D)) ->
       D -> Comp (list (Bvector eta) * D) 
*)
Check         (fun (ls : list (D * Bvector eta)) (a : D) =>
         x <-$ { 0 , 1 }^eta; ret (x, (a, x) :: ls)).
(*  : list (D * Bvector eta) ->
       D -> Comp (Bvector eta * list (D * Bvector eta)) *)
Variable lsx : list (D * Bvector eta).
Check      ((PRF_DRBG_f_G2 v_init O) _ _
                          (* don't understand this -- PRF_DRBG_f_G2 returns oraclecomp?
                           what is this function doing? is it an oracle? *)
        (fun (ls : list (D * Bvector eta)) (a : D) =>
         x <-$ { 0 , 1 }^eta; ret (x, (a, x) :: ls))
        nil).
(*  : Comp (list (Bvector eta) * list (D * Bvector eta)) *)

     induction n; intuition; simpl in *.
     fcf_simp.
     fcf_spec_ret.
     simpl.
     rewrite app_nil_r.
     apply Permutation_refl.

     fcf_inline_first.
     fcf_skip.
     fcf_skip.                  (* gets rid of the InjD part *)
     fcf_spec_ret.
     simpl in H3.
     simpl.
     destruct (split ls).
     simpl in H3. simpl.
     eapply Permutation_trans.
     apply H3.
     apply Permutation_cons_app.
     apply Permutation_refl.
   Qed.

       (*   Definition PRF_DRBG_G3_3 :=
    [b, ls] <-$2 PRF_A _ _  (fun ls a => x <-$ {0, 1}^eta; ret (x, (a, x)::ls)) nil;
    ret (b, hasDups _ (fst (split ls))). *)
       (* ls is the state of the oracle : list (D * Bvector eta), so we are looking for duplicates in the input, not the DRBG's output? *)

Check PRF_A _ _  (fun ls a => x <-$ {0, 1}^eta; ret (x, (a, x)::ls)) nil.

       (*   (* The state of the random function is no longer necessary.  We can simplify things by changing the oracle interaction into a standard (recursive) computation. *)
  Fixpoint PRF_DRBG_f_bad (v : D)(n : nat) : Comp (list D) :=
    match n with
      | O =>  ret nil
      | S n' => 
          r <-$ {0,1}^eta;
          (* this is just a list of n random inputs starting with v; f is removed *)
          ls' <-$ (PRF_DRBG_f_bad (injD r) n');
          ret (v :: ls')
    end.

Check PRF_DRBG_f_bad.

  Definition PRF_DRBG_G3_bad_1 :=
    ls <-$ PRF_DRBG_f_bad v_init l;
    ret (hasDups _ ls). *)

   (* transition from game to bad game: show that you can throw away the outputs and just focus on the inputs *)
   Theorem PRF_DRBG_G3_bad_equiv : 
     Pr[x <-$ PRF_DRBG_G3_3; ret (snd x)] == Pr[PRF_DRBG_G3_bad_1].
   Proof.
     unfold PRF_DRBG_G3_3, PRF_DRBG_G3_bad_1.
     simpl.
     fcf_inline_first.
     fcf_to_prhl_eq.
     fcf_skip.
     * apply PRF_DRBG_f_bad_spec. (* inputs equal up to permutation, given some init state *)
     (* why the evar? *)

     * simpl in H1.
       fcf_inline_first.
       fcf_irr_l.               (* irrelevant, move to hypothesis *)
       fcf_simp.
       simpl.
       fcf_spec_ret.

       apply Permutation_hasDups. (* note permutation *)
       assumption.                (* where did this come from *)
   Qed.

   (* In the next simplification, we remove the v input from the recursive function, and simply put the random values in the list. *)
   Fixpoint PRF_DRBG_f_bad_2 (n : nat) :=
    match n with
        | O =>  ret nil
        | S n' => 
          r <-$ {0,1}^eta;
            ls' <-$ (PRF_DRBG_f_bad_2 n');
            ret (r :: ls')
    end.

Check PRF_DRBG_f_bad_2.

   Definition PRF_DRBG_G3_bad_2 :=
     ls <-$ PRF_DRBG_f_bad_2 (pred l);
     ret (hasDups _ (v_init :: (map injD ls))).

   (* This new recursive computation is similar to the previous one---we just need to shift everything over by one place, and map the injection over the output. *)
   Theorem PRF_DRBG_f_bad_2_equiv : 
     forall n v, 
     comp_spec (fun x1 x2 => x1 = v :: (map injD x2))
               (PRF_DRBG_f_bad v (S n)) 
               (PRF_DRBG_f_bad_2 n).

     induction n; intuition; simpl in *.
     fcf_irr_l.
     fcf_simp.
     fcf_spec_ret.

     fcf_skip.
     fcf_skip.
     fcf_spec_ret.
   Qed.

   Theorem PRF_DRBG_G3_bad_1_2_equiv : 
     Pr[PRF_DRBG_G3_bad_1] == Pr[PRF_DRBG_G3_bad_2].

     unfold PRF_DRBG_G3_bad_1, PRF_DRBG_G3_bad_2.
     fcf_to_prhl_eq.

     destruct l; simpl; intuition.
     fcf_simp.
     simpl.
     fcf_reflexivity.

     fcf_skip. (* TODO: comp_spec (with something other than eq) is applied here *)
     apply PRF_DRBG_f_bad_2_equiv.
     (* the postcondition becomes a hypothesis for the next goal! *)
     simpl in H1.
     subst.

     fcf_spec_ret.
   Qed.


   (* The previous recursive function is equivalent to mapping the computation that produces random values over a list of the appropriate length.  The form thet uses compMap can be unified with some existing theory to compute the probability of the event. *)
   Definition PRF_DRBG_G3_bad_3 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (v_init :: (map injD ls))).

   Theorem PRF_DRBG_f_bad_2_compMap_equiv :
     forall n, 
     comp_spec eq
     (PRF_DRBG_f_bad_2 n)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats n)).

     induction n; intuition; simpl in *.
     fcf_reflexivity.
     fcf_skip.
     fcf_skip.
     apply IHn.
     subst.
     fcf_reflexivity.

   Qed.

   Theorem PRF_DRBG_G3_bad_2_3_equiv : 
     Pr[PRF_DRBG_G3_bad_2] == Pr[PRF_DRBG_G3_bad_3].

     unfold PRF_DRBG_G3_bad_2, PRF_DRBG_G3_bad_3.
     fcf_to_prhl_eq.
     pose proof PRF_DRBG_f_bad_2_compMap_equiv.
     fcf_skip.

   Qed.
   
   (* Don't apply the injection to the random values and initial input. *)
   Definition PRF_DRBG_G3_bad_4 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (r_init :: ls)).

    Theorem PRF_DRBG_G3_bad_3_4_equiv : 
     Pr[PRF_DRBG_G3_bad_3] == Pr[PRF_DRBG_G3_bad_4].

     unfold PRF_DRBG_G3_bad_3, PRF_DRBG_G3_bad_4.
     fcf_to_prhl_eq.
     fcf_skip.
     fcf_spec_ret.
     unfold v_init.

     symmetry.
     erewrite (hasDups_inj_equiv _ _ (r_init :: b)).
     simpl. eauto.
     trivial.
   Qed.

   (* HasDups.v has a theorem that computes the probability of duplicates in a list of random values.  We need a form of the dupProb theorem that allows the first item in the list to be fixed.  *)
    (* TODO: this theorem + how it uses RndInList + how it's used *)
   Theorem dupProb_const : 
    forall (X : Set)(ls : list X)(v : Bvector eta),
      (* why not put PRF_DRBG_G3_bad_4 here? *)
      Pr[x <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (hasDups _ (v :: x))] <= 
      ((S (length ls)) ^ 2 / 2 ^ eta).

     intuition.
     (* Either the list of random values has duplicates, or v is in this list.  The probability value that we want is (at most) the sum of the probabilities of these two events.  The evalDist_orb_le theorem allows us to reason about them separately.  Put the game in a form that unifies with this theorem. *)

     fcf_rewrite_l (Pr[x <-$ compMap (Bvector_EqDec eta) (fun _ : X => { 0 , 1 }^eta) ls;
                      ret ((if (in_dec (EqDec_dec _) v x) then true else false) || (hasDups (Bvector_EqDec eta) x)) ] 
                 ).
     fcf_skip.
     simpl.
     destruct ( in_dec (EqDec_dec (Bvector_EqDec eta)) v x).
     simpl.
     intuition.
     rewrite orb_false_l.
     intuition.

     rewrite evalDist_orb_le.

     (* Use a theorem from the library to determine the probability that v is present in the random list. *)
     rewrite FixedInRndList_prob.
     (* Now determine the probability that there are duplicates in the random list. *)
     rewrite dupProb.
     
     (* The rest is just arithmetic. *)
     simpl.
     rewrite mult_1_r.
     cutrewrite ( S (length ls + length ls * S (length ls)) =  (S (length ls) + length ls * S (length ls)))%nat.
     rewrite ratAdd_num.
     eapply ratAdd_leRat_compat.
     eapply leRat_terms;
     omega.
     eapply leRat_terms.
     eapply mult_le_compat; omega.
     trivial.
     omega.
   Qed.

   Theorem PRF_DRBG_G3_bad_4_small :
      Pr[PRF_DRBG_G3_bad_4] <= (l ^ 2 / 2 ^ eta).

     unfold PRF_DRBG_G3_bad_4.
     rewrite dupProb_const.
     destruct l.
     omega.
     
     simpl.
     rewrite forNats_length.
     rewrite mult_1_r.
     reflexivity.
   Qed.

   (* Combine all of the results related to the G3 games to show that G3 and G4 are close. *)
   Theorem PRF_DRBG_G3_G4_close : 
     | Pr[ PRF_DRBG_G3 ] - Pr[  PRF_DRBG_G4 ] | <= (l^2 / 2^eta).
   Proof.
     (* randomFunc -> randomFunc_withDups *)
     rewrite PRF_DRBG_G3_1_eq.

     (* identical until bad: both return fst (expose bad event?), <= collision bound *)
     (* randomFunc_withDups; bad event: inputs to RF have dups *)
     (* the outputs of the RF are random AND are the new inputs to the RF *)
     Print PRF_A. Print PRF_DRBG_f_G2.
     rewrite PRF_DRBG_G3_1_2_eq. (* returning 1 (not bad) *)
     (* new random value for all inputs. bad event: duplicate input *)
     rewrite <- PRF_DRBG_G3_3_G4_eq. (* returning 1 (not bad) *)

     (* from diff of adv guessing correct bit in 2 games, to just the pr of adv guessing correct bit in 1 game (from fst to snd) *) (* **** *)
     (* the difference between the fsts is equal to one game with snd *)
     (* id until bad: the difference between the probability of the first game returning 1 (?) minus the probability of the second game returning 1 is <= the probability of the *second* (?) game returning bad (?) *)
     (* can we choose which game we want to use? (the 2nd one is easier here?) *)
     rewrite PRF_DRBG_G3_2_3_close. (* returning bad *)
     (* identical until bad? transitions from the normal game to the one exposing the bad event *) 
     rewrite PRF_DRBG_G3_bad_equiv.
     (* throw away game output *)

     (* TODO: examine *_G3_bad_* games! *)
     rewrite PRF_DRBG_G3_bad_1_2_equiv.
     rewrite PRF_DRBG_G3_bad_2_3_equiv.
     rewrite PRF_DRBG_G3_bad_3_4_equiv.
     apply PRF_DRBG_G3_bad_4_small. (* bad event bounding? *)
   Qed.

   (* Finally, show that G4 is equivalent to the second game in the DRBG security definition. *)
   Theorem PRF_DRBG_f_G2_compMap_spec :
     forall n v, 
     comp_spec (fun x1 x2 => fst x1 = x2)
     ((PRF_DRBG_f_G2 v n) unit unit_EqDec
        (fun (_ : unit) (_ : D) => x <-$ { 0 , 1 }^eta; ret (x, tt)) tt)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta) (forNats n)).

     induction n; intuition; simpl in *.
     fcf_simp.
     fcf_spec_ret.
     
     fcf_inline_first.
     fcf_skip.
     fcf_skip.
     fcf_spec_ret.
   Qed.
       
  Theorem PRF_DRBG_G4_DRBG_equiv : 
    Pr[PRF_DRBG_G4] == Pr[DRBG_G1 RndOut A].

    unfold PRF_DRBG_G4, DRBG_G1, RndOut, PRF_A.
    simpl.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_with PRF_DRBG_f_G2_compMap_spec fcf_skip.
   
    simpl.
    fcf_inline_first.
    fcf_ident_expand_r.
    fcf_skip.

  Qed.


  (* The final security result showing that the advantage of the adversary against the DRBG is at most the advantage of the constructed adversary against the PRF, and some negligible value. *)

  Theorem PRF_DRBG_Adv_small :
    (* difference between game START and game END *)
    DRBG_Advantage RndKey RndOut PRF_DRBG A <=
    (* advantage of constructed adversary against PRF *)
    PRF_Advantage RndKey ({ 0 , 1 }^eta) f D_EqDec (Bvector_EqDec eta) PRF_A
    + l ^ 2 / 2 ^ eta.          (* probability of collisions in list *)
  Proof.
    (* written and checked in Coq proof assistant *)
    intuition.
    unfold DRBG_Advantage.
    rewrite PRF_DRBG_G1_equiv.
    rewrite PRF_DRBG_G1_G2_equiv.
    rewrite <- PRF_DRBG_G4_DRBG_equiv.
    eapply ratDistance_le_trans.
    apply PRF_DRBG_G2_G3_close.
    apply PRF_DRBG_G3_G4_close.
  Qed.

  Print Assumptions PRF_DRBG_Adv_small.

End PRF_DRBG.
