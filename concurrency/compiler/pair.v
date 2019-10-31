Require Import Coq.Program.Basics. 
Import Basics.
Require Import Relation_Definitions.


(* For unfolding all definitions that hide pair constructors 
   (So the tactics can reach them)*)
Create HintDb pair.
(* For unfolding pair constructors (for internal use)*)
Create HintDb deep_pair. (*TODO: add the Hiint Unfold for all constructors*)

Notation "'Pair'  T " := (T * T)%type (at level 100).
Create HintDb pair.
Definition Liftable (f: Type -> Type):=
  forall a b, f (a -> b) -> (f a -> f b).

(* OLD version*)
(*Definition func_pair {T1 T2: Type} (f:T1 -> T2): (Pair T1) -> Pair T2:=
        fun aa:Pair T1 => (f (fst aa), f (snd aa)).
      Definition pair_appl {T1 T2: Type}  (f: Pair (T1 -> T2)) (a: Pair T1):=
        ((fst f) (fst a),(snd f) (snd a)).
      Definition func_pair2 {T1 T2 T3: Type} (f:T1 -> T2 -> T3):=
        fun aa bb=> pair_appl (func_pair f aa) bb. 
            Definition mk_pair {T:Type} (a:T): Pair T:= (a,a).  
 *)

Definition pair_appl: Liftable (fun x=> Pair x):=
  fun a b (f : Pair a -> b) aa => (fst f (fst aa), snd f (snd aa)).
Arguments pair_appl {_ _} f.
Definition pair0 {T} (x:T): Pair T:= (x,x).
Notation "g ̊" := (compose g) (at level 8, left associativity).
Definition pair1 {T1 T2}: (T1 -> T2) -> _:=
  pair_appl ̊ pair0.
Definition pair2 {T1 T2 T3}: (T1 -> T2 -> T3) -> _:=
  pair_appl ̊̊ pair1.
Definition pair3 {T1 T2 T3 T4}: (T1 -> T2 -> T3 -> T4) -> _:=
  pair_appl ̊̊̊ pair2.

(* 'Pair Prop' ~~ /\ *)
Definition pair_prop (a: Pair Prop): Prop:= fst a /\ snd a.
Definition pair0_prop:= pair_prop ̊ pair0.
Definition pair1_prop {T1}: (T1 -> Prop) -> _:=
  pair_prop ̊̊ pair1.
Definition pair2_prop {T1 T2}: (T1 -> T2 -> Prop) -> _:=
  pair_prop ̊̊̊ pair2.
Definition pair3_prop {T1 T2 T3}: (T1 -> T2 -> T3 -> Prop) -> _:=
  pair_prop ̊̊̊̊ pair3.

(* F preserves P*)
Definition impredicative
           {k}
           (F:(forall x : Type, k x -> k (Pair x)))
           (P:forall {T}, k T -> Prop)
  := forall {A} (R:k A),
    (*F A R := "Pair R" *)
    P R -> P (F A R).
(* Impredicatiive relation *)
(* Lifting Pairs preserves prediicates over relations *)
Definition impr_relation:=
  @impredicative relation (fun T => @pair2_prop T T).
Definition impr_func:=
  @impredicative (fun t=> t) (fun _ T => pair0 T).
Ltac destruct_and_simpl H:=
  let H1:= fresh in
  let H2:= fresh in  
  destruct H as [H1 H2]; simpl in H1, H2.
Ltac destruct_pair_and:=
  match goal with
  |[H: pair0_prop _ |- _] => destruct_and_simpl H
  |[H: pair1_prop _ _ |- _] => destruct_and_simpl H
  |[H: pair2_prop _ _ _ |- _] => destruct_and_simpl H
  |[H: pair3_prop _ _ _ _ |- _] => destruct_and_simpl H
  end.
Ltac solve_impr_rel:=
  (*INIT*)
  let A:= fresh in
  let R:= fresh in
  let HH:= fresh in
  intros A R HH;
  (* !goal ?P (pair2_prop R) *)
  split; simpl; intros; repeat destruct_pair_and;
  (* !goal ?P (fun x y => R (fst x) (fst y))   *)
  (* !goal ?P (fun x y => R (snd x) (snd y))   *)
  eapply HH; eauto.

Lemma impr_rel_refl: impr_relation reflexive.
Proof. solve_impr_rel. Qed.
Lemma impr_rel_symm:
  impr_relation symmetric.
Proof. solve_impr_rel. Qed.
Lemma impr_rel_trans:
  impr_relation transitive.
Proof. solve_impr_rel. Qed.





Ltac destruct_pair_and_hyp H:=
  match type of H with
  | pair3_prop _ _ _ _ => destruct_and_simpl H
  | pair2_prop _ _ _ => destruct_and_simpl H
  | pair1_prop _ _ => destruct_and_simpl H
  | pair0_prop _  => destruct_and_simpl H
  end.                                      
Ltac strong_destruct_pair:=
  match goal with
  |[H: pair0_prop _ |- _] => destruct_and_simpl H
  |[H: pair1_prop _ _ |- _] => destruct_and_simpl H
  |[H: pair2_prop _ _ _ |- _] => destruct_and_simpl H
  |[H: pair3_prop _ _ _ _ |- _] => destruct_and_simpl H
  |[H: ?X _ _ _ _ |- _] => unfold X in H; destruct_pair_and_hyp H
  |[H: ?X _ _ _ |- _] => unfold X in H; destruct_pair_and_hyp H
  |[H: ?X _ _ |- _] => unfold X in H; destruct_pair_and_hyp H
  |[H: ?X _ |- _] => unfold X in H; destruct_pair_and_hyp H
  end.



(* This is a decent ltac that transforms "pure" Pair lemmas, into their
   non Pair version. Example:

  transitivity R -> transitivity (pair2_prop R)

  Currently limmited of lemmas of the form:
  forall x1 .. yn, pair_constr1 x1 .. yn -> .. 
                   pair_constrm x1 .. yn.
  - All uniiversall quantifiications
  - All quantification at the beggining.
  - the rest is just implications of pairs of constructors.             
 *)


Ltac merge_quant' T:=
  match eval simpl in T with
  | fun vars: Pair ?T1 =>
      forall x: Pair ?T2, @?PP vars x =>
    let curr_T := constr:(fun vars:Pair (T1*T2) =>
                            let v:= (fst (fst vars), fst (snd vars)) in
                            let x:= (snd (fst vars), snd (snd vars)) in
                            PP v x) in
    merge_quant' curr_T
  | fun vars: Pair ?T1 => @?PP vars =>
    constr:((forall vars, PP vars))
  end.
Ltac process_cut HH v:=
  match goal with
  | |- forall x: Pair ?T, _ =>
    let x:= fresh in
    intros x;
    let new_v:= constr:(pair (fst v,fst x) (snd v,snd x)) in
    process_cut HH new_v
  | _ => specialize (HH v)
  end.



Ltac solve_pair_cut:=
  match goal with 
  | |- _ -> _ => let HH:= fresh in
              intros HH;
              process_cut HH (tt,tt);
              simpl in HH; auto 
  end.
Ltac merge_quant:=
  match goal with
    |- ?G => let new_G:=merge_quant' constr:(fun _: Pair unit => G) in
           cut new_G; 
           [solve_pair_cut|simpl]
  end.
Ltac unmerge_quant:=
  repeat (match goal with
          | |- forall _:unit, _ => simpl; intros _
          | |- forall xy: ?T1* ?T2, _ =>
            let x:=fresh in
            let y:=fresh "x" in
            intros [x y]; revert x y
          end).
Lemma blah:
  forall T (P1 P2: T -> Prop) PP1 PP2,
    (forall x, P1 x -> P2 x) ->
    (forall xx, PP1 xx -> pair1_prop P1 xx) ->
    (forall xx, pair1_prop P2 xx -> PP2 xx) ->
    (forall vars: Pair T, PP1 vars -> PP2 vars).
Proof.
  intros. eapply X.
  split; eapply H;
    eapply H0; assumption.
Qed.

Lemma pair_impl:
  forall X Y: Pair Prop,
    pair_prop 
      ((fst X -> fst Y), (snd X -> snd Y)) ->
    pair_prop X -> pair_prop Y.
Proof.
  intros [] [] [] [].
  constructor; auto.
Qed.
Lemma pair_and:
  forall X Y: Pair Prop,
    pair_prop 
      ((fst X /\ fst Y), (snd X /\ snd Y)) ->
    pair_prop X /\ pair_prop Y.
Proof.
  intros [] [] [[][]]; simpl in *.
  do 2 constructor; assumption.
Qed.
Lemma pair_iff:
  forall X Y: Pair Prop,
    pair_prop 
      ((fst X <-> fst Y), (snd X <-> snd Y)) ->
    pair_prop X  <-> pair_prop Y.
Proof.
  intros [] [] [[][]]; simpl in *.
  constructor; eapply pair_impl; constructor; auto.
Qed.
Lemma single_pair_impl
  : forall (x: Prop) (Y : Pair Prop),
    pair_prop (x -> fst Y, x -> snd Y) ->
    x -> pair_prop Y.
Proof.
  intros * [] **. econstructor; eauto.
Qed.
Ltac ez:= intros; constructor; simpl; eauto.
Lemma trivial_predicate:
  forall T (P: T-> Prop) x,
    P x -> P x.
Proof. trivial. Qed.
Lemma pair_prop_simpl:
  forall T (R:T->Prop),
    (forall x, R x)->
    forall x1 x2,
      pair_prop (R x1, R x2).
Proof. ez. Qed.

Lemma pair_immidiate:
  forall {T} (A: T -> Prop),
    (forall X, A X) -> 
    forall X1 X2, pair_prop (A X1, A X2).
Proof.
  intros ? ? H; split; simpl; eapply H.
Qed.
Ltac pair_prop_simpl X1 X2:= 
  try (revert X1 X2;
       eapply pair_prop_simpl).
Ltac pair_prop_implications':=
  match goal with
  | |- pair_prop _ -> pair_prop _ =>
    eapply pair_impl
  | |- pair_prop _ <-> pair_prop _ =>
    eapply pair_iff
  | |- pair_prop _ /\ pair_prop _ =>
    eapply pair_and
  | |- pair_prop _ -> ?G =>
    let HH:= fresh in
    intros HH;
    pair_prop_implications';
    revert HH;
    pair_prop_implications'
  | |- ?G -> pair_prop _ =>
    eapply single_pair_impl
  | |- ?G1 -> ?G2 =>
    (* This case we think G1 is not a pair predicate*)
    let HH:= fresh in
    intros HH;
    pair_prop_implications';
    revert HH;
    pair_prop_implications'
  end.
Ltac pair_prop_implications X1 X2:=
  try pair_prop_implications'; simpl; pair_prop_simpl X1 X2.
Hint Unfold pair3_prop : pair.
Hint Unfold pair2_prop : pair.
Hint Unfold pair1_prop : pair.
Hint Unfold pair3 : pair.
Hint Unfold pair2 : pair.
Hint Unfold pair1 : pair.
Hint Unfold pair0 : pair.
Hint Unfold pair_appl : pair.
Hint Unfold compose : pair.
Ltac solve_pair:=
  (* Unfold definitions hiding the "pair" 
     These must be defined as
     Hint Unfold _ : pair.
   *)
  repeat autounfold with pair;
  (* Unfold all superfluous definitions,
     leaving pair_prop
   *)
  unfold pair3_prop, pair2_prop, pair1_prop,
  pair3, pair2, pair1, pair_appl, compose; simpl;

  (*turn all the universal quant into ONE*)
  merge_quant;
  intros [X1 X2]; simpl;
  (* you should be left with a train of implications
                                 with pair_prop:
                                 pair_prop A -> pair_prop B -> pair_prop C...
   *)
  pair_prop_implications X1 X2; simpl;
  (*return quantificatiion as it should*)
  unmerge_quant.
