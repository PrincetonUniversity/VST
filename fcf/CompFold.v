(* Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Operations that fold and map a computation over a list, and related theory. *)

Set Implicit Arguments.
Require Import fcf.FCF.

Local Open Scope list_scope.

(* Definitions for fold, map etc.   These should probably go somewhere else. *)

(* Fold a computation over a list *)
Fixpoint compFold(A B : Set)(eqd : EqDec B)(f : B -> A -> Comp B)(init : B)(ls : list A) :=
  match ls with
      | nil => ret init 
      | a :: ls' =>
        init' <-$ f init a;
          compFold  _ f init' ls'
  end.

(* foldBody_option is an adapter that allows you to fold a computation with signature B -> A -> Comp (option B) over a list of A, accumulating an option B. *)
Definition foldBody_option(A B : Set)(eqd : EqDec B)(f : B -> A -> Comp (option B))(b_opt : option B)(a : A) :=
  match b_opt with
      | None => ret None
      | Some b =>
        f b a
  end.

Definition opt_pred(A B : Set)(P : A -> B -> Prop)(opt_a : option A)(opt_b : option B) :=
  match opt_a with
    | Some a =>
      match opt_b with
        | Some b => P a b
        | None => False
      end
    | None =>
      match opt_b with
        | Some _ => False
        | None => True
      end
  end.

Theorem foldBody_option_spec : 
  forall (A B C D: Set)(eqda : EqDec A)(eqdb : EqDec B) (c1 : A -> C -> Comp (option A)) (c2 : B -> D -> Comp (option B)) (post : A -> B -> Prop) (pre1 : A -> B -> Prop) (pre2 : C -> D -> Prop), 
    (forall a b c d, 
         pre1 a b -> pre2 c d -> comp_spec (opt_pred post) (c1 a c) (c2 b d)) ->
    forall opt_a opt_b c d,
      opt_pred pre1 opt_a opt_b ->
      pre2 c d ->
      comp_spec
        (opt_pred post)
        (foldBody_option _ c1 opt_a c)
        (foldBody_option _ c2 opt_b d).

  intuition.
  unfold foldBody_option.
  unfold opt_pred in *.
  
  destruct opt_a; destruct opt_b; intuition.

  eapply comp_spec_ret; intuition.
Qed.


Theorem compFold_option_spec : 
  forall (A B : Set)(lsa : list A)(lsb : list B)(pre : A -> B -> Prop),
    list_pred pre lsa lsb ->
    forall (C D : Set){eqdc : EqDec C}{eqdd : EqDec D}(c1 : C -> A -> Comp (option C))(c2 : D -> B -> Comp (option D))(post : C -> D -> Prop) c d,
      (forall c d a b, post c d -> pre a b -> comp_spec (opt_pred post) (c1 c a) (c2 d b)) ->
      opt_pred post c d ->
      comp_spec 
        (opt_pred post) 
        (compFold _ (foldBody_option _ c1) c lsa) 
        (compFold _ (foldBody_option _ c2) d lsb).

  induction 1; intuition; simpl.
  eapply comp_spec_ret; intuition.

  eapply comp_spec_seq; eauto.
  eapply foldBody_option_spec; eauto.
Qed.

(* Map a computation over a list. *)
Fixpoint compMap (A B : Set)(eqdb : EqDec B)(c : A -> Comp B)(ls : list A) : Comp (list B) :=
  match ls with
      | nil => ret nil
      | a :: lsa' =>
        b <-$ c a;
          lsb' <-$ compMap _ c lsa';
          ret (b :: lsb')
  end.


Theorem compMap_cons: 
  forall (A B : Set)(eqdb : EqDec B) (ls : list A)(c : A -> Comp B) (a : A) x,
    evalDist (compMap _ c (a :: ls)) x ==
    evalDist (b <-$ c a; lsb <-$ compMap _ c ls; ret (b :: lsb)) x.
  
  intuition.
  simpl.
  intuition.
  
Qed.

Theorem compMap_nil : 
  forall (A B : Set)(eqdb : EqDec B)(c : A -> Comp B),
    compMap _ c nil = ret nil.

  intuition.

Qed.

Theorem list_inhabited : 
  forall (A : Set), list A.

  intuition.
  apply nil.

Qed.

Theorem compMap_fission_eq:
  forall (A B C D : Set){eqdb : EqDec B}{eqdd : EqDec D}{eqdc : EqDec C}(ls : list A)(f1 : A -> Comp B)(f2 : A -> Comp C)(f3 : list B -> Comp (list D))(f4 : C -> Comp D) P,
    (comp_spec eq (f3 nil) (ret nil)) -> 
    (forall a, comp_spec P (f1 a) (f2 a)) -> 
    (forall r1 r2 r3, P r1 r2 ->
      comp_spec eq (f3 (r1 :: r3)) (r0 <-$ f3 r3; a0 <-$ f4 r2; ret a0 :: r0)) ->
    comp_spec eq 
    (lsb <-$ compMap _ f1 ls; f3 lsb)
    (compMap _ (fun a => b <-$ f2 a; f4 b) ls).
  
  induction ls; intuition.
  unfold compMap.

  prog_simp.
  intuition.

  simpl.
  prog_inline_first.
  
  Hint Resolve list_inhabited : inhabited.

  eapply comp_spec_seq; intuition;
  eauto with inhabited. 

  eapply comp_spec_eq_trans.
  2:{
    eapply comp_spec_seq_eq; eauto with inhabited. 
    eapply comp_spec_eq_refl.
    intuition.
    eapply comp_spec_seq_eq; eauto with inhabited. 
    intuition.
    eapply comp_spec_eq_refl.
  }
   
  prog_swap_r.
  prog_inline_first.
  prog_skip.

Qed.  
  

Theorem compMap_map_fission_eq :
  forall (A B C D : Set){eqdb : EqDec B}{eqdd : EqDec D}{eqdc : EqDec C}(ls : list A)(f1 : A -> Comp B)(f2 : A -> Comp C)(f3 : B -> D)(f4 : C -> D),
    (forall a, comp_spec (fun b c => f3 b = f4 c)
              (f1 a) (f2 a)) -> 
    comp_spec eq (lsb <-$ compMap _ f1 ls; ret (map f3 lsb))
     (compMap _ (fun a => b <-$ f2 a; ret (f4 b)) ls).

  intuition.
  eapply compMap_fission_eq; intuition.
  simpl.
  eapply comp_spec_eq_refl.

  simpl.
  prog_simp.
  eapply comp_spec_ret.
  congruence.
 
Qed.


Theorem fold_map_fission_spec_eq : 
  forall (A B C: Set)(eqdB : EqDec B)(eqdC : EqDec C) ls c init (ca : A -> Comp B) cb,
    (forall a init, comp_spec eq (c init a) (x <-$ ca a; cb init x)) ->
    comp_spec eq (compFold _ c init ls) 
    (lsa <-$ (compMap _ ca ls); compFold _ cb init lsa).

  induction ls; intuition.
  unfold compMap.
  prog_simp.
  eapply comp_spec_eq_refl.

  simpl.
  prog_inline_first.
  prog_at prog_inline rightc 1%nat.
  simpl.

  prog_at prog_ret rightc 2.
  simpl.
  prog_at prog_swap rightc 1%nat.
  eapply comp_spec_eq_trans.
  eapply comp_spec_seq_eq; intuition.
  eapply comp_spec_eq_refl.
  
  prog_inline_first.
  do 2 prog_skip.
  
Qed.

Theorem fold_map_fission_spec : 
  forall (A E : Set)(P : A -> E -> Prop)(B D : Set)(eqdA : EqDec A)(c1 : A -> B -> Comp A)(ls_b : list B)(init_a : A)
    (eqdD : EqDec D)(eqdE : EqDec E)(c2 : B -> Comp D)(c3 : E -> D -> Comp E)(init_e : E),
    P init_a init_e ->
    (forall a b e, P a e -> comp_spec P (c1 a b) (a0 <-$ c2 b; c3 e a0)) ->
    comp_spec P 
    (compFold _ c1 init_a ls_b)
    (ls_d <-$ (compMap _ c2 ls_b); compFold _ c3 init_e ls_d).

  induction ls_b; intuition.

  simpl.
  prog_simp.
  simpl.
  eapply comp_spec_ret.
  trivial.

  simpl.
  prog_inline_first.
  prog_at prog_inline rightc 1%nat.
  simpl.
  prog_at prog_ret rightc 2.
  simpl.
  prog_at prog_swap rightc 1%nat.
  
  Ltac prog_assoc_r :=
    eapply comp_spec_eq_trans_r; [ idtac | eapply comp_spec_assoc].

  prog_assoc_r.
  eapply comp_spec_seq; intuition.
Qed.

(* A bounded repeat based on fold. *)
Definition repeatMax(A : Set)(eqd : EqDec A)(c : Comp A)(P : A -> bool) def (n : nat):=
  compFold _ (fun a' i => if (P a') then (ret a') else c) def (allNatsLt n).
  
Lemma repeatMax_fold_true :
  forall (A B: Set)(ls : list B)(eqd : EqDec A)(c : B -> Comp A)(P : A -> bool)(a : A),
    P a = true ->
    comp_spec eq 
    (compFold _ (fun acc b => if (P acc) then (ret acc) else (c b)) a ls)  
    (ret a).

  induction ls; intuition; simpl.

  eapply comp_spec_eq_refl.

  rewrite H.
  prog_simp.
  intuition.
Qed.

Lemma repeatMax_fold_in_support_false : 
  forall (A B : Set)(ls : list B)(eqd : EqDec A)(c : B -> Comp A)(P : A -> bool)(a : A),
    (forall b, In b ls -> In a (getSupport (c b))) ->
    P a = false ->
    In a
       (getSupport
          (compFold eqd
                    (fun (a' : A) b => if P a' then ret a' else (c b)) a ls)).

  induction ls; intuition.
  simpl.
  intuition.

  unfold compFold.
  fold compFold.
  eapply getSupport_In_Seq.
  
  rewrite H0.
  eapply H.
  simpl.
  intuition.

  eapply IHls; intuition.
Qed.


Theorem compFold_repeat_spec : 
  forall (C D: Set)(ls1 : list C)(ls2 : list D)(pre : C -> D -> Prop),
    list_pred pre ls1 ls2 ->
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(post : A -> B -> Prop)(c1 : C -> Comp A)(P1 : A -> bool)(c2 : D -> Comp B)(P2 : B -> bool) a b,
    post a b -> 
    (forall a b, pre a b -> comp_spec post (c1 a) (c2 b)) ->
    (forall a b, post a b -> (P1 a = true <-> P2 b = true)) ->
    comp_spec 
      post 
      (compFold _ (fun acc v => if (P1 acc) then (ret acc) else (c1 v)) a ls1) 
      (compFold _ (fun acc v => if (P2 acc) then (ret acc) else (c2 v)) b ls2).
  
  induction 1; intuition.
  simpl.
  eapply comp_spec_ret.
  trivial.

  simpl.
  case_eq (P1 a); intuition.
  assert (P2 b = true).
  eapply H3; eauto.
  rewrite H5.
  prog_simp.
  eauto.

  case_eq (P2 b); intuition.
  assert (P1 a = true).
  eapply H3; intuition; eauto.
  congruence.
  
  eapply comp_spec_seq; intuition.
Qed.


Theorem compFold_eq : 
  forall (A1 A2 : Set) P (ls1 : list A1) (ls2 : list A2),
    list_pred P ls1 ls2 ->
    forall (B : Set)(eqd : EqDec B) (c1 : B -> A1 -> Comp B) (c2: B -> A2 -> Comp B),
      (forall acc a1 a2, P a1 a2 -> In a1 ls1 -> In a2 ls2 ->
        comp_spec eq (c1 acc a1) (c2 acc a2) ) ->
      forall init, 
        comp_spec eq (compFold _ c1 init ls1) (compFold _ c2 init ls2).
  
  induction 1; intuition; simpl.

  eapply comp_spec_eq_refl.

  eapply comp_spec_seq; intuition.
  subst.
  intuition.
  
Qed.

Lemma list_pred_zip_l : 
  forall (A B: Set)(lsa : list A)(lsb : list B)(P : A -> B -> Prop),
    list_pred P lsa lsb ->
    forall (C : Set)(lsc : list C)(P1 : A -> C -> Prop)(P2 : B -> C -> Prop),
      list_pred P1 lsa lsc ->
      list_pred P2 lsb lsc ->
      list_pred (fun (p : A * B) c => P (fst p) (snd p) /\ P1 (fst p) c /\ P2 (snd p) c) (zip lsa lsb) lsc.
  
  induction 1; intuition.
  inversion H.
  subst.
  econstructor.
  
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  simpl.
  econstructor; intuition.
Qed.

Lemma list_pred_eq : 
  forall (A : Set)(lsa : list A),
    list_pred eq lsa lsa.
  
  induction lsa; intuition; simpl in *; econstructor; intuition.
  
Qed.

Lemma list_pred_I : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    (length lsa = length lsb) ->
    list_pred (fun a b => True) lsa lsb.
  
  induction lsa; destruct lsb; intuition; simpl in *; try omega.
  econstructor.
  econstructor;
    intuition.
  
Qed.

Lemma list_pred_length_eq : 
  forall (A B : Set)(lsa : list A)(lsb : list B)(P : A -> B -> Prop),
       list_pred P lsa lsb ->
       length lsa = length lsb.
  
  induction 1; intuition; simpl in *.
  f_equal.
  intuition.
  
Qed.

Lemma list_pred_zip_l_eq : 
  forall (A B: Set)(lsa : list A)(lsb : list B)(P : A -> B -> Prop),
    list_pred P lsa lsb ->
    list_pred (fun p a => (fst p) = a /\ P (fst p) (snd p)) (zip lsa lsb) lsa.
  
  intuition.
  eapply list_pred_impl.
  eapply list_pred_zip_l.
  eauto.
  eapply list_pred_eq.
  eapply list_pred_I.
  symmetry.
  eapply list_pred_length_eq; eauto.
  
  intuition.
Qed.

Lemma list_pred_map_r_eq : 
  forall (A B : Set)(ls : list A)(f : A -> B),
    list_pred (fun a b => f a = b) ls (map f ls).
  
  
  induction ls; intuition; simpl in *.
  econstructor.
  econstructor; intuition.
Qed.

Lemma list_pred_map_r : 
  forall (A B : Set)(lsa : list A)(lsb : list B)(P : A -> B -> Prop),
    list_pred P lsa lsb ->
    forall (C : Set)(f : B -> C),
           list_pred (fun a c => exists b, P a b /\ c = f b) lsa (map f lsb).
  
  induction 1; intuition; simpl in *.
  econstructor.
  econstructor; intuition.
  econstructor; intuition.
  trivial.
  
Qed.

Lemma list_pred_zip_r : 
  forall (A B: Set)(lsa : list A)(lsb : list B)(P : A -> B -> Prop),
    list_pred P lsa lsb ->
    forall (C : Set)(lsc : list C)(P1 : A -> C -> Prop)(P2 : B -> C -> Prop),
      list_pred P1 lsa lsc ->
      list_pred P2 lsb lsc ->
      list_pred (fun c (p : A * B) => P (fst p) (snd p) /\ P1 (fst p) c /\ P2 (snd p) c) lsc (zip lsa lsb).
       
  induction 1; intuition.
  inversion H.
  subst.
  econstructor.
  
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  simpl.
  econstructor; intuition.
Qed.

Lemma list_pred_map_l_eq : 
  forall (A B : Set)(ls : list A)(f : A -> B),
    list_pred (fun b a => f a = b) (map f ls) ls.
  
  
  induction ls; intuition; simpl in *.
  econstructor.
  econstructor; intuition.
Qed.

(* map constructed out of fold -- more complicated but allows us to apply any fold theory to map operations.*)
Definition compMap_fold (A B : Set)(eqd : EqDec B)(c : A -> Comp B)(ls : list A) :=
  compFold _ (fun (acc : list B)(a : A) => b <-$ c a; ret (acc ++ (b :: nil))) nil ls.

Lemma compFold_spec : 
  forall (A C D : Set)(P2 : list A -> C -> D -> Prop)(eqdc : EqDec C)(eqdd : EqDec D)(lsa : list A)(c1 : C -> A -> Comp C)(c2 : D -> A -> Comp D) init1 init2,
    P2 lsa init1 init2 ->
    (forall a lsa c d, P2 (a :: lsa) c d -> comp_spec (P2 lsa) (c1 c a) (c2 d a)) ->
    comp_spec (P2 nil) (compFold _ c1 init1 lsa) (compFold _ c2 init2 lsa).
  
  induction lsa; intuition; simpl.
  eapply comp_spec_ret; intuition.

  eapply comp_spec_seq; intuition.
  eapply H0; eauto.

  intuition.
Qed.


Theorem compMap_fold_equiv : 
  forall (A B : Set)(eqd : EqDec B)(c : A -> Comp B)(ls : list A),
    comp_spec eq (compMap eqd c ls) (compMap_fold eqd c ls).
  
  induction ls; intuition; simpl.
  unfold compMap_fold.
  simpl.
  eapply comp_spec_eq_refl.

  unfold compMap_fold.
  simpl.
  prog_inline_first.
  prog_skip.
  prog_simp.
  
  eapply comp_spec_eq_trans.
  eapply comp_spec_seq_eq; eauto with inhabited.
  intuition.
  eapply comp_spec_eq_refl.
  unfold compMap_fold.
  
  eapply comp_spec_eq_trans_r.
  2:{
    eapply comp_spec_right_ident.
  }
  eapply comp_spec_seq; eauto with inhabited.
  eapply (@compFold_spec _ _ _ (fun ls p1 p2 => b :: p1 = p2)); intuition.
  subst.
  simpl.
  comp_skip.
  eapply comp_spec_ret.
  trivial.
  intuition.
  subst.
  eapply comp_spec_eq_refl.
Qed.

Lemma compFold_wf : 
  forall (A B : Set)(eqd : EqDec A)(c : A -> B -> Comp A)(ls : list B) init,
    (forall a b, well_formed_comp (c a b)) ->
    well_formed_comp (compFold _ c init ls).
  
  induction ls; intuition.
  
  unfold compFold.
  wftac.
  
  unfold compFold.
  fold compFold.
  wftac.
  
Qed.

Lemma compMap_map : 
  forall (A B : Set)(eqd : EqDec B)(f : A -> B) ls,
    comp_spec eq (compMap _ (fun a => ret (f a)) ls) (ret (map f ls)).
  
  induction ls; intuition.
  simpl.
  eapply comp_spec_eq_refl.

  simpl.
  prog_simp.
  
  eapply comp_spec_eq_trans.
  eapply comp_spec_seq_eq; intuition.
  eapply IHls.
  eapply comp_spec_eq_refl.
  prog_simp.
  eapply comp_spec_eq_refl.
Qed.

Lemma compFold_nop : 
  forall (A B : Set)(eqd : EqDec A)(c : A -> B -> Comp A)(ls : list B) init x, 
    In x (getSupport (compFold _ c init ls)) ->
    (forall b a, In b ls -> In a (getSupport (c init b)) -> a = init) ->
    x = init.
  
  induction ls; intuition.
  
  simpl in *.
  intuition.
  
  unfold compFold in H.
  fold compFold in H.
  simp_in_support.
  assert (x0 = init).
  eapply H0; eauto.
  simpl.
  intuition.
  subst.
  
  eapply IHls.
  trivial.
  intuition.
  eapply H0; eauto.
  simpl.
  intuition.
  
Qed.

Lemma compFold_app : 
  forall (A B : Set)(eqd : EqDec A)(c : A -> B -> Comp A)(ls1 ls2 : list B) init x,
    evalDist (compFold _ c init (ls1 ++ ls2)) x ==
    evalDist (init' <-$ compFold _ c init ls1; compFold _ c init' ls2) x.
  
  induction ls1; intuition.
  rewrite app_nil_l.
  unfold compFold.
  fold compFold.
  comp_simp.
  intuition.
  
  rewrite <- app_comm_cons.
  unfold compFold.
  fold compFold.
  inline_first.
  comp_skip.
  
Qed.

Theorem comp_fold_ext : 
  forall (A B : Set)(eqd : EqDec A)(c1 c2 : A -> B -> Comp A)(ls : list B)(init : A),
    (forall a b,
       comp_spec eq (c1 a b) (c2 a b)) ->
    comp_spec eq (compFold _ c1 init ls) (compFold _ c2 init ls).
  
  intuition.
  eapply compFold_eq.
  eapply list_pred_eq.
  intuition.
  subst.
  eauto.
  
Qed.


Lemma list_pred_app : 
  forall (A B : Set)(P : A -> B -> Prop)(lsa1 lsa2 : list A)(lsb : list B),
    list_pred P (lsa1 ++ lsa2) lsb ->
    list_pred P lsa1 (firstn (length lsa1) lsb) *
    list_pred P lsa2 (skipn (length lsa1) lsb).
  
  induction lsa1; intuition; simpl in *.
  econstructor.

  inversion H; clear H; subst.
  econstructor; intuition.
  eapply IHlsa1; eauto.

  inversion H; clear H; subst.
  eapply IHlsa1; eauto.  
Qed.

Theorem list_pred_map_l_inv :
  forall (A B C : Set) (lsa : list A) (lsb : list B) (f : A -> C)(P : C -> B -> Prop),
    list_pred P (map f lsa) lsb ->
    list_pred (fun a b => P (f a) b) lsa lsb.
  
  induction lsa; intuition; simpl in *.
  inversion H; clear H; subst.
  econstructor.
  
  inversion H; clear H; subst.
  
  econstructor.
  trivial.
  eauto.
Qed.

Definition flatten_prep
           (A B : Set)(ls : list (A * (list B))) : list (list (nat * nat * A * B)) :=
  map (fun p => [a, lsb] <-2 p; map (fun p' => [i, b] <-2 p'; (i, length lsb, a, b)) (zip (allNatsLt (length lsb)) lsb)) ls.


Theorem compFold_flatten : 
  forall (A B C D: Set) P (eqd1 eqd2 : EqDec C)(c1 : C -> (D * list A) -> Comp C)(c2 : C -> B -> Comp C)(ls1 : list (D * (list A)))(ls2 : list B) init x,
    list_pred P (flatten (flatten_prep ls1)) ls2 ->
    (forall d lsa lsb init x, list_pred P (map (fun p => [i, a] <-2 p; (i, (length lsa), d, a)) (zip (allNatsLt (length lsa)) lsa)) lsb -> evalDist (c1 init (d, lsa)) x == evalDist (compFold eqd2 c2 init lsb) x) ->
    evalDist (compFold eqd1 c1 init ls1) x ==
    evalDist (compFold eqd2 c2 init ls2) x.
  
  induction ls1; intuition.
  simpl in H.
  inversion H; clear H; subst.
  unfold compFold.
  eapply evalDist_ret_eq.
  trivial.
  
  simpl in H.
  unfold compFold.
  fold compFold.

  eapply list_pred_app in H.
  intuition.

  erewrite <- (@firstn_skipn _ _ ls2).
 
  rewrite compFold_app.
  comp_skip.
Qed.

Lemma compMap_eq : 
  forall (A B : Set)(P : A -> B -> Prop)(C : Set)(eqd : EqDec C)(c1 : A -> Comp C)(c2 : B -> Comp C)(lsa : list A)(lsb : list B),
    list_pred P lsa lsb ->
    (forall a b, P a b -> forall x, evalDist (c1 a) x == evalDist (c2 b) x) ->
    forall x, 
      evalDist (compMap _ c1 lsa) x == evalDist (compMap _ c2 lsb) x.
  
  induction 1; intuition.
  unfold compMap.
  intuition.
  
  unfold compMap. fold compMap.
  comp_skip.
  comp_skip.
  
Qed.

Require Import Permutation.

Theorem compFold_perm : 
  forall (A B : Set)(inv : B -> Prop)(ls1 ls2 : list A),
    Permutation ls1 ls2 ->
    forall (eqd : EqDec B) (c : B -> A -> Comp B) init x,
      (forall b a1 a2 x,
           In a1 ls1 ->
           In a2 ls2 ->
           inv b -> 
           evalDist (b' <-$ c b a1; c b' a2) x ==
           evalDist (b' <-$ c b a2; c b' a1) x) ->
      (forall a b b',
         In a ls1 ->
         inv b ->
         In b' (getSupport (c b a)) ->
         inv b') ->
      inv init -> 
      evalDist (compFold _ c init ls1) x ==
      evalDist (compFold _ c init ls2) x.
  
  induction 1; 
  intuition.
  
  unfold compFold.
  fold compFold.
  comp_skip.
  eapply IHPermutation; intuition.
  eapply H1.
  simpl.
  right.
  eapply H4.
  eapply H5.
  trivial.
  eapply H1.
  simpl.
  left.
  eauto.
  eauto.
  trivial.
  
  unfold compFold.
  fold compFold.
  eapply (trans _  (evalDist (init'0 <-$ (init' <-$ c init y; c init' x); compFold eqd c init'0 l) x0)).
  inline_first.
  intuition.
  eapply trans.
  comp_skip.
  eapply eqRat_refl.
  inline_first.
  intuition.
  
  eapply trans.
  eapply IHPermutation1; intuition.
  eapply H1; intuition.
  eapply Permutation_in; eauto.
  eapply IHPermutation2; intuition.
  eapply H1; intuition.
  eapply Permutation_in.
  eapply Permutation_sym.
  eauto.
  trivial.
  
  eapply H2; eauto.
  eapply Permutation_in.
  eapply Permutation_sym.
  eauto.
  trivial.
Qed.

Lemma list_pred_app_both : 
  forall (A B : Set)(P : A -> B -> Prop)(lsa1 lsa2 : list A)(lsb1 lsb2 : list B),
    list_pred P lsa1 lsb1 ->
    list_pred P lsa2 lsb2 ->
    list_pred P (lsa1 ++ lsa2) (lsb1 ++ lsb2).
  
  induction lsa1; destruct lsb1; intuition.
  inversion H.
  inversion H.
  
  inversion H; clear H; subst.
  repeat rewrite <- app_comm_cons.
  econstructor.
  trivial.
  eauto.
Qed.

Lemma list_pred_map_both : 
  forall (A B C D : Set)(P : A -> B -> Prop)(lsa : list A)(lsb : list B)(f1 : A -> C)(f2 : B -> D),
    list_pred P lsa lsb ->
    list_pred (fun c d => exists a b, P a b /\ c = (f1 a) /\ d = (f2 b)) (map f1 lsa) (map f2 lsb).
  
  induction lsa; destruct lsb; intuition; simpl in *.
  econstructor.
  
  inversion H.
  inversion H.
  
  inversion H; clear H; subst.
  econstructor; intuition.
  eauto.
  
Qed.

Lemma compMap_spec : 
  forall (A B C D : Set)(eqdc : EqDec C)(eqdd : EqDec D)(P1 : A -> B -> Prop)(P2 : C -> D -> Prop)(lsa : list A)(lsb : list B)(c1 : A -> Comp C)(c2 : B -> Comp D),
    list_pred P1 lsa lsb ->
    (forall a b, In a lsa -> In b lsb -> P1 a b -> comp_spec P2 (c1 a) (c2 b)) ->
    comp_spec (list_pred P2)
                   (compMap _ c1 lsa) 
                   (compMap _ c2 lsb).
  
  induction 1; intuition.
  
  unfold compMap.

  eapply comp_spec_ret.
  econstructor.

  simpl.
  eapply comp_spec_seq.
  apply nil.
  apply nil.
  eapply H1;
  simpl; intuition.

  intuition.
  eapply comp_spec_seq.
  eapply nil.
  eapply nil.
  eapply IHlist_pred.
  intuition.
  intuition.
  eapply comp_spec_ret.
  econstructor; eauto.
  
Qed.

Theorem compMap_fission_ex : 
  forall (A B C : Set)(eqdb : EqDec B)(eqdc : EqDec C)
         (c1 : A -> Comp B)(c2 : B -> Comp C)(ls : list A),
    comp_spec eq 
              (compMap _ (fun a => b <-$ c1 a; c2 b) ls)
              (ls' <-$ compMap _ c1 ls; compMap _ c2 ls').

  induction ls; intuition; simpl in *.
  comp_simp; simpl; reflexivity.

  inline_first; comp_skip; inline_first.
  comp_swap_l.
  
  (* comp_skip *)
  (* *)
  eapply comp_spec_eq_trans.
  eapply (@comp_spec_seq (list C) (list C));
  eauto with inhabited.
   (* *)
  intuition; subst.
  eapply comp_spec_eq_refl.
  inline_first; comp_skip; comp_simp; simpl.
  comp_swap_r; comp_skip.

Qed.


Lemma list_pred_eq_gen : 
  forall (A : Set)(ls1 ls2 : list A),
    ls1 = ls2 ->
    list_pred eq ls1 ls2.
  
  intuition.
  subst.
  eapply list_pred_eq.
  
Qed.

Lemma compMap_support : 
  forall (A B : Set)(P : A -> B -> Prop)(eqd : EqDec B)(c : A -> Comp B)(lsa : list A)(lsb : list B),
    In lsb (getSupport (compMap _ c lsa)) ->
    (forall a b, In a lsa -> In b (getSupport (c a)) -> P a b) ->
    list_pred P lsa lsb.
  
  induction lsa; intuition.
  
  simpl in *.
  intuition; subst.
  econstructor.
  
  unfold compMap in *.
  fold compMap in *.
  repeat simp_in_support.
  econstructor.
  eapply H0.
  simpl.
  intuition.
  trivial.
  
  eapply IHlsa.
  trivial.
  intuition.
  
Qed.

Lemma In_zip : 
  forall (A B : Set)(a : A)( b : B) lsa lsb, 
    In (a, b) (zip lsa lsb) ->
    In a lsa /\ In b lsb.
  
  induction lsa; intuition; simpl in *.
  intuition.
  
  destruct lsb.
  inversion H.
  simpl in H.
  intuition.
  pairInv.
  intuition.
  right.
  eapply IHlsa.
  eauto.
  
  destruct lsb.
  inversion H.
  simpl in *.
  intuition.
  pairInv.
  intuition.
  right.
  eapply IHlsa.
  eauto.
       
Qed.

Lemma list_pred_map_l
: forall (A B : Set) (lsa : list A) (lsb : list B) (P : A -> B -> Prop),
    list_pred P lsa lsb ->
    forall (C : Set) (f : A -> C),
      list_pred 
        (fun (c : C) (b : B) => exists a : A, P a b /\ c = f a) (map f lsa)
        lsb.
  
  induction 1; intuition; simpl in *.
  
  econstructor.
  
  econstructor.
  econstructor; eauto.
  eauto.
  
Qed.

Lemma list_pred_map_l_if : 
  forall (A B C : Set) (P  : C -> B -> Prop)(lsa : list A)(lsb : list B)(f : A -> C),
    list_pred P (map f lsa) lsb ->
    list_pred (fun a b => P (f a) b) lsa lsb.
  
  induction lsa; inversion 1; intuition; subst; simpl in *;
  econstructor.
  
  inversion H; clear H; subst.
  trivial.
  
  inversion H; clear H; subst.
  eauto.
  
Qed.

Lemma list_pred_map_r_if : 
  forall (A B C : Set) (P  : A -> C -> Prop)(lsb : list B)(lsa : list A)(f : B -> C),
    list_pred P lsa (map f lsb) ->
    list_pred (fun a b => P a (f b)) lsa lsb.
  
  induction lsb; inversion 1; intuition; subst; simpl in *;
  econstructor.
  
  inversion H; clear H; subst.
  trivial.
  
  inversion H; clear H; subst.
  eauto.
  
Qed.

Lemma list_pred_map_r'
: forall (A B C : Set) (lsa : list A) (lsb : list B) (P : A -> C -> Prop) (f : B -> C),
    list_pred (fun a b => P a (f b)) lsa lsb ->
    list_pred P lsa (map f lsb).
  
  induction lsa; inversion 1; intuition; subst; simpl in *;
  
  econstructor.
  
  inversion H; clear H; subst.
  trivial.
  eauto.
  
Qed.

Lemma list_pred_map_l'
: forall (A B C : Set) (lsa : list A) (lsb : list B) (P : C -> B -> Prop) (f : A -> C),
    list_pred (fun a b => P (f a) b) lsa lsb ->
    list_pred P (map f lsa) lsb.
  
  induction lsa; inversion 1; intuition; subst; simpl in *;
  
  econstructor.
  
  inversion H; clear H; subst.
  trivial.
  eauto.
  
Qed.


Theorem list_pred_rev : 
  forall (A B : Set)(lsa : list A)(lsb : list B) P,
    list_pred P lsa lsb ->
    forall a b,
    P a b ->
    list_pred P (lsa ++ (a :: nil)) (lsb ++ (b :: nil)).

  induction 1; intuition.
  repeat rewrite app_nil_l.
  econstructor.
  intuition.
  econstructor.

  repeat rewrite <- app_comm_cons.
  econstructor; intuition.

Qed.

Theorem list_pred_impl'
     : forall (A B : Set) (lsa : list A) (lsb : list B) (P1 : A -> B -> Prop),
       list_pred P1 lsa lsb ->
       forall P2 : A -> B -> Prop,
       (forall (a : A) (b : B), In a lsa -> In b lsb -> P1 a b -> P2 a b) -> list_pred P2 lsa lsb.

  induction 1; intuition.
  econstructor.
  econstructor; intuition.

Qed.

Lemma list_pred_allNatsLt : 
  forall (A : Set)(ls : list A),
    list_pred (fun i a => forall a', nth i ls a' = a) (allNatsLt (length ls)) ls.
  
  induction ls using rev_ind; intuition; simpl in *.
  
  econstructor.

  rewrite app_length.
  rewrite plus_comm.
  simpl.
  
  eapply list_pred_rev.
  eapply list_pred_impl'.
  eapply IHls.
  intuition.
  rewrite app_nth1.
  eauto.
  apply allNatsLt_lt.
  trivial.

  intuition.
  rewrite app_nth2.
  rewrite minus_diag.
  simpl.
  trivial.
  intuition.
Qed.

Lemma compMap_length :
  forall (A B : Set)(eqd : EqDec B)(ls : list A) x (c : A -> Comp B) ,
    In x (getSupport (compMap _ c ls)) ->
    length x = length ls.
  
  induction ls ; intuition.
  simpl in *.
  intuition; subst.
  simpl.
  trivial.
  
  unfold compMap in *.
  fold compMap in *.
  repeat simp_in_support.
  simpl.
  f_equal.
  eauto.
Qed.

Lemma map_eq : 
  forall (A B C : Set)(lsa : list A)(lsb : list B)(f1 : A -> C)(f2 : B -> C),
    list_pred (fun a b => f1 a = f2 b) lsa lsb ->
    map f1 lsa = map f2 lsb.
  
  induction lsa; inversion 1; intuition; simpl in *; subst.
  
  f_equal; eauto.
  
Qed.

Lemma zip_length : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    length (zip lsa lsb) = length lsa.
  
  induction lsa; intuition; simpl in *.
  destruct lsb;
    simpl in *.
  discriminate.

  f_equal.
  eapply IHlsa.
  omega.
  
Qed.


Definition numberedMap(A B : Set)(f : nat -> nat -> A -> B)(ls : list A) :=
  map (fun p => [i, a] <-2 p; f i (length ls) a) (zip (allNatsLt (length ls)) ls).

Lemma numberedMap_length : 
  forall (A B : Set)(ls : list A)(f : nat -> nat -> A -> B),
    length (numberedMap f ls) = length ls.
  
  intuition.
  unfold numberedMap.
  rewrite map_length.

  repeat rewrite zip_length.
  apply allNatsLt_length.
  apply allNatsLt_length.
Qed.

Lemma nth_zip : 
  forall (A B : Set)(lsa : list A)(lsb : list B) n a b defa defb,
    length lsa = length lsb ->
    nth n (zip lsa lsb) (defa, defb) = (a, b) ->
    nth n lsa defa = a /\ nth n lsb defb = b.
  
  induction lsa; destruct lsb; destruct n; intuition; simpl in *; try omega; try pairInv; intuition.
  
  inversion H; clear H; subst.
  eapply IHlsa.
  eauto.
  eauto.
  
  eapply IHlsa.
  eauto.
  eauto.
Qed.


Lemma compFold_spec' : 
  forall (A B C D : Set)(P2 : list A -> list B -> C -> D -> Prop)(eqdc1 eqdc2  : EqDec C)(eqdd1 eqdd2 : EqDec D)(lsa : list A)(lsb : list B)(c1 : C -> A -> Comp C)(c2 : D -> B -> Comp D) init1 init2,
    length lsa = length lsb ->
    P2 lsa lsb init1 init2 ->
    (forall a lsa b lsb c d, P2 (a :: lsa) (b :: lsb) c d -> comp_spec (P2 lsa lsb) (c1 c a) (c2 d b)) ->
    @comp_spec _ _ eqdc1 eqdd1 (P2 nil nil) (compFold eqdc2 c1 init1 lsa) (compFold eqdd2 c2 init2 lsb).
  
  induction lsa; destruct lsb; intuition.
  simpl.
  eapply comp_spec_ret; intuition.
  
  simpl in *.
  discriminate.
  simpl in *.
  discriminate.
  
  simpl.
  eapply comp_spec_seq; intuition.
  eapply H1; eauto.
  eapply IHlsa; eauto.
Qed.
  

Lemma compMap_support_app : 
  forall (A B : Set)(eqd : EqDec B)(c : A -> Comp B)(lsa1 lsa2 : list A)(lsb1 lsb2 : list B),
    In lsb1 (getSupport (compMap _ c lsa1)) ->
    In lsb2 (getSupport (compMap _ c lsa2)) ->
    In (lsb1 ++ lsb2) (getSupport (compMap _ c (lsa1 ++ lsa2))).
  
  induction lsa1; intuition.
  
  simpl in H.
  intuition; subst.
  
  repeat rewrite app_nil_l.
  trivial.
  
  unfold compMap in H.
  fold compMap in H.
  repeat simp_in_support.
  
  repeat rewrite <- app_comm_cons.
  unfold compMap.
  fold compMap.
  eapply getSupport_In_Seq; eauto.
  eapply getSupport_In_Seq; eauto.
  simpl; intuition.
  
Qed.

Lemma list_pred_single : 
  forall (A : Set) (P : A -> A -> Prop) (lsa : list A),
    (forall a, In a lsa -> P a a) ->
    list_pred P lsa lsa.
  
  induction lsa; intuition; simpl in *;
  econstructor.
  eapply H.
  intuition.
  eauto.
  
Qed.

Lemma flatten_map_eq : 
  forall (A B : Set)(ls : list (list A))(f : A -> B),
    map f (flatten ls) = flatten (map (fun ls' => map f ls') ls).
  
  induction ls; intuition; simpl in *.
  rewrite map_app.
  f_equal; eauto.
  
Qed.

Lemma zip_app : 
  forall (A B : Set)(lsa1 lsa2 : list A)(lsb1 lsb2 : list B),
    length lsa1 = length lsb1 ->
    length lsa2 = length lsb2 ->
    (zip lsa1 lsb1) ++ (zip lsa2 lsb2) =
    (zip (lsa1 ++ lsa2) (lsb1 ++ lsb2)).
  
  induction lsa1; destruct lsb1; destruct lsa2; destruct lsb2; intuition; simpl in *; try omega.
  
  repeat rewrite app_nil_r.
  trivial.
        
  f_equal.
  rewrite <-  IHlsa1.
  simpl.
  trivial.
  omega.
  simpl.
  omega.
        
Qed.

Lemma length_flatten_eq : 
  forall (A B : Set)(lsa : list (list A))(lsb : list (list B)),
    list_pred (fun a1 a2 => length a1 = length a2) lsa lsb ->
    length (flatten lsa) = length (flatten lsb).
  
  induction 1; intuition; simpl in *.
  
  repeat rewrite app_length.
  f_equal.
  trivial.
  trivial.
  
Qed.

Lemma flatten_map_pair_eq : 
  forall (A B C : Set)(ls : list (list A * list B))(f : A * B -> C),
    (forall ls1 ls2, In (ls1, ls2) ls -> length ls1 = length ls2) ->
    flatten (map (fun p => [ls1, ls2] <-2 p; map f (zip ls1 ls2)) ls) = 
    map f (zip (flatten (fst (unzip ls))) (flatten (snd (unzip ls)))).
  
  induction ls; intuition; simpl in *.
  
  rewrite IHls.
  
  rewrite <- zip_app.
  rewrite map_app.
  trivial.
  eapply H.
  intuition.
  
  eapply length_flatten_eq.
  eapply list_pred_map_r'.
  eapply list_pred_map_l'.

  eapply list_pred_single.
  intuition.
  destruct a. simpl.
  eapply H.
  intuition.
  
  intuition.

Qed.

Lemma compMap_app : 
  forall (A B : Set)(eqd : EqDec B)(ls1 ls2 : list A)(c : A -> Comp B) x,
    evalDist (compMap _ c (ls1 ++ ls2)) x ==
    evalDist (r1 <-$ compMap _ c ls1; r2 <-$ compMap _ c ls2; ret (r1 ++ r2)) x.
  
  induction ls1; intuition.
  
  rewrite app_nil_l.
  unfold compMap.
  fold compMap.
  comp_simp.
  
  rewrite <- evalDist_right_ident.
  comp_skip.
  simpl.
  reflexivity.

  rewrite <- app_comm_cons.
  unfold compMap.
  fold compMap.
  inline_first.
  comp_skip.
  eapply eqRat_trans.
  comp_skip.
  eapply eqRat_refl.
  inline_first.
  comp_skip.
  inline_first.
  comp_simp.
  comp_skip.
  simpl.
  intuition.
Qed.

Lemma compMap_flatten :
  forall (A B : Set)(eqd : EqDec B)(c : A -> Comp B)(ls : list (list A)),
    comp_spec
      (fun ls1 ls2 => ls2 = flatten ls1)
      (compMap _ (fun ls' => compMap _ c ls') ls)
      (compMap _ c (flatten ls)).
  
  induction ls; intuition; simpl in *.

  eapply comp_spec_ret; simpl; intuition.

  eapply comp_spec_eq_trans_r.
  2:{
    eapply comp_spec_eq_symm.
    eapply eq_impl_comp_spec_eq.
    intros.
    eapply compMap_app.
  }
  comp_skip.
  eapply comp_spec_seq.
  apply nil.
  apply nil.
  eapply IHls.
  intuition.
  subst.
  eapply comp_spec_ret.
  simpl.
  intuition.
Qed.

Lemma map_f_equal : 
  forall (A B : Set)(f1 f2 : A -> B)(ls1 ls2 : list A),
    (forall a, f1 a = f2 a) ->
    ls1 = ls2 ->
    map f1 ls1 = map f2 ls2.
  
  intuition.
  subst.
  eapply map_ext.
  trivial.
  
Qed.

Lemma list_pred_zip_eq_rev : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    (length lsa = length lsb) ->
    list_pred (fun p1 p2 => [a1, b1] <-2 p1; [b2, a2] <-2 p2; a1 = a2 /\ b1 = b2) (zip lsa lsb) (zip lsb lsa).
  
  induction lsa; destruct lsb; intuition; simpl in *; try omega;
  econstructor.
  
  intuition.
  eauto.
  
Qed.

Lemma list_pred_zip_in : 
  forall (A B : Set)(P : A -> B -> Prop)(lsa : list A)(lsb : list B),
    list_pred P lsa lsb ->
    forall a b, 
      In (a, b) (zip lsa lsb) ->
      P a b.
  
  induction 1; intuition; simpl in *.
  intuition.
  intuition.
  
  pairInv.
  trivial.
Qed.

Lemma in_zip_swap : 
  forall (A B : Set)(lsa : list A)(lsb : list B) a b,
    length lsa = length lsb ->
    In (a, b) (zip lsa lsb) ->
    In (b, a) (zip lsb lsa).
  
  induction lsa; destruct lsb; intuition; simpl in *; try omega.
  intuition.
  pairInv.
  intuition.
  
Qed.

Lemma unzip_zip_inv : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    unzip (zip lsa lsb) = (lsa, lsb).
  
  induction lsa; destruct lsb; intuition; simpl in *; try omega.
  
  unfold unzip in *.
  simpl.
  
  assert ((map (fst (B:=B)) (zip lsa lsb), map (snd (B:=B)) (zip lsa lsb)) =
          (lsa, lsb)).
  eapply IHlsa.
  omega.
  
  repeat f_equal.
  
  congruence.
  congruence.
Qed.

Notation "'foreach' '(' x 'in' ls ')' c " := (compMap _ (fun x => c) ls) (right associativity, at level 85, only parsing) : comp_scope.
Notation "'foreach' '(' x 'in' ls ')' c " := (map (fun x => c) ls) (right associativity, at level 85, only parsing).
Notation "'for' '(' x ''<' n ')' c " := (map (fun x => c) (allNatsLt n)) (right associativity, at level 86, only parsing).


Fixpoint removePresent (A : Set)(eqd : eq_dec A)(u ls : list A) :=
  match ls with
    | nil => nil
    | a' :: ls' =>
      ls'' <- removePresent eqd u ls'; 
        if (in_dec eqd a' u) then ls'' else (a' :: ls'')
  end.

Lemma removePresent_not_in : 
  forall (A : Set)(eqd : eq_dec A)(a : A) ls1 ls2,
    In a (removePresent eqd ls1 ls2) ->
    In a ls1 -> 
    False.
  
  induction ls2; intuition; simpl in *.
  unfold setLet in *.
  destruct (in_dec eqd a0 ls1).
  eauto.
  simpl in *.
  intuition; subst.
  intuition.
  
Qed.

Ltac hypInv :=
      try (match goal with
          | [H: Some _ = Some _ |-_ ] => inversion H; clear H; subst
      end); try pairInv.

Fixpoint lookupIndex (A : Set)(eqd : eq_dec A)(ls : list A)(a : A) def :=
  match ls with
    | nil => def
    | a' :: ls' =>
      if (eqd a a') then O else S (lookupIndex eqd ls' a def)
  end.

Lemma nth_lookupIndex : 
  forall (A : Set)(eqd : eq_dec A)(ls : list A) n (a a': A),
    In a ls ->
    nth (lookupIndex eqd ls a n ) ls a' = a.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  intuition; subst.
  destruct (eqd a0 a0); try congruence.
       
  destruct (eqd a0 a); subst.
  trivial.
  eauto.
  
Qed.

Theorem map_ext_in : 
  forall (A B : Set)(ls : list A)(f1 f2 : A -> B),
    (forall a, In a ls -> f1 a = f2 a) ->
    map f1 ls = map f2 ls.
  
  induction ls; intuition; simpl in *.
  f_equal.
  eapply H.
  intuition.
  eauto.
  
Qed.

Lemma nth_map_In : 
  forall (A B : Set)(ls : list A)(f : A -> B) i defa defb,
    i < length ls ->
    nth i (map f ls) defa = f (nth i ls defb).
  
  induction ls; intuition; simpl in *.
  destruct i.
  omega.
  omega.
  
  destruct i.
  trivial.
  eapply IHls.
  omega.
  
Qed.

Lemma removePresent_In : 
  forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) a,
    In a ls2 ->
    (~ In a ls1) ->
    In a (removePresent eqd ls1 ls2).
  
  induction ls2; intuition; simpl in *.
  intuition; subst.
  unfold setLet.
  destruct (in_dec eqd a0 ls1); intuition.
  
  unfold setLet.
  destruct (in_dec eqd a ls1); subst.
  eauto.
  
  simpl.
  destruct (eqd a a0); subst.
  intuition.
  
  right.
  eauto.
  
Qed.

Lemma lookupIndex_lt_length :
  forall (A : Set)(eqd : eq_dec A)(ls : list A) a def,
    In a ls -> 
    lookupIndex eqd ls a def < length ls.
  
  induction ls; intuition; simpl in *;
  intuition; subst.
  
  destruct (eqd a0 a0); subst; intuition.
  
  destruct (eqd a0 a); subst.
  omega.
  eapply lt_n_S.
  eapply IHls.
  trivial.
  
Qed.

Lemma skipn_app : 
  forall (A : Set)(ls1 ls2 : list A),
    skipn (length ls1) (ls1 ++ ls2) = ls2.
  
  induction ls1; intuition; simpl in *; intuition.
  
Qed.

Lemma fold_add_init_nat_h : 
  forall (A : Set)(f : A -> nat)(ls : list A)(init1 init2 : nat),
    (fold_left (fun acc a => acc + (f a))%nat ls (init1 + init2) = 
     init1 + fold_left (fun acc a => acc + (f a))%nat ls init2)%nat.
  
  induction ls; intuition; simpl in *.
  rewrite <- plus_assoc.
  eapply IHls.
  
Qed.

Lemma fold_add_init_nat : 
  forall (A : Set)(f : A -> nat)(ls : list A)(init : nat),
    (fold_left (fun acc a => acc + (f a))%nat ls init = 
     init + fold_left (fun acc a => acc + (f a))%nat ls O)%nat.
  
  intuition.
  rewrite <- (plus_0_r init) at 1.
  rewrite fold_add_init_nat_h.
  trivial.
Qed.

Lemma length_flatten : 
  forall (A : Set)(ls : list (list A)),
    length (flatten ls) =
    fold_left (fun acc a => (acc + (length a))%nat) ls O.
  
  induction ls; intuition; simpl in *.
  rewrite app_length.
  rewrite fold_add_init_nat.
  f_equal.
  eauto.
Qed.

Lemma fold_left_map_eq : 
  forall (A B C : Set)(ls : list A)(f1 : A -> B)(f2 : C -> B -> C)(init : C),
    fold_left (fun acc b => f2 acc b) (map f1 ls) init = 
    fold_left (fun acc a => f2 acc (f1 a)) ls init.
  
  induction ls; intuition; simpl in *.
  eauto.
  
Qed.

Lemma fold_add_nat_Permutation : 
  forall (A : Set)(f : A -> nat)(ls1 ls2 : list A),
    Permutation ls1 ls2 ->
    fold_left (fun acc a => acc + (f a))%nat ls1 O = 
    fold_left (fun acc a => acc + (f a))%nat ls2 O.
  
  induction 1; intuition; simpl in *.
  rewrite fold_add_init_nat.
  symmetry.
  rewrite fold_add_init_nat.
  symmetry.
  f_equal.
  eauto.
  
  rewrite plus_comm.
  trivial.
Qed.

Lemma intersect_NoDup : 
  forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
    NoDup ls2 ->
    NoDup (intersect eqd ls1 ls2).
  
  intuition.
  eapply filter_NoDup.
  trivial.
  
Qed.

Lemma intersect_comm_Permutation : 
  forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
    NoDup ls1 ->
    NoDup ls2 ->
    Permutation
      (intersect eqd ls1 ls2)
      (intersect eqd ls2 ls1).
  
  intuition.
  
  eapply NoDup_Permutation; intuition.
  
  eapply intersect_NoDup.
  trivial.
  eapply intersect_NoDup.
  trivial.
  
  unfold intersect in *.
  apply filter_In in H1.
  intuition.
  eapply filter_In; intuition.
  destruct (in_dec eqd x ls1); try congruence.
  destruct (in_dec eqd x ls2); intuition.
  
  unfold intersect in *.
  apply filter_In in H1.
  intuition.
  eapply filter_In; intuition.
  destruct (in_dec eqd x ls2); try congruence.
  destruct (in_dec eqd x ls1); intuition.
Qed.


Lemma fold_add_nat_filter_partition : 
  forall (A : Set)(P : A -> bool)(f : A -> nat)(ls : list A),
    fold_left (fun acc a => acc + (f a))%nat ls O = 
    (plus
       (fold_left (fun acc a => acc + (f a))%nat (filter P ls) O)
       (fold_left (fun acc a => acc + (f a))%nat (filter (fun a => negb (P a)) ls) O)
    ).
  
  induction ls; intuition; simpl in *.
  
  destruct (P a); simpl;
  repeat rewrite (fold_add_init_nat _ _ (f a)).
  rewrite IHls.
  repeat rewrite plus_assoc.
  trivial.
  
  rewrite IHls.
  repeat rewrite plus_assoc.
  f_equal.
  rewrite plus_comm.
  trivial.
  
Qed.

Lemma fold_left_add_removePresent : 
  forall (B : Set)(eqd : eq_dec B)(f : B -> nat)(ls u : list B),
    NoDup ls ->
    NoDup u ->
    fold_left (fun acc b => (acc + (f b))%nat) (removePresent eqd u ls) O = 
    minus 
      (fold_left (fun acc b => (acc + (f b))%nat) ls O)
      (fold_left (fun acc b => (acc + (f b))%nat) (intersect eqd ls u) O).
  
  
  induction ls; intuition; simpl in *.
  
  inversion H; clear H; subst.
  destruct (in_dec eqd a u).
  unfold setLet.
  rewrite IHls; trivial.
  rewrite (@fold_add_nat_Permutation _ _ (intersect eqd (a :: ls) u) (intersect eqd u (a :: ls))).
  
  simpl.
  destruct (in_dec eqd a u); intuition.
  simpl.
  
  repeat rewrite (@fold_add_init_nat _ _ _ (f a)).
  rewrite <- minus_plus_simpl_l_reverse.
  f_equal.
  eapply fold_add_nat_Permutation.
  eapply intersect_comm_Permutation; intuition.
  eapply intersect_comm_Permutation; intuition.
  econstructor; eauto.
  
  unfold setLet.
  rewrite (@fold_add_nat_Permutation _ _ (intersect eqd (a :: ls) u) (intersect eqd u (a :: ls))); trivial.
  simpl.
  destruct (in_dec eqd a u); intuition.
  
  repeat rewrite (@fold_add_init_nat _ _ _ (f a)).
  rewrite IHls.
  
  rewrite minus_plus_assoc.
  f_equal.
  f_equal.
  eapply fold_add_nat_Permutation.
  eapply intersect_comm_Permutation; intuition.
       
  rewrite (@fold_add_nat_filter_partition _ (fun a => if (in_dec eqd a u) then true else false) _ ls).
  rewrite <- plus_0_r at 1.
  eapply plus_le_compat; intuition.
  
  trivial.
  trivial.
  
  eapply intersect_comm_Permutation; intuition.
  econstructor; eauto.
  
Qed.

Lemma fold_add_nat_0 : 
  forall (A : Set)(ls : list A)(f : A -> nat), 
    (forall a, In a ls -> f a = O) ->
    fold_left (fun acc a => acc + (f a))%nat ls O = O.
  
  induction ls; intuition; simpl in *.
  
  rewrite H; intuition.
  
Qed.

Lemma map_snd_zip : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    map (fun p => snd p) (zip lsa lsb) = lsb.
  
  induction lsa; intuition; simpl in *.
  destruct lsb; simpl in *; congruence.
  
  destruct lsb; simpl in *; try omega.
  f_equal.
  eauto.
  
Qed.

Theorem Permutation_flatten :
  forall (A : Set)(ls1 ls2 : list (list A)),
    Permutation ls1 ls2 ->
    Permutation (flatten ls1) (flatten ls2).
  
  induction 1; intuition; simpl in *.
  eapply Permutation_app_head.
  trivial.
  
  repeat rewrite app_assoc.
  eapply Permutation_app_tail.
  eapply Permutation_app_comm.
  
  eapply Permutation_trans;
    eauto.
  
Qed.

Theorem zip_map_eq :
  forall (A B C : Set)(ls : list A)(f1 : A -> B)(f2 : A -> C),
    zip (map f1 ls) (map f2 ls) = map (fun a => (f1 a, f2 a)) ls.
  
  induction ls; intuition; simpl in *.
  f_equal.
  eauto.
Qed.

Theorem removePresent_in_only_if : 
  forall (A : Set)(eqd : eq_dec A)(u ls : list A) a,
    In a (removePresent eqd u ls) ->
    In a ls.
  
  induction ls; intuition; simpl in *.
  unfold setLet in *.
  destruct (in_dec eqd a u); intuition.
  simpl in *.
  intuition.
  
Qed.

Theorem removePresent_correct : 
  forall (A : Set)(eqd : eq_dec A)(u ls : list A) a,
    In a u ->
    In a (removePresent eqd u ls) ->
    False.
  
  induction ls; intuition; simpl in *.
  unfold setLet in *.
  
  destruct (in_dec eqd a u).
  eauto.
  simpl in *.
  intuition; subst; intuition.
  eauto.
Qed.

Theorem removePresent_NoDup :
  forall (A : Set)(eqd : eq_dec A)(u ls : list A),
    NoDup ls ->
    NoDup (removePresent eqd u ls).
  
  induction ls; intuition; simpl in *.
  unfold setLet.
  inversion H; clear H; subst.
  destruct (in_dec eqd a u); intuition.
  econstructor; intuition.
  eapply H2.
  eapply removePresent_in_only_if.
  eauto.
Qed.

Theorem removePresent_correct2 : 
  forall (A : Set)(eqd : eq_dec A)(u ls : list A) a,
    (~In a u) ->
    In a ls ->
    In a (removePresent eqd u ls).
  
  induction ls; intuition; simpl in *.
  unfold setLet in *.
  
  destruct (in_dec eqd a u).
  intuition; subst; intuition.
  
  intuition; subst.
  simpl.
  intuition.
Qed.

Definition optSwap (A : Set)(opt : option (A * A)) :=
  match opt with
    | None => None
    | Some (a1, a2) =>
      Some (a2, a1)
  end.

Theorem optSwap_involutive : 
  forall (A : Set)(opt : option (A * A)),
    optSwap (optSwap opt) = opt.
  
  intuition.
  unfold optSwap.
  destruct opt.
  destruct p.
  trivial.
  
  trivial.
  
Qed.

Theorem nth_listReplace_nil_eq : 
  forall (A : Set) i (a def1 def2 : A),
    nth i (listReplace nil i a def1) def2 = a.
  
  induction i; intuition; simpl in *.
  
Qed.

Theorem nth_listReplace_eq : 
  forall (A : Set) i (ls : list A) a def1 def2,
    nth i (listReplace ls i a def1) def2 = a.
  
  induction i; destruct ls; intuition; simpl in *.
  
  eapply nth_listReplace_nil_eq.
  
  eauto.
  
Qed.

Theorem nth_NoDup : 
  forall (A : Set)(ls : list (list A)) i,
    (forall e, In e ls -> NoDup e) ->
    NoDup (nth i ls nil).
  
  induction ls; destruct i; intuition; simpl in *.
  econstructor.
  econstructor.
  eauto.
      
Qed.      

Lemma listReplace_twice_nil : 
  forall (A : Set)(n : nat) (a1 a2 def : A),
    listReplace (listReplace nil n a1 def) n a2 def =
    listReplace nil n a2 def.
  
  induction n; intuition; simpl in *.
  f_equal.
  eapply IHn.
Qed.

Lemma listReplace_twice : 
  forall (A : Set)(n : nat)(ls : list A) a1 a2 def,
    listReplace (listReplace ls n a1 def) n a2 def =
    listReplace ls n a2 def.
  
  induction n; destruct ls; intuition; simpl in *.
  f_equal.
  eapply  listReplace_twice_nil.
  f_equal.
  eauto.
  
Qed.

Lemma compFold_foldBodyOption_None : 
  forall (A B : Set)(eqd : EqDec A)(c : A -> B -> Comp (option A))(ls : list B) x,
    evalDist (compFold _ (foldBody_option _ c) None ls) x ==
    evalDist (ret None) x.
  
  induction ls; intuition.
  unfold compFold.
  intuition.
  
  unfold compFold.
  fold compFold.
  unfold foldBody_option.
  comp_simp.
  eapply IHls.
  
Qed.

 Lemma Bvector_ne_exists : 
      forall (n : nat)(v : Bvector n),
        n > 0 ->
        exists v', v <> v'.

      induction n; intuition.
      omega.
      destruct (vector_S v).
      destruct H0.
      exists (Vector.cons bool (negb x) n x0).
      intuition.
      rewrite H0 in H1.
      inversion H1.
      destruct x; simpl in *; discriminate.
    Qed.

Lemma map_eq_inv : 
      forall (A B : Set)(f1 f2 : A -> B)(ls : list A),
        map f1 ls = map f2 ls ->
        forall a, In a ls -> f1 a = f2 a.

      induction ls; intuition; simpl in *;
      intuition.
      subst.
      inversion H; clear H; subst.
      trivial.
      inversion H; clear H; subst.
      eauto.

    Qed.

Lemma nth_lt_length : 
  forall (A : Set)(ls : list A)(i : nat) a def,
    nth i ls def = a ->
    def <> a ->
    i < length ls.
  
  induction ls; intuition; simpl in *.
  destruct i; intuition.
  
  destruct i; subst.
  omega.
  
  eapply lt_n_S.
  eauto.
  
Qed.

Lemma map_eq_nth_h : 
  forall (A B C : Set) (f1 : A -> C)(f2 : B -> C)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    map f1 lsa = map f2 lsb ->
    forall i def1 def2, 
      i < length lsa ->
      f1 (nth i lsa def1) = f2 (nth i lsb def2).
  
  induction lsa; destruct lsb; intuition; simpl in *; try omega.
  
  inversion H0; clear H0; subst.
  destruct i; intuition.
  
Qed.

Lemma map_eq_nth : 
  forall (A B C : Set) i def1 def2 (f1 : A -> C)(f2 : B -> C)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    map f1 lsa = map f2 lsb ->
    i < length lsa ->
    f1 (nth i lsa def1) = f2 (nth i lsb def2).
  
  intuition.
  eapply map_eq_nth_h; intuition.
  
Qed.

Theorem compFold_eq' : 
  forall (A1 A2 : Set) P (ls1 : list A1) (ls2 : list A2),
    list_pred P ls1 ls2 ->
    forall (B : Set)(eqd1 eqd2 : EqDec B) (c1 : B -> A1 -> Comp B) (c2: B -> A2 -> Comp B),
      (forall acc a1 a2 x, P a1 a2 -> In a1 ls1 -> In a2 ls2 ->evalDist (c1 acc a1) x == evalDist (c2 acc a2) x) ->
      forall init x, 
        evalDist (compFold eqd1 c1 init ls1) x == evalDist (compFold eqd2 c2 init ls2) x.
  
  induction 1; intuition.
  
  unfold compFold.
  eapply evalDist_ret_eq.
  intuition.
  
  unfold compFold.
  comp_skip.
  
Qed.

Lemma list_pred_flatten_both : 
  forall (A B : Set)(P : A -> B -> Prop)(lsa : list (list A))(lsb : list (list B)),
    list_pred (list_pred P) lsa lsb ->
    list_pred P (flatten lsa) (flatten lsb).
  
  induction 1; intuition; simpl in *.
  econstructor.
  
  eapply list_pred_app_both; intuition.
  
Qed.

Theorem compMap_wf :
  forall (A B : Set){eqdb : EqDec B}(c : A -> Comp B)(ls : list A),
    (forall a, In a ls -> well_formed_comp (c a)) ->
    well_formed_comp (compMap _ c ls).

  induction ls; intuition; simpl in *; wftac.

Qed.

Theorem list_pred_listReplace : 
  forall n (A B : Set) P (lsa : list A)(lsb : list B),
    list_pred P lsa lsb ->
    forall a b defa defb,
      P a b -> 
      P defa defb ->
      list_pred P (listReplace lsa n a defa) (listReplace lsb n b defb).
  
  induction n; intuition; simpl in *.
  
  inversion H; clear H; subst.
  econstructor; intuition.
  econstructor.
  econstructor; intuition.
  
  inversion H; clear H; subst.
  econstructor; intuition.
  eapply IHn.
  econstructor.
  intuition.
  intuition.
  
  econstructor; intuition.
  
Qed.

Theorem list_pred_nth : 
  forall n (A B : Set) P (lsa : list A)(lsb : list B) defa defb,
    list_pred P lsa lsb ->
    P defa defb ->
    P (nth n lsa defa) (nth n lsb defb).
  
  induction n; intuition; simpl in *.
       
  inversion H; clear H; subst; intuition; simpl in *.
  
  inversion H; clear H; subst; intuition; simpl in *.
  eapply IHn; intuition.
  
Qed.

Theorem compFold_cons : 
  forall (A B : Set)(eqda : EqDec A)(c : A -> B -> Comp A)(ls : list B) b (a : A),
    comp_spec eq (compFold _ c a (b :: ls)) (a' <-$ c a b; compFold _ c a' ls).
  
  intuition.
  simpl.
  eapply comp_spec_eq_refl.
Qed.

Theorem compFold_support_h : 
  forall (A B : Set)(eqda : EqDec A)(P : A -> list B -> list B -> Prop)(c : A -> B -> Comp A) (ls1 ls2 ls3 : list B)(a z : A),
    In z (getSupport (compFold _ c a ls1)) ->
    P a ls2 (ls1 ++ ls3) ->
    (forall a1 a2 b ls1 ls2,
       In a2 (getSupport (c a1 b)) ->
       P a1 ls1 (b :: ls2) ->
       P a2 (ls1 ++ (b :: nil)) ls2
    ) ->
    P z (ls2 ++ ls1) ls3.
  
  induction ls1; intuition; simpl in *.
  intuition; subst.
  rewrite app_nil_r.
  trivial.
  eapply in_getUnique_if in H.
  eapply in_flatten in H.
  destruct H.
  intuition.
  eapply in_map_iff in H2.
  destruct H2.
  intuition.
  subst.
  
  rewrite app_cons_eq.
  eapply IHls1.
  eauto.
  eapply H1.
  eauto.
  eauto.
  
  intuition.
Qed.

Theorem compFold_support : 
  forall (A B : Set)(eqda : EqDec A)(P : A -> list B -> list B -> Prop)(c : A -> B -> Comp A) (ls1 : list B)(a z : A),
    In z (getSupport (compFold _ c a ls1)) ->
    P a nil ls1 ->
    (forall a1 a2 b ls1 ls2,
       In a2 (getSupport (c a1 b)) ->
       P a1 ls1 (b :: ls2) ->
       P a2 (ls1 ++ (b :: nil)) ls2
    ) ->
    P z ls1 nil.
  
  intuition.
  eapply (compFold_support_h _ P c ls1 nil nil); intuition.
  eauto.
  rewrite app_nil_r.
  trivial.
Qed.

Theorem list_pred_app_both_if : 
   forall (A B : Set) P (x y : list A)(z q : list B),
     length x = length z ->
     list_pred P (x ++ y) (z ++ q) ->
     list_pred P x z /\ list_pred P y q.
   
   intros.
   eapply list_pred_app in H0.
   rewrite H in H0.
   rewrite ?firstn_app, ?skipn_app, ?firstn_ge_all,
     ?minus_diag, ?firstn_O, ?app_nil_r in * by omega.
   firstorder.
Qed.

Theorem compMap_seq_map :
  forall (A B C : Set)(eqdc : EqDec C)(ls : list A)(f : A -> B)(c : B -> Comp C),
    comp_spec eq
              (compMap _ c (map f ls))
              (compMap _ (fun x => c (f x)) ls).
  
  induction ls; intuition; simpl in *.
  eapply comp_spec_eq_refl.
  
  comp_skip.
  comp_skip.
  
Qed.

Lemma compMap_Repeat_close : 
  forall n (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c : Comp A)(P : A -> bool)(f : A -> B) x,
    well_formed_comp c ->
    (exists a, In a (filter P (getSupport c))) ->
    | (evalDist 
      (a <-$ compMap eqda (fun _ : nat => c) (forNats n);
       ret hd_error (map f (filter P a))) x) - 
      (evalDist 
         (a <-$ Repeat c P; ret Some (f a)) x) | <= 
     expRat (Pr[a <-$ c; ret (negb (P a))]) n.

  induction n; intuition.

  unfold forNats.
  unfold compMap.

  unfold expRat.
  eapply ratDistance_le.
  eapply evalDist_le_1.
  eapply evalDist_le_1.
  destruct H0; intuition.

  unfold forNats.
  fold forNats.
  unfold compMap.
  fold compMap.
  unfold expRat.
  fold expRat.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply ratDistance_eqRat_compat.
  eapply eqRat_refl.
  eapply evalDist_seq.
  intuition.
  intuition.
  eapply repeat_unroll_eq; intuition.
  econstructor; eauto.
  intuition.
  eapply eqRat_refl.

  assert (forall x, 
            evalDist
              (a <-$
                 (b <-$ c;
                  lsb' <-$ compMap eqda (fun _ : nat => c) (forNats n); ret b :: lsb');
               ret hd_error (map f (filter P a))) x == 
            evalDist
              (a <-$ c;
               a' <-$ 
                 (
                  lsa <-$ compMap eqda (fun _ : nat => c) (forNats n);
                  ret hd_error (map f (filter P lsa)));
               ret (if (P a) then Some (f a) else a')) x).
  intuition.
  inline_first.
  comp_skip.
  inline_first.
  comp_skip.
  comp_simp.
  simpl.
  case_eq (P x2); intuition.
  simpl.
  unfold value.
  intuition.

  rewrite H1.
  clear H1.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply ratDistance_eqRat_compat.
  eapply eqRat_refl.
  comp_inline_l.
  eapply eqRat_refl.

  assert 
    ((|
   evalDist
     (a <-$ c;
      a' <-$
      (lsa <-$ compMap eqda (fun _ : nat => c) (forNats n);
       ret hd_error (map f (filter P lsa))); ret (if P a then Some (f a) else a')) x -
   evalDist
     (a <-$ c; r2 <-$ (if P a then ret a else Repeat c P); ret Some (f r2)) x |) ==
     (|
      sumList (getSupport c) (fun a => evalDist c a * 
   (evalDist
     (a' <-$
      (lsa <-$ compMap eqda (fun _ : nat => c) (forNats n);
       ret hd_error (map f (filter P lsa))); ret (if P a then Some (f a) else a'))) x) -
      sumList (getSupport c) (fun a => evalDist c a * 
   (evalDist
     (r2 <-$ (if P a then ret a else Repeat c P); ret Some (f r2)) x)) | )).

  simpl.
  intuition.
  rewrite H1.
  clear H1.
  eapply leRat_trans.
  eapply sumList_distance_prod.
  cbv beta.
  rewrite (sumList_filter_partition P).
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  eapply eqRat_impl_leRat.
  eapply sumList_0; intuition.
  apply filter_In in H1; intuition.
  rewrite H3.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply eqRat_trans.
  eapply ratDistance_eqRat_compat.
  comp_irr_l.

  wftac.
  eapply compMap_wf; intuition.

  eapply eqRat_refl.
  comp_ret_l.
  eapply eqRat_refl.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  eapply ratMult_0_r.

  eapply sumList_le; intuition.
  apply filter_In in H1; intuition.
  destruct (P a).
  simpl in *.
  discriminate.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  rewrite evalDist_right_ident.
  eapply IHn; intuition.
  econstructor; eauto.
  rewrite <- ratAdd_0_l.
  rewrite sumList_factor_constant_r.
  eapply ratMult_leRat_compat; intuition.
  simpl.
  eapply eqRat_impl_leRat.
  symmetry.
  rewrite (sumList_filter_partition (P )).
  symmetry.
  rewrite ratAdd_0_l.
  eapply ratAdd_eqRat_compat; intuition.
  symmetry.
  eapply sumList_0; intuition.
  apply filter_In in H2.
  intuition.
  destruct (EqDec_dec bool_EqDec (negb (P a)) true).
  destruct (P a).
  simpl in *.
  discriminate.
  discriminate.
  eapply ratMult_0_r.

  eapply sumList_body_eq; intuition.
  apply filter_In in H2.
  intuition.
  destruct (EqDec_dec bool_EqDec (negb (P a)) true).
  rewrite ratMult_1_r.
  intuition.
  congruence.
Qed.

Theorem compMap_head : 
  forall (A B : Set)(eqd : EqDec B)(f : A -> Comp B)(ls : list A) x,
    (forall a, In a ls -> well_formed_comp (f a)) ->
    evalDist (ls' <-$ compMap _ f ls; ret (head ls')) x ==
    evalDist (match (head ls) with
                  | None => ret None
                  | Some a => b <-$ f a; ret (Some b)
              end) x.

  destruct ls; intuition.

  unfold compMap.
  unfold hd_error.
  unfold error.
  comp_simp.
  intuition.

  unfold compMap. fold compMap.
  unfold hd_error. fold hd_error.
  unfold value.
  
  inline_first.
  comp_skip.
  inline_first.
  comp_irr_l.
  eapply compMap_wf.
  intuition.
  intuition.
Qed.

Theorem compMap_filter : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list A)(c : A -> Comp B)(P : A -> bool) x,  
    (forall a, In a ls -> well_formed_comp (c a)) ->
    evalDist (compMap _ c (filter P ls)) x ==
    evalDist (ps <-$ compMap _ (fun a => b <-$ (c a); ret (a, b)) ls; ret (snd (unzip (filter (fun p => P (fst p)) ps)))) x.
  
  induction ls; intuition.
  unfold filter.
  unfold compMap.
  comp_simp.
  simpl.
  intuition.
  
  rewrite filter_cons.
  case_eq (P a); intuition.
  unfold compMap.
  fold compMap.
  inline_first.
  comp_skip.
  comp_simp.
  eapply eqRat_trans.
  comp_skip.
  eapply eqRat_refl.
  inline_first.
  comp_skip.
  comp_simp.
  dist_compute.

  unfold compMap.
  fold compMap.
  inline_first.
  comp_irr_r.
  comp_simp.
  
  rewrite IHls.
  inline_first.
  comp_skip.
  comp_simp.
  dist_compute.

  intuition.

Qed.

Theorem prob_sum_le : 
  forall (A : Set)(ls : list A)(c : A -> Comp bool),
    Pr 
      [compFold _ (fun b a => x <-$ c a; ret (b || x)) false ls] <=
    sumList ls (fun a => Pr [c a]).
  
  Local Opaque evalDist.
  
  induction ls; intuition.
  simpl in *.
  rewrite evalDist_ret_0.
  eapply rat0_le_all.
  intuition.
  
  simpl.
  
  inline_first.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply sumList_cons.
  }
  simpl.
  
  comp_at comp_ret leftc 1%nat.
  
  assert (
      Pr 
        [a0 <-$ c a;
          compFold bool_EqDec (fun (b : bool) (a1 : A) => x <-$ c a1; ret b || x)
                   a0 ls ]
      <=
      Pr 
        [a0 <-$ c a;
          a1 <-$ compFold bool_EqDec (fun (b : bool) (a1 : A) => x <-$ c a1; ret b || x)
             false ls;
          ret (a0 || a1) ]
    ).
  comp_skip.
  
  rewrite <- evalDist_right_ident.
  eapply comp_spec_impl_le.
  comp_skip.
  eapply (@compFold_spec _ _ _ (fun _ a b => x = false -> a = b)).
  intuition.
  intuition.
  comp_skip.
  eapply comp_spec_ret; intuition.
  subst.
  trivial.
  eapply comp_spec_ret; intuition.
  destruct x; simpl in *; intuition.
  subst.
  intuition.
  
  rewrite H.
  clear H.

  
  rewrite prob_or_le_sum.
  eapply ratAdd_leRat_compat; intuition.

  Grab Existential Variables.
  intuition.

Qed.

Theorem prob_sum_le_mult : 
  forall (n : nat)(c : Comp bool),
    Pr 
      [compFold _ (fun b a => x <-$ c; ret (b || x)) false (forNats n)] <=
    n/1 * Pr [c].
  
  intuition.
  rewrite prob_sum_le.
  
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply sumList_body_eq.
  intuition.
  symmetry.
  eapply ratMult_1_r.
  rewrite sumList_factor_constant_l.
  rewrite ratMult_comm.
  eapply ratMult_leRat_compat; intuition.

  rewrite  sumList_1_mult.
  rewrite forNats_length.
  intuition.
Qed.

Theorem compMap_Q_eq_compFold : 
  forall (B : Set)(eqdb : EqDec B)(Q : B -> bool) n1  (c : Comp B) z,
    Pr[ls <-$ compMap _ (fun _ => c) (forNats n1); ret (fold_left (fun b x => b || (Q x)) ls z)] == 
    Pr[compFold _ (fun b _ => z <-$ (x <-$ c; ret Q x); ret b || z) z (forNats n1)].
  
  induction n1; intuition.
  
  simpl.
  comp_simp.
  simpl.
  intuition.

  Local Opaque evalDist.
  simpl.
  inline_first.
  comp_skip.
  inline_first.
  comp_simp.
  comp_at comp_ret leftc 1%nat.
  eapply IHn1.
Qed.

Theorem Repeat_unroll_n : 
  forall n (A : Set)(eqda : EqDec A)(c : Comp A)(P : A -> bool) a,
    well_formed_comp c ->
    (exists x, In x (filter P (getSupport c))) ->
    evalDist (Repeat c P) a == 
    evalDist (x <-$ compMap _ (fun _ => c) (forNats n);
              match (hd_error (filter P x)) with
                | None => Repeat c P
                | Some z => ret z
              end) a.
  
  induction n; intuition.
  unfold forNats.
  unfold compMap.
  comp_simp.
  simpl.
  intuition.
  
  unfold forNats.
  fold forNats.
  unfold compMap.
  fold compMap.
  inline_first.
  rewrite repeat_unroll_eq.
  comp_skip.
  inline_first.
  case_eq (P x); intuition.
  comp_irr_r.
  eapply compMap_wf.
  intuition.
  comp_simp.
  simpl.
  rewrite H2.
  simpl.
  reflexivity.
  rewrite IHn.
  comp_skip.
  reflexivity.
  comp_simp.
  simpl.
  rewrite H2.
  intuition.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Theorem compFold_ret_eq : 
  forall (A B : Set)(eqdb : EqDec B)(ls : list A)(f : B -> A -> B) init,
    comp_spec eq
              (compFold _ (fun b a => ret (f b a)) init ls)
              (ret (fold_left f ls init)).
  
  induction ls; intuition; simpl in *.
  eapply comp_spec_eq_refl.
  comp_simp.
  eauto.
  
Qed.

Theorem prob_fold_add_false_0 :
  forall (A B : Set)(c : Comp A)(ls : list B)(P : A -> bool),
    Pr[compFold _ (fun b _ => x <-$ c; ret b && (P x)) false ls] == 0.
  
  induction ls; intuition.
  simpl.
  rewrite evalDist_ret_0; intuition.
  
  simpl.
  inline_first.
  eapply leRat_impl_eqRat.
  eapply distro_irr_le.
  intuition.
  comp_simp.
  rewrite IHls.
  intuition.
  eapply rat0_le_all.

Qed.  

Theorem sumList_support_bool':
  forall (c : Comp bool) (f : bool -> Rat),
    sumList (getSupport c) (fun x => evalDist c x * f x) == 
    Pr  [c ] * (f true) + (evalDist c false * (f false)).
  
  intuition.
  case_eq (getSupport c);
    intuition.
  unfold sumList.
  simpl.
  
  assert (Pr[c] == 0).
  eapply getSupport_not_In_evalDist.
  rewrite H.
  simpl; intuition.
  rewrite H0.
  clear H0.
  
  assert (evalDist c false == 0).
  eapply getSupport_not_In_evalDist.
  rewrite H.
  simpl; intuition.
  rewrite H0.
  clear H0.
  
  repeat rewrite ratMult_0_l.
  rewrite <- ratAdd_0_r.
  reflexivity.
  
  destruct b.
  rewrite sumList_cons.
  eapply ratAdd_eqRat_compat; intuition.
  destruct l.
  
  unfold sumList.
  simpl.
  
  assert (evalDist c false == 0).
  eapply getSupport_not_In_evalDist.
  rewrite H.
  simpl; intuition.
  rewrite H0.
  clear H0.
  rewrite ratMult_0_l.
  intuition.
  
  destruct b.
  specialize (getSupport_NoDup c); intuition.
  rewrite H in H0.
  inversion H0; clear H0; subst.
  simpl in *; intuition.
  
  rewrite sumList_cons.
  symmetry.
  rewrite ratAdd_0_r at 1.
  eapply ratAdd_eqRat_compat.
  intuition.
  destruct l.
  unfold sumList; simpl; intuition.
  
  specialize (getSupport_NoDup c); intuition.
  rewrite H in H0.
  destruct b.
  inversion H0; clear H0; subst; simpl in *; intuition.
  inversion H0; clear H0; subst.
  inversion H4; clear H4; subst; simpl in *; intuition.
  
  rewrite sumList_cons.
  symmetry.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  destruct l.
  unfold sumList.
  simpl.
  
  assert (Pr[c] == 0).
  eapply getSupport_not_In_evalDist.
  rewrite H.
  simpl; intuition.
  rewrite H0.
  clear H0.
  eapply ratMult_0_l.
  
  destruct b.
  rewrite sumList_cons.
  rewrite ratAdd_0_r at 1.
  eapply ratAdd_eqRat_compat.
  intuition.
  
  destruct l.
  unfold sumList.
  simpl.
  intuition.
  
  specialize (getSupport_NoDup c); intuition.
  rewrite H in H0.
  destruct b.
  inversion H0; clear H0; subst.
  inversion H4; clear H4; subst; simpl in *; intuition.
  inversion H0; clear H0; subst; simpl in *; intuition.
  
  specialize (getSupport_NoDup c); intuition.
  rewrite H in H0.
  inversion H0; clear H0; subst; simpl in *; intuition.
  
Qed.

Theorem prob_fold_and_eq_exp_h : 
  forall (A B : Set)(c : Comp A)(ls : list B)(P : A -> bool),
    Pr[compFold _ (fun b _ => x <-$ c; ret b && (P x)) true ls] ==
    expRat (Pr[x <-$c; ret (P x)]) (length ls).
  
  induction ls; intuition.
  simpl.
  rewrite evalDist_ret_1; intuition.

  simpl.
  rewrite evalDist_seq_step.
  
  rewrite sumList_support_bool'.
  rewrite prob_fold_add_false_0.
  repeat rewrite ratMult_0_r.
  rewrite <- ratAdd_0_r.
  eapply ratMult_eqRat_compat; intuition.
Qed.

Theorem prob_fold_and_eq_exp : 
  forall (A : Set)(c : Comp A)(n : nat)(P : A -> bool),
    Pr[compFold _ (fun b _ => x <-$ c; ret b && (P x)) true (forNats n)] ==
    expRat (Pr[x <-$c; ret (P x)]) n.
  
  intuition.
  rewrite prob_fold_and_eq_exp_h.
  rewrite forNats_length.
  reflexivity.
  
Qed.

