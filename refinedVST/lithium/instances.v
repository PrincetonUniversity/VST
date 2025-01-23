From lithium Require Export base.
From VST.lithium Require Import syntax definitions proof_state.

(** This file collects the default instances for the definitions in
[definitions.v]. Note that these instances must be in a separate file
since the instances are defined using the notation from
[proof_state.v]. *)

(** * [find_in_context] *)
Lemma find_in_context_direct {prop:bi} {B} P (T : B → prop):
  find_in_context (FindDirect P) T :- pattern: x, P x; return T x.
Proof. done. Qed.
Definition find_in_context_direct_inst := [instance @find_in_context_direct with FICSyntactic].
Global Existing Instance find_in_context_direct_inst | 1.

(** * Simplification *)
Lemma simplify_hyp_id {prop:bi} (P : prop)  `{Affine prop P} (T : prop):
  simplify_hyp P T :- return T.
Proof. iIntros "HT Hl". iFrame. Qed.
Definition simplify_hyp_id_inst (prop:bi) (P : prop) `{affine_p: Affine prop P}:=
  [instance simplify_hyp_id P as SimplifyHyp P None].
Global Existing Instance simplify_hyp_id_inst | 100.

Lemma simplify_goal_id {prop:bi} (P : prop) T :
  simplify_goal P T :- exhale P; return T.
Proof. iIntros "$". Qed.
Definition simplify_goal_id_inst (prop:bi) (P : prop) :=
  [instance simplify_goal_id P as SimplifyGoal P None].
Global Existing Instance simplify_goal_id_inst | 100.

(** * Subsumption *)
Lemma subsume_id {prop:bi} {A} (P : prop) (T : A → prop):
  subsume P (λ _, P) T :- ∃ x, return T x.
Proof. iIntros "[% ?] $". by iExists _. Qed.
Definition subsume_id_inst := [instance @subsume_id].
Global Existing Instance subsume_id_inst | 1.

Lemma subsume_simplify {prop:bi} {A} (P1 : prop) (P2 : A → prop) o1 o2 T :
  (* TCOneIsSome must be first here since [instance ...] reverse the order *)
  ∀ `{!TCOneIsSome o1 o2} {SH : SimplifyHyp P1 o1} {SG : ∀ x, SimplifyGoal (P2 x) o2},
    let GH := (SH (∃ x, P2 x ∗ T x)%I).(i2p_P) in
    let GG := (P1 -∗ ∃ x, (SG x (T x)).(i2p_P))%I in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then GG else GH
     | Some n1, _ => GH
     | _, _ => GG
       end in
    subsume P1 P2 T :- return G.
Proof.
  iIntros (???) "/= Hs Hl".
  destruct o1 as [n1|], o2 as [n2|] => //. 1: case_match.
  1,3,4: by iDestruct (i2p_proof with "Hs Hl") as "Hsub".
  all: iDestruct ("Hs" with "Hl") as (?) "HSG"; iExists _.
  all: iDestruct (i2p_proof with "HSG") as "$".
Qed.
Definition subsume_simplify_inst := [instance @subsume_simplify].
Global Existing Instance subsume_simplify_inst | 1000.

(** * sep_list *)

Global Instance sep_list_related_to (prop:bi) A B id ig l f :
  @RelatedTo prop _ (λ x : B, sep_list id A (ig x) (l x) (f x)) :=
  {| rt_fic := FindSepList id |}.

Lemma find_sep_list {prop:bi} id (T : _ → prop):
  find_in_context (FindSepList id) T :-
    pattern: A ig l f, sep_list id A ig l f; return T (sep_list id A ig l f).
Proof. iIntros "(%&%&%&%&?&?)". iExists _. by iFrame. Qed.
Definition find_sep_list_inst := [instance @find_sep_list with FICSyntactic].
Global Existing Instance find_sep_list_inst | 1.

Lemma subsume_sep_list_eq {prop:bi} {_:BiPositive prop} {B} A id ig (l1 : list A) (l2 : B → list A) f (T : B → prop) :
  subsume (sep_list id A ig l1 f) (λ x : B, sep_list id A ig (l2 x) f) T :-
    ∃ x, exhale <affine> ⌜list_subequiv ig l1 (l2 x)⌝; return T x.
Proof.
  unfold sep_list. iDestruct 1 as (b Hequiv) "HT".  iIntros "[%Hln Hl]". iExists b. iFrame "HT".
  set (l2' := (l2 b)) in *. clearbody l2'; clear l2; rename l2' into l2.
  have [Hlen _]:= Hequiv 0. iSplit; first by iPureIntro; congruence. clear Hln.
  iInduction l1 as [|x l1] "IH" forall (f ig l2 Hlen Hequiv); destruct l2 => //=.
  (* rewrite bi.affinely_sep. *)
  iDestruct "Hl" as "[Hx Hl]". move: Hlen => /= [?].
  iSplitL "Hx".
  - case_bool_decide as Hb => //. have [_ /= Heq]:= Hequiv 0. by  move: (Heq Hb) => [->].
  - iDestruct ("IH" $! (f ∘ S) (pred <$> (filter (λ x, x ≠ 0%nat) ig)) l2 with "[//] [%] [Hl]") as "Hl". {
      move => i. split => // Hin. move: (Hequiv (S i)) => [_ /= {}Hequiv]. apply: Hequiv.
      contradict Hin. apply elem_of_list_fmap. eexists (S i). split => //.
        by apply elem_of_list_filter.
    }
    + iApply (big_sepL_impl with "Hl"). iIntros "!>" (k ??) "Hl".
      case_bool_decide as Hb1; case_bool_decide as Hb2 => //.
      contradict Hb2. apply elem_of_list_fmap. eexists (S k). split => //.
      by apply elem_of_list_filter.
    + iApply (big_sepL_impl with "Hl"). iIntros "!>" (k ??) "Hl".
      case_bool_decide as Hb1; case_bool_decide as Hb2 => //.
      contradict Hb2. move: Hb1 => /elem_of_list_fmap[[|?][? /elem_of_list_filter [??]]] //.
      by simplify_eq/=.
Qed.
Definition subsume_sep_list_eq_inst := [instance @subsume_sep_list_eq].
Global Existing Instance subsume_sep_list_eq_inst | 1000.

Lemma subsume_sep_list_insert_in_ig {prop:bi} {B} A id ig i x (l1 : list A) (l2 : B → list A)
  (f : nat → A → prop) (T : B → prop) :
  subsume (sep_list id A ig (<[i := x]>l1) f) (λ x : B, sep_list id A ig (l2 x) f) T
     where `{!CanSolve (i ∈ ig)} :-
  return subsume (sep_list id A ig l1 f) (λ x : B, sep_list id A ig (l2 x) f) T.
Proof.
  unfold CanSolve, sep_list => ?. iIntros "Hsub [<- Hl]".
  rewrite length_insert. iApply "Hsub". iSplit; [done|].
  destruct (decide (i < length l1)%nat). 2: { by rewrite list_insert_ge; [|lia]. }
  iDestruct (big_sepL_insert_acc with "Hl") as "[? Hl]". { by apply: list_lookup_insert. }
  have [//|y ?]:= lookup_lt_is_Some_2 l1 i.
  iDestruct ("Hl" $! y with "[]") as "Hl". { by case_decide. }
  destruct (bool_decide (i∈ig)); by rewrite list_insert_insert list_insert_id.
Qed.
Definition subsume_sep_list_insert_in_ig_inst := [instance @subsume_sep_list_insert_in_ig].
Global Existing Instance subsume_sep_list_insert_in_ig_inst.

Lemma subsume_sep_list_insert_not_in_ig {prop:bi} A B id ig i x (l1 : list A) l2 (f : nat → A → prop) (T : B → prop) :
  subsume (sep_list id A ig (<[i := x]>l1) f) (λ x : B, sep_list id A ig (l2 x) f) T
    where `{!CanSolve (i ∉ ig)} :-
      exhale <affine> ⌜i < length l1⌝%nat;
      inhale <affine> f i x;
      y ← (sep_list id A (i :: ig) l1 f) :>> (λ x : B, sep_list id A (i :: ig) (l2 x) f);
      ∃ x2, exhale <affine> ⌜l2 y !! i = Some x2⌝;
      exhale <affine> f i x2;
      return T y.
Proof.
  unfold CanSolve, sep_list. iIntros (?) "[% Hsub] [<- Hl]". rewrite big_sepL_insert // length_insert.
  iDestruct "Hl" as "[Hx Hl]". case_bool_decide => //.
  iDestruct ("Hsub" with "Hx [Hl]") as "[% [[%Heq Hl] [% [% [? HT]]]]]". {
    iSplit; [done|]. iApply (big_sepL_impl with "Hl"). iIntros "!>" (???) "?".
    repeat case_decide => //; set_solver.
  }
  iExists _. iFrame. iSplit; [done|].
  rewrite -{2}(list_insert_id (l2 _) i x2) // big_sepL_insert; [|lia]. case_bool_decide => //. iFrame.
  iApply (big_sepL_impl with "Hl"). iIntros "!>" (???) "?".
  repeat case_decide => //; set_solver.
Qed.
Definition subsume_sep_list_insert_not_in_ig_inst := [instance @subsume_sep_list_insert_not_in_ig].
Global Existing Instance subsume_sep_list_insert_not_in_ig_inst.

Lemma subsume_sep_list_trivial_eq {prop:bi} A B id ig (l : list A) (f : nat → A → prop) (T : B → prop) :
  subsume (sep_list id A ig l f) (λ x : B, sep_list id A ig l f) T :- ∃ x, return T x.
Proof. iIntros "[% ?] $". iExists _. by iFrame. Qed.
Definition subsume_sep_list_trivial_eq_inst := [instance @subsume_sep_list_trivial_eq].
Global Existing Instance subsume_sep_list_trivial_eq_inst | 5.

Lemma subsume_sep_list_cons {prop:bi} A B id ig (x1 : A) (l1 : list A) l2 (f : nat → A → prop) (T : B → prop) :
  subsume (sep_list id A ig (x1 :: l1) f) (λ y : B, sep_list id A ig (l2 y) f) T :-
    exhale <affine> ⌜0 ∉ ig⌝;
    ∀ id', inhale (<affine> f 0%nat x1);
    inhale (sep_list id' A (pred <$> ig) l1 (λ i, f (S i)));
    ∃ y x2 l2', exhale <affine> ⌜l2 y = x2 :: l2'⌝;
    exhale (<affine> f 0%nat x2);
    exhale (sep_list id' A (pred <$> ig) l2' (λ i, f (S i)));
    return T y.
Proof.
  unfold sep_list. iIntros "[% Hs] [<- Hl]".
  rewrite !big_sepL_cons /=. case_bool_decide => //. iDestruct "Hl" as "[H0 H]".
  iDestruct ("Hs" $! {|sep_list_len := _|} with "H0 [H]") as (??? Heq1) "[? [[%Heq2 H] ?]]".
  { iSplit; [simpl; done|]. iApply (big_sepL_impl with "H"); iIntros "!#" (???) "?".
    case_bool_decide as Hx1 => //; case_bool_decide as Hx2 => //; contradict Hx2.
    set_unfold. eexists _. split; [|done]. done. }
  iExists _. iFrame. iSplit. { iPureIntro. rewrite Heq1 /=. by rewrite Heq2. }
  rewrite Heq1 => /=. rewrite bool_decide_false //. iFrame.
  iApply (big_sepL_impl with "H"); iIntros "!#" (???) "?".
  case_bool_decide as Hx1 => //; case_bool_decide as Hx2 => //; contradict Hx2.
  by move: Hx1 => /(elem_of_list_fmap_2 _ _ _)[[|?]//=[->?]].
Qed.
Definition subsume_sep_list_cons_inst := [instance @subsume_sep_list_cons].
Global Existing Instance subsume_sep_list_cons_inst | 40.
