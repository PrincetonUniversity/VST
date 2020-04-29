Require Import VST.floyd.base2.
Require Import VST.floyd.canon.
Require Import VST.floyd.entailer.
Require Import Coq.Lists.List.
Export ListNotations.
Require Import VST.floyd.client_lemmas.

Local Open Scope logic.

Module ZOrder <: Orders.TotalLeBool.
  Definition t := Z.
  Definition leb := Z.leb.
  Theorem leb_total : forall a1 a2, Z.leb a1 a2 = true \/ Z.leb a2 a1 = true.
  Proof.  intros. destruct (Zle_bool_total a1 a2); auto. Qed. 
End ZOrder.
Module SortZ := Mergesort.Sort(ZOrder).

Module NatOrder <: Orders.TotalLeBool.
  Definition t := nat.
  Definition leb := Nat.leb.
  Theorem leb_total : forall a1 a2, Nat.leb a1 a2 = true \/ Nat.leb a2 a1 = true.
  Proof.  intros. 
    pose proof (Nat.leb_spec a1 a2).
    pose proof (Nat.leb_spec a2 a1).
    inv H; inv H0; auto; lia.
  Qed.
End NatOrder.
Module SortNat := Mergesort.Sort(NatOrder).

Module Type FREEZER.
Parameter FRZ : mpred -> mpred.
Parameter FRZ1: forall p, p |-- FRZ p.
Parameter FRZ2: forall p, FRZ p |-- p.

Parameter FRZL : list mpred -> mpred.
Parameter FRZL1: forall ps, fold_right sepcon emp ps |-- FRZL ps.
Parameter FRZL2: forall ps, FRZL ps |-- fold_right sepcon emp ps.

Parameter FRZRw : list mpred -> list mpred -> Type.
Parameter FRZRw_constr : forall {L1 G1: list mpred} {F: mpred},
    (fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F -> FRZRw L1 G1.
Parameter FRZR : forall L1 G1 {w: FRZRw L1 G1}, mpred.
Parameter FRZR1: forall L1 G1 (w: FRZRw L1 G1), fold_right sepcon emp G1 |-- fold_right sepcon emp L1 * @FRZR L1 G1 w.
Parameter FRZR2: forall L1 G1 L2 G2 F H, F |-- fold_right sepcon emp L2 -* fold_right sepcon emp G2 -> fold_right sepcon emp L2  * @FRZR L1 G1 (@FRZRw_constr L1 G1 F H) |-- fold_right sepcon emp G2.

End FREEZER.

Module Freezer : FREEZER.
Definition FRZ (p: mpred) := p.
Lemma FRZ1 p: p |-- FRZ p. apply derives_refl. Qed.
Lemma FRZ2 p: FRZ p |-- p. apply derives_refl. Qed.

Definition FRZL (ps:list mpred): mpred := fold_right sepcon emp ps.
Lemma FRZL1 ps: (fold_right_sepcon ps) |-- FRZL ps. apply derives_refl. Qed.
Lemma FRZL2 ps: FRZL ps |-- fold_right_sepcon ps. apply derives_refl. Qed.

Inductive FRZRw' (L1 G1: list mpred): Type :=
| FRZRw'_constr: forall F: mpred,
    (fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F -> FRZRw' L1 G1.

Definition FRZRw := FRZRw'.
Definition FRZRw_constr:= FRZRw'_constr.

Definition FRZR (L1 G1: list mpred) {w: FRZRw L1 G1}: mpred := 
  match w with
  | FRZRw'_constr F _ => F
  end.

Lemma FRZR1: forall L1 G1 (w: FRZRw L1 G1), fold_right sepcon emp G1 |-- fold_right sepcon emp L1 * @FRZR L1 G1 w.
Proof. intros ? ? [? ?]. auto. Qed.

Lemma FRZR2: forall L1 G1 L2 G2 F H, F |-- fold_right sepcon emp L2 -* fold_right sepcon emp G2 -> fold_right sepcon emp L2 * @FRZR L1 G1 (@FRZRw_constr L1 G1 F H) |-- fold_right sepcon emp G2.
Proof. intros ? ? ? ? ? ? ?. rewrite sepcon_comm. apply wand_sepcon_adjoint; auto. Qed.

End Freezer.

Notation FRZ := Freezer.FRZ.
Notation FRZL := Freezer.FRZL.
Notation FRZR := Freezer.FRZR.
Notation FRZRw := Freezer.FRZRw.

(************************ Freezing a single mpred ************************)
Lemma FRZ_ax:forall p, FRZ p = p.
Proof. intros. apply pred_ext. apply Freezer.FRZ2. apply Freezer.FRZ1. Qed.

Fixpoint freeze_nth (n: nat) (al: list mpred) {struct n}: list mpred :=
 match n, al with
 | O , a::al => (FRZ a) ::al
 | S n', a::al' => a :: freeze_nth n' al'
 | _, nil => nil
 end.

Lemma freeze1_SEP':
 forall n Espec {cs: compspecs} Delta P Q R c Post,
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (freeze_nth n R)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros. subst.
eapply semax_pre; try apply H.
apply andp_left2.
go_lowerx; entailer!.  clear.
generalize dependent R.
induction n; destruct R; simpl; cancel. apply Freezer.FRZ1.
Qed.
Tactic Notation "freeze1_SEP" constr(n) :=
  eapply (freeze1_SEP' (Z.to_nat n)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) :=
  (gather_SEP' (n::m::nil)); eapply (freeze1_SEP' (Z.to_nat 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k)  :=
  (gather_SEP' (n::m::k::nil)); eapply (freeze1_SEP' (Z.to_nat 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k)  constr(p) :=
  (gather_SEP' (n::m::k::p::nil)); eapply (freeze1_SEP' (Z.to_nat 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k) constr(p) constr(q) :=
  (gather_SEP' (n::m::k::p::q::nil)); eapply (freeze1_SEP' (Z.to_nat 0)); simpl.

(*******************freezing a list of mpreds ******************************)

Fixpoint delete_list {A: Type} (ns: list nat) (xs: list A) : list A :=
 (* ns must already be sorted *)
 match ns with
 | nil => xs
 | n::ns' => delete_nth n (delete_list ns' xs)
 end.

Definition freezelist_nth (ns: list nat) (al: list mpred) : list mpred * list mpred :=
  (map (fun i => my_nth i al emp) ns,
   delete_list (SortNat.sort ns) al).

Lemma my_nth_delete_nth_permutation: 
  forall al a, 
   (a < length al)%nat -> Permutation al (my_nth a al emp :: delete_nth a al).
Proof.
induction al; simpl; intros.
lia.
destruct a0; simpl.
apply Permutation_refl.
eapply Permutation_trans; [ | apply perm_swap].
apply perm_skip.
apply IHal.
lia.
Qed.

Function is_increasing (ns: list nat) (last: nat) {measure length ns}: bool  :=
 match ns with
 | nil => true
 | a::nil => Nat.ltb a last
 | a::b::ns' => andb (Nat.ltb a b) (is_increasing (b::ns') last)
 end.
Proof. intros. subst. simpl. lia.
Defined.


(*
Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  induction 1; simpl; intros; auto.
  inv H0; constructor; auto.
  inv H. inv H3. constructor; auto.
Qed.
*)

Lemma delete_nth_length:
   forall {A} i (al: list A), (i < length al)%nat ->
     (S (length (delete_nth i al)) = length al)%nat.
Proof.
induction i; destruct al; simpl; intros; try lia.
apply f_equal.
apply IHi; lia.
Qed.

Lemma freezelist_nth_permutation: forall ns al,
  is_increasing (SortNat.sort ns) (length al) = true ->
  Permutation al (fst (freezelist_nth ns al) ++ snd (freezelist_nth ns al)).
Proof.
unfold freezelist_nth.
simpl.
intros.
apply Permutation_trans
 with 
 (map (fun i : nat => my_nth i al emp) (SortNat.sort ns) ++
   delete_list (SortNat.sort ns) al).
2:{ apply Permutation_app_tail.
     apply Permutation_map.
     apply Permutation_sym.
     apply SortNat.Permuted_sort.
}
 forget (SortNat.sort ns) as ns'; clear ns; rename ns' into ns.
 revert al H; induction ns; simpl; intros.
 apply Permutation_refl.
 replace (my_nth a al emp) with (my_nth a (delete_list ns al) emp).
-
 eapply Permutation_trans; [ | apply Permutation_sym; apply Permutation_middle].
 eapply Permutation_trans; [ | apply Permutation_app_head; apply my_nth_delete_nth_permutation].
   apply IHns.
  rewrite is_increasing_equation in H. destruct ns; simpl; auto.
  rewrite andb_true_iff in H; destruct H; auto.
  rewrite is_increasing_equation in H. destruct ns; simpl; auto. 
  apply Nat.ltb_lt; auto.
  rewrite andb_true_iff in H; destruct H; auto.
  apply Nat.ltb_lt in H.
  clear - H H0.
  change (delete_nth n (delete_list ns al)) with (delete_list (n::ns) al).
  revert n a al H H0; induction ns; intros;
  rewrite is_increasing_equation in H0.
  simpl.
  apply Nat.ltb_lt in H0.
  pose proof (delete_nth_length n al H0). lia.
 change (delete_list (n :: a :: ns) al)%nat with (delete_nth n (delete_list ( a :: ns) al))%nat.
  rewrite andb_true_iff in H0; destruct H0; auto.
  apply Nat.ltb_lt in H0.
 specialize (IHns a n al).
 spec IHns; [lia|]. specialize (IHns H1).
 pose proof (delete_nth_length n (delete_list (a::ns) al) IHns).
 assert (a0 <= S (Datatypes.length
   (delete_nth n (delete_list (a :: ns) al))))%nat; [ | lia].
  rewrite H2.
 lia.
-
 clear - H.
 revert a al H; induction ns; intros.
 simpl. auto.
 simpl.
 transitivity (my_nth a0 (delete_list ns al) emp).
 +
  rewrite is_increasing_equation in H.
  rewrite andb_true_iff in H; destruct H.
  apply Nat.ltb_lt in H.
  forget (delete_list ns al) as bl.
  clear - H.
  revert a0 bl H; induction a; destruct a0, bl; simpl; intros; auto; try lia.
  apply IHa. lia.
 +  apply IHns.
   clear - H.
  rewrite is_increasing_equation in H.
  rewrite andb_true_iff in H; destruct H.
  apply Nat.ltb_lt in H.
  rewrite is_increasing_equation in H0.
  rewrite is_increasing_equation.
  destruct ns.
  apply Nat.ltb_lt in H0.
  apply Nat.ltb_lt. lia.
  rewrite andb_true_iff in H0; destruct H0.
  rewrite andb_true_iff; split; auto.
  apply Nat.ltb_lt in H0.
  apply Nat.ltb_lt. lia.
Qed.

(* This older version of freezelist_nth didn't work when the l list was not sorted 
Fixpoint freezelist_nth (l: list nat) (al: list mpred): (list mpred) * (list mpred) :=
 match l with
 | nil => (nil,al)
 | (n::l') => let (xs, ys) := freezelist_nth l' al
              in (nth n ys emp::xs, delete_nth n ys)
 end.
*)
Lemma FRZL_ax ps: FRZL ps = fold_right_sepcon ps.
Proof. intros. apply pred_ext. apply Freezer.FRZL2. apply Freezer.FRZL1. Qed.

Lemma fold_right_sepcon_deletenth: forall n (l: list mpred),
  fold_right_sepcon l = nth n l emp * fold_right_sepcon (delete_nth n l).
Proof.
  induction n; destruct l; simpl. rewrite sepcon_emp; trivial.
  reflexivity.
  rewrite sepcon_emp; trivial.
  rewrite IHn.
  do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm m). trivial.
Qed.
Lemma fold_right_sepcon_deletenth': forall n (l:list (LiftEnviron mpred)),
  @fold_right (environ -> mpred) (environ -> mpred) sepcon emp l =
  nth n l emp * fold_right sepcon emp (delete_nth n l).
Proof.
  induction n; destruct l; simpl. rewrite sepcon_emp; trivial.
  reflexivity.
  rewrite sepcon_emp; trivial.
  rewrite IHn; clear IHn. extensionality. simpl.
  do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm (l x)). trivial.
Qed.

Lemma fold_right_sepcon_permutation:
 forall al bl, Permutation al bl -> fold_right_sepcon al = fold_right_sepcon bl.
Proof.
intros.
induction H; simpl; auto.
congruence.
rewrite <- ! sepcon_assoc.
rewrite (sepcon_comm x).
auto.
congruence.
Qed.

Lemma freeze_SEP':
 forall l Espec {cs: compspecs} Delta P Q  R c Post xs ys,
  is_increasing (SortNat.sort l) (length R) = true ->
 (xs, ys) = freezelist_nth l R ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros *. intro Hii; intros. subst.
eapply semax_pre; try eassumption.
apply andp_left2. unfold PROPx. normalize.
apply andp_derives; auto.
pose proof (freezelist_nth_permutation _ _ Hii).
rewrite <- H in H2.
simpl in H2.
clear - H2.
unfold SEPx.
intros _.
rewrite (fold_right_sepcon_permutation _ _ H2).
rewrite FRZL_ax.
clear.
induction xs; simpl.
rewrite emp_sepcon.
auto.
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma freeze_SEP'entail:
 forall l Delta P Q  R Post xs ys,
  is_increasing (SortNat.sort l) (length R) = true ->
 (xs, ys) = freezelist_nth l R ->
 ENTAIL Delta, (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) |-- Post ->
 ENTAIL Delta, (PROPx P (LOCALx Q (SEPx R))) |-- Post.
Proof.
intros *. intro Hii; intros. subst.
eapply derives_trans; try apply H0.
unfold PROPx. normalize.
apply andp_derives; auto.
pose proof (freezelist_nth_permutation _ _ Hii).
rewrite <- H in H2.
simpl in H2.
clear - H2.
apply andp_derives; auto.
unfold SEPx.
intros _.
rewrite (fold_right_sepcon_permutation _ _ H2).
rewrite FRZL_ax.
clear.
induction xs; simpl.
rewrite emp_sepcon.
auto.
rewrite sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma map_delete_nth {A B} (f:A->B): forall n l, delete_nth n (map f l) = map f (delete_nth n l).
Proof.
  induction n; intros; destruct l; simpl; trivial.
  rewrite IHn. trivial.
Qed.

Fixpoint my_nth {A} (n : nat) (l : list A) (default : A) {struct l} : A :=
  match n with
  | 0%nat => match l with
             | [] => default
             | x :: _ => x
             end
  | S m => match l with
           | [] => default
           | _ :: t => my_nth m t default
           end
  end.

Lemma my_nth_nth {A}: forall n l (d:A), my_nth n l d = nth n l d.
Proof.
  induction n; destruct l; intros; simpl; trivial. Qed.

Fixpoint my_delete_nth {A} (n:nat) (xs:list A) : list A :=
 match n with
  | 0%nat => match xs with
             | [] => []
             | _ :: ys => ys
             end
  | S n' => match xs with
            | [] => []
            | y :: ys => y :: my_delete_nth n' ys
            end
  end.

Lemma my_delete_nth_delete_nth {A}: forall n (l:list A), my_delete_nth n l = delete_nth n l.
Proof. induction n; destruct l; intros; simpl; trivial. Qed.

Fixpoint my_delete_list {A: Type} (ns: list nat) (xs: list A) : list A :=
 (* ns must already be sorted *)
 match ns with
 | nil => xs
 | n::ns' => my_delete_nth n (my_delete_list ns' xs)
 end.

Definition my_freezelist_nth (ns: list nat) (al: list mpred) : list mpred * list mpred :=
  (map (fun i => my_nth i al emp) ns,
   my_delete_list (SortNat.sort ns) al).

Lemma my_freezelist_nth_freezelist_nth: forall l al,
  my_freezelist_nth l al = freezelist_nth l al.
Proof. (*unfold my_freezelist_nth, freezelist_nth. *)
 intros. unfold my_freezelist_nth, freezelist_nth.
 f_equal.
  induction l; simpl; intros; trivial.
  f_equal; auto.
  clear.
  revert al; induction a; destruct al; simpl; auto. 
Qed.

(*Variant if l is monotonically decreasing
Fixpoint new_freezelist_nth (l: list nat) (al: list mpred): (list mpred) * (list mpred) :=
 match l with
 | nil => (nil,al)
 | (n::l') => let (xs, ys) := new_freezelist_nth l' (my_delete_nth n al)
              in (my_nth n al emp::xs, ys)
 end.*)

Lemma freeze_SEP'':
 forall l Espec {cs: compspecs} Delta P Q  R c Post xs ys,
  is_increasing (SortNat.sort l) (length R) = true ->
 (xs, ys) = my_freezelist_nth l R ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof. intros. rewrite my_freezelist_nth_freezelist_nth in H0.
  eapply freeze_SEP'; eassumption.  Qed.

Lemma freeze_SEP''entail:
 forall l Delta P Q  R Post xs ys,
  is_increasing (SortNat.sort l) (length R) = true ->
 (xs, ys) = my_freezelist_nth l R ->
 ENTAIL Delta, (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) |-- Post ->
 ENTAIL Delta, (PROPx P (LOCALx Q (SEPx R))) |-- Post.
Proof. intros. rewrite my_freezelist_nth_freezelist_nth in H0.
  eapply freeze_SEP'entail; eassumption.  Qed.

Ltac solve_is_increasing :=
  reflexivity ||
  match goal with |- is_increasing (SortNat.sort ?L) ?K = true =>
   let L' := eval compute in L in
   let K' := eval compute in K in
   (unify (is_increasing L' (S (List.fold_right Nat.max O L'))) false;
           fail 1 "Your freeze-list" L' "has repeated indexes") ||
    fail "Your freeze-list" L' "contains an index >= the number of SEP conjuncts, which is" K'
  end.

Ltac freeze_tac L name :=
  eapply (freeze_SEP'' (map Z.to_nat L)); 
   [solve_is_increasing | reflexivity 
   | match goal with
           | |- semax _ (PROPx _ (LOCALx _ (SEPx ((FRZL ?xs) :: my_delete_list ?A _)))) _ _ =>
           let D := fresh name in
           set (D:=xs);
           change xs with (@abbreviate (list mpred) xs) in D;
            let x := fresh "x" in 
            set (x:=A); compute in x; subst x;
             unfold my_delete_list, my_delete_nth
         end].

Ltac freeze_tac_entail L name :=
  eapply (freeze_SEP''entail (map Z.to_nat L)); 
   [solve_is_increasing | reflexivity 
   | match goal with
           | |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ((FRZL ?xs) :: my_delete_list ?A _)))) |-- _ =>
           let D := fresh name in
           set (D:=xs);
(*           hnf in D;*)
           change xs with (@abbreviate (list mpred) xs) in D;
            let x := fresh "x" in 
            set (x:=A); compute in x; subst x;
             unfold my_delete_list, my_delete_nth
         end].

Function Zlist_complement'  (i: Z) (n: nat) (bl: list Z) : list Z :=
 match n with O => nil
 | S n' =>
   match bl with
   | nil => i :: Zlist_complement' (Z.succ i) n' bl
   | b::bl' => if Z.ltb i b then i :: Zlist_complement' (Z.succ i) n' bl
                    else Zlist_complement' (Z.succ i) n' bl'
   end
 end.

Definition Zlist_complement (n: nat) (al: list Z) : list Z :=
  let bl := SortZ.sort al
  in Zlist_complement' 0 n bl.

(* Compute Zlist_complement 9 [4;5;3]. *)

Ltac find_freeze1 comp id A :=
lazymatch goal with
| fr := @abbreviate mpred _ |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  match R with context [fr :: ?R'] =>
    let L := constr:(Zlength R - (Z.succ (Zlength R'))) in
     let L := eval cbn in L in
      let A' := constr:(L::A) in
        unfold abbreviate in fr; subst fr; find_freeze1 comp id A'
   end
| |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ => 
            let A' := constr:(if comp then Zlist_complement (length R) A 
                                     else A) in
            let A' := eval compute in A' in
            freeze_tac A' id
| fr := @abbreviate mpred _ |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  match R with context [fr :: ?R'] =>
    let L := constr:(Zlength R - (Z.succ (Zlength R'))) in
     let L := eval cbn in L in
      let A' := constr:(L::A) in
        unfold abbreviate in fr; subst fr; find_freeze1 comp id A'
   end
| |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ => 
            let A' := constr:(if comp then Zlist_complement (length R) A 
                                     else A) in
            let A' := eval compute in A' in
            freeze_tac_entail A' id
end.

Ltac freezer i := find_freeze1  false i (@nil Z).
Ltac complement_freezer i := find_freeze1 true i (@nil Z).

Tactic Notation "freeze" constr(L) ident(i) :=
  freeze_tac L i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) :=
  freeze1 a1; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) :=
  freeze1 a1; freeze1 a2; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) :=
  freeze1 a1; freeze1 a2; freeze1 a3; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) :=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) :=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8) uconstr(a9):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; freeze1 a9; freezer i.
Tactic Notation "freeze" ident(i) ":=" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8) uconstr(a9) uconstr(a10):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; freeze1 a9; freeze1 a10; freezer i.

Tactic Notation "freeze" ident(i) ":=" "-"  :=
    complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) :=
  freeze1 a1; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) :=
  freeze1 a1; freeze1 a2; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) :=
  freeze1 a1; freeze1 a2; freeze1 a3; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) :=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) :=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8) uconstr(a9):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; freeze1 a9; complement_freezer i.
Tactic Notation "freeze" ident(i) ":=" "-" uconstr(a1) uconstr(a2) uconstr(a3) uconstr(a4) uconstr(a5) uconstr(a6) uconstr(a7) uconstr(a8) uconstr(a9) uconstr(a10):=
  freeze1 a1; freeze1 a2; freeze1 a3; freeze1 a4; freeze1 a5; freeze1 a6; freeze1 a7; freeze1 a8; freeze1 a9; freeze1 a10; complement_freezer i.

(****************************************************************************)

Lemma flatten_emp_in_mpreds' {A}:
  forall n (R: list mpred),
   nth_error R n = Some emp ->
   @SEPx A R = SEPx (firstn n R ++ skipn (S n) R).
Proof.
unfold SEPx. intros. extensionality rho.
revert R H. clear.
induction n; destruct R; intros.
+ inv H.
+ simpl nth_error in H. inv H. simpl. apply emp_sepcon.
+ reflexivity.
+ inv H.
  specialize (IHn _ H1). clear H1. simpl firstn.
  change (m :: firstn n R) with (app (m::nil) (firstn n R)).
  rewrite app_ass. unfold app at 1.
  simpl; f_equal; auto.
Qed.

Lemma flatten_emp_in_SEP':
  forall n P Q (R: list mpred) R',
   nth_error R n = Some emp ->
   R' = firstn n R ++ skipn (S n) R ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
f_equal. f_equal. subst R'.
 apply flatten_emp_in_mpreds'. trivial.
Qed.
(*
Ltac flatten_emp_in_mpreds RR :=
 match RR with
 | (SEPx (?R)) =>
   match R with context [emp :: ?R'] =>
      let n := constr:(length R - Datatypes.S (length R'))%nat in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(@flatten_emp_in_mpreds' n' R _ (eq_refl _));
      [ |
        let RR := fresh "RR" in set (RR := R);
        unfold firstn, app, skipn; subst RR; cbv beta iota;
        apply eq_refl
      ]
   end
 end.

Ltac flatten_emp :=
  match goal with
  | |- semax _ ?PQR _ _ => flatten_emp_in_SEP PQR
  | |-  ?PQR |-- _ => first [flatten_emp_in_SEP PQR |
                             flatten_emp_in_mpreds PQR ]
end.*)


Ltac flatten_emp_in_SEP PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [emp :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(@flatten_emp_in_SEP' n' P Q R _ (eq_refl _));
      [ |
        let RR := fresh "RR" in set (RR := R);
        unfold firstn, app, skipn; subst RR; cbv beta iota;
        apply eq_refl
      ]
   end
 end.

Ltac flatten_emp :=
  match goal with
  | |- semax _ ?PQR _ _ => flatten_emp_in_SEP PQR
  | |-  ?PQR |-- _ => flatten_emp_in_SEP PQR
end.

(*Thawing a freezer results in the sepcon product of the frozen items.*)

(*Tactic requires the resulting goal to be normalized manually.*)
Ltac thaw' name :=
  rewrite (FRZL_ax name); unfold name, abbreviate; clear name.

(*add simplification of the list operations inside the freezer,
   flatten the sepcon, and eliminate the emp term*)
Ltac thaw name :=
thaw' name;
let x := fresh "x" in let y := fresh "y" in let a := fresh "a" in 
lazymatch goal with
|  |- context [fold_right_sepcon (map ?F ?A)] =>
  set (x:= fold_right_sepcon (map F A));
  set (y := F) in *; 
  simpl in x
|  |- context [fold_right_sepcon ?A] =>
  set (x:= fold_right_sepcon A);
   unfold fold_right_sepcon in x
end;
pattern x;
match goal with |- ?A x => set (a:=A) end;
revert x;
rewrite <- ?sepcon_assoc, sepcon_emp;
intro x; subst a x; try subst y;
  unfold my_delete_list, my_delete_nth, my_nth, fold_right_sepcon;
  repeat flatten_sepcon_in_SEP; repeat flatten_emp.

(************************ Ramification ************************)

Inductive split_FRZ_in_SEP: list mpred -> list mpred -> list mpred -> Prop :=
| split_FRZ_in_SEP_nil: split_FRZ_in_SEP nil nil nil
| split_FRZ_in_SEP_FRZ: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZ F :: R) R' (FRZ F :: RF)
| split_FRZ_in_SEP_FRZL: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZL F :: R) R' (FRZL F :: RF)
| split_FRZ_in_SEP_FRZR: forall R R' RF L G w, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (@FRZR L G w :: R) R' (@FRZR L G w :: RF)
| split_FRZ_in_SEP_other: forall R R' RF R0, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (R0 :: R) (R0 :: R') RF.

Ltac prove_split_FRZ_in_SEP :=
  solve [
    repeat first
    [ simple apply split_FRZ_in_SEP_nil
    | simple apply split_FRZ_in_SEP_FRZ
    | simple apply split_FRZ_in_SEP_FRZL
    | simple apply split_FRZ_in_SEP_FRZR
    | simple apply split_FRZ_in_SEP_other]].

Lemma split_FRZ_in_SEP_spec: forall R R' RF,
  split_FRZ_in_SEP R R' RF ->
  fold_right_sepcon R = fold_right_sepcon R' * fold_right_sepcon RF.
Proof.
  intros.
  induction H.
  + simpl.
    rewrite sepcon_emp; auto.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
Qed.

Lemma localize: forall R_L Espec {cs: compspecs} Delta P Q R R_FR R_G c Post,
  split_FRZ_in_SEP R R_G R_FR ->
  (let FR_L := @abbreviate _ R_L in
   let FR_G := @abbreviate _ R_G in
   exists  (w: FRZRw FR_L FR_G),
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_L ++ @FRZR FR_L FR_G w :: R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  destruct H0 as [? ?].
  eapply semax_pre; [clear H0 | exact H0].
  apply split_FRZ_in_SEP_spec in H.
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  rewrite H.
  rewrite fold_right_sepcon_app.
  simpl.
  cancel.
  apply Freezer.FRZR1.
Qed.

Ltac unfold_app :=
change (@app mpred)
  with (fix app (l m : list mpred) {struct l} : list mpred :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
change (@app Prop)
  with (fix app (l m : list Prop) {struct l} : list Prop :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
cbv beta iota.

Ltac localize R_L :=
  eapply (localize R_L); [prove_split_FRZ_in_SEP |];
  let FR_L := fresh "RamL" in
  let FR_G := fresh "RamG" in
  intros FR_L FR_G;
  eexists;
  unfold_app.

Lemma unlocalize_aux: forall R_G2 R R_FR R_L1 R_G1 R_L2 F w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  F |-- fold_right_sepcon R_L2 -* fold_right_sepcon R_G2 ->
  fold_right_sepcon R |-- fold_right_sepcon (R_G2 ++ R_FR).
Proof.
  intros.
  apply split_FRZ_in_SEP_spec in H.
  rewrite H.
  rewrite fold_right_sepcon_app.
  simpl.
  cancel.
  destruct H0 as [? ?]; subst.
  apply Freezer.FRZR2.
  auto.
Qed.

Lemma unlocalize_triple: forall R_G2 Espec {cs: compspecs} Delta P Q R R_FR R_L1 R_G1 R_L2 c Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: fold_right_sepcon R_G1 |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre; [clear H1 | exact (H1 I)].
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalize_derives_canon: forall R_G2 Delta P Q R R_FR R_L1 R_G1 R_L2 Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR))) |-- Post) ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [clear H1 | exact (H1 I)].
  apply andp_derives; auto.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalize_derives_unlift: forall R_G2 Pre R R_FR R_L1 R_G1 R_L2 Post w,
  construct_fold_right_sepcon Pre R ->
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> fold_left_sepconx (R_G2 ++ R_FR) |-- Post) ->
  Pre |-- Post.
Proof.
  intros.
  apply construct_fold_right_sepcon_spec in H.
  subst Pre.
  eapply derives_trans; [clear H2 | exact (H2 I)].
  rewrite fold_left_sepconx_eq.
  eapply unlocalize_aux; eauto.
Qed.

Inductive ramif_frame_gen: mpred -> mpred -> Prop :=
| ramif_frame_gen_refl: forall P, ramif_frame_gen P P
| ramif_frame_gen_prop: forall (Pure: Prop) P Q, Pure -> ramif_frame_gen P (imp (prop Pure) Q) -> ramif_frame_gen P Q
| ramif_frame_gen_allp: forall {A: Type} (x: A) P Q, (forall x: A, ramif_frame_gen (P x) (Q x)) -> ramif_frame_gen (allp P) (Q x).

Ltac prove_ramif_frame_gen_rec wit :=
  match wit with
  | pair ?wit0 ?x =>
      prove_ramif_frame_gen_rec wit0;
      match goal with
      | |- ramif_frame_gen _ ?P => super_pattern P x
      end;
      apply (ramif_frame_gen_allp x);
      clear dependent x;
      intros x
  | _ =>
      match goal with
      | |- ramif_frame_gen _ ?P => super_pattern P wit
      end;
      apply (ramif_frame_gen_allp wit);
      clear dependent wit;
      intros wit
  end.

Ltac prove_ramif_frame_gen wit :=
  prove_ramif_frame_gen_rec wit;
  apply ramif_frame_gen_refl.

Ltac conj_gen assu :=
  match assu with
  | pair ?assu0 ?a => let r := conj_gen assu0 in constr:(conj r a)
  | _ => constr:(assu)
  end.

Ltac prove_ramif_frame_gen_prop assu :=
  let H := conj_gen assu in
  let Pure := type of H in
    apply (ramif_frame_gen_prop Pure _ _ H).

Lemma ramif_frame_gen_spec: forall P Q, ramif_frame_gen P Q -> P |-- Q.
Proof.
  intros.
  induction H.
  + apply derives_refl.
  + apply imp_andp_adjoint in IHramif_frame_gen.
    eapply derives_trans; [| apply IHramif_frame_gen].
    apply andp_right; auto.
    apply prop_right; auto.
  + apply (allp_left _ x).
    apply H0.
Qed.

Lemma unlocalizeQ_triple: forall R_G2 Espec {cs: compspecs} Delta P Q R R_FR R_L1 R_G1 R_L2 F c Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre; [clear H2 | exact (H2 I)].
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  apply ramif_frame_gen_spec in H0; auto.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalizeQ_derives_canon: forall R_G2 Delta P Q R R_FR R_L1 R_G1 R_L2 F Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR))) |-- Post) ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [clear H2 | exact (H2 I)].
  apply andp_derives; auto.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  apply ramif_frame_gen_spec in H0; auto.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalizeQ_derives_unlift: forall R_G2 Pre R R_FR R_L1 R_G1 R_L2 F Post w,
  construct_fold_right_sepcon Pre R ->
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> fold_left_sepconx (R_G2 ++ R_FR) |-- Post) ->
  Pre |-- Post.
Proof.
  intros.
  apply construct_fold_right_sepcon_spec in H.
  subst Pre.
  eapply derives_trans; [clear H3 | exact (H3 I)].
  apply ramif_frame_gen_spec in H1; auto.
  rewrite fold_left_sepconx_eq.
  eapply unlocalize_aux; eauto.
Qed.

Ltac unlocalize_plain R_G2 :=
  match goal with
  | |- @semax _ _ _ _ _ _ =>
          eapply (unlocalize_triple R_G2)
  | |- local (tc_environ _) && _ |-- _ =>
          eapply (unlocalize_derives_canon R_G2)
  | |- @derives _ Nveric _ _ =>
          eapply (unlocalize_derives_unlift R_G2); [construct_fold_right_sepcon | ..]
  end;
  [ prove_split_FRZ_in_SEP
  | refine (ex_intro _ _ eq_refl);
    match goal with
    | |- fold_right_sepcon ?R_G1 |-- sepcon (fold_right_sepcon ?R_L1) _ =>
           unfold abbreviate in R_L1, R_G1; unfold R_L1, R_G1; clear R_L1 R_G1
    end;
    rewrite <- !fold_left_sepconx_eq;
    unfold fold_left_sepconx
  | match goal with
    | |- _ ?R_L1 ?R_G1 -> _ =>
      intros _;
      clear R_L1 R_G1;
      unfold_app
    end;
    try unfold fold_left_sepconx
  ].

Ltac unlocalize_wit R_G2 wit tac :=
  match goal with
  | |- @semax _ _ _ _ _ _ =>
          eapply (unlocalizeQ_triple R_G2)
  | |- local (tc_environ _) && _ |-- _ =>
          eapply (unlocalizeQ_derives_canon R_G2)
  | |- @derives _ Nveric _ _ =>
          eapply (unlocalizeQ_derives_unlift R_G2); [construct_fold_right_sepcon | ..]
  end;
  [ prove_split_FRZ_in_SEP
  | rewrite <- !fold_right_sepconx_eq;
    unfold fold_right_sepconx;
    tac;
    prove_ramif_frame_gen wit
  | refine (ex_intro _ _ eq_refl);
    match goal with
    | |- fold_right_sepcon ?R_G1 |-- sepcon (fold_right_sepcon ?R_L1) _ =>
           unfold abbreviate in R_L1, R_G1; unfold R_L1, R_G1; clear R_L1 R_G1
    end;
    rewrite <- !fold_right_sepconx_eq;
    unfold fold_right_sepconx
  | match goal with
    | |- _ ?R_L1 ?R_G1 -> _ =>
      intros _;
      clear R_L1 R_G1;
      unfold_app
    end;
    try unfold fold_left_sepconx
  ].

Tactic Notation "unlocalize" constr(R_G2) :=
  unlocalize_plain R_G2.

Tactic Notation "unlocalize" constr(R_G2) "using" constr(wit) :=
  unlocalize_wit R_G2 wit idtac.

Tactic Notation "unlocalize" constr(R_G2) "using" constr(wit) "assuming" constr(assu) :=
  let tac := prove_ramif_frame_gen_prop assu in
  unlocalize_wit R_G2 wit tac.

Ltac thaw'' i :=
thaw' i;
let x := fresh "x" in let y := fresh "y" in let a := fresh "a" in 
match goal with |- context [fold_right_sepcon (map ?F ?A)] =>
  set (x:= fold_right_sepcon (map F A));
  set (y := F) in *; 
  simpl in x
end;
pattern x;
match goal with |- ?A x => set (a:=A) end;
revert x;
rewrite <- ?sepcon_assoc, sepcon_emp;
intro x; subst a x y;
  unfold my_delete_list, my_delete_nth, my_nth, fold_right_sepcon.

Ltac gather_SEP'' L :=
 gather_SEP' L;
 idtac "Warning: gather_SEP with numeric arguments is deprecated".

Tactic Notation "gather_SEP" uconstr(a) :=
  gather_SEP'' (a::nil) ||  (let i := fresh "i" in freeze i := a; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) :=
  gather_SEP'' (a::b::nil) ||  (let i := fresh "i" in freeze i := a b; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) :=
  gather_SEP'' (a::b::c::nil) ||  (let i := fresh "i" in freeze i := a b c; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) :=
  gather_SEP'' (a::b::c::d::nil) ||  (let i := fresh "i" in freeze i := a b c d; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) :=
  gather_SEP'' (a::b::c::d::e::nil) ||  (let i := fresh "i" in freeze i := a b c d e; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) :=
  gather_SEP'' (a::b::c::d::e::f::nil) ||  (let i := fresh "i" in freeze i := a b c d e f; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) :=
  gather_SEP'' (a::b::c::d::e::f::g::nil) ||  (let i := fresh "i" in freeze i := a b c d e f g; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) :=
  gather_SEP'' (a::b::c::d::e::f::g::h::nil) ||  (let i := fresh "i" in freeze i := a b c d e f g h; thaw'' i).

Tactic Notation "gather_SEP" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) uconstr(i0) :=
  gather_SEP'' (a::b::c::d::e::f::g::h::i0::nil) ||  (let i := fresh "i" in freeze i := a b c d e f g h i0; thaw'' i).

