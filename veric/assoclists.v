Require Import VST.veric.base.
Require Import VST.veric.initial_world.

Lemma filter_filter {A f1 f2}: forall {l:list A}, 
      filter f1 (filter f2 l) = filter (fun x => andb (f1 x) (f2 x)) l.
Proof.
  induction l; simpl; trivial.
  remember (f1 a) as b1; destruct b1; simpl. 
+ destruct (f2 a); simpl; [ rewrite <- Heqb1, IHl |]; trivial.
+  destruct (f2 a); simpl; [ rewrite <- Heqb1 |] ; trivial.
Qed.

Lemma filter_filter_comm {A f1 f2}: forall {l:list A}, 
      filter f1 (filter f2 l) = filter f2 (filter f1 l).
Proof.
  induction l; simpl; trivial.
  remember (f1 a) as b1; destruct b1; simpl. 
+ destruct (f2 a); simpl; [ rewrite <- Heqb1, IHl |]; trivial.
+  destruct (f2 a); simpl; [ rewrite <- Heqb1 |] ; trivial.
Qed.

Lemma app_inj_length {A}: forall {l1 l1' l2 l2'} (L:l1 ++ l2 = l1'++l2') (LEN: @length A l1 = length l1'),
      l1=l1' /\ l2=l2'.
Proof. 
  induction l1; simpl; intros.
  + destruct l1'; inv LEN. split; trivial.
  + destruct l1'; inv LEN; simpl in *. inv L.
    destruct (IHl1 _ _ _ H2 H0); subst. split; trivial.
Qed.

Lemma filter_app {A f}: forall {l1 l2: list A}, filter f (l1++l2) = filter f l1 ++ filter f l2.
Proof. induction l1; simpl; intros. trivial. rewrite IHl1. destruct (f a); trivial. Qed.

Lemma id_in_list_app {i l1 l2}: id_in_list i (l1++l2) = orb (id_in_list i l1) (id_in_list i l2).
Proof. induction l1; simpl; [ trivial | rewrite IHl1, orb_assoc; trivial]. Qed. 

Lemma find_id_None_iff {A} i: forall (l:list (ident * A)), find_id i l = None <-> ~ In i (map fst l).
Proof.
  induction l; simpl.
+ split; intros; auto.
+ destruct a as [i' a]; simpl. 
  destruct (eq_dec i i'); subst; split; intros; [ inv H | | |]; intuition.
Qed.

Lemma find_id_filter_char {A f}: forall l (L: list_norepet (map fst l)) i,
  find_id i (filter f l) = match @find_id A i l with
                           Some x => if f (i,x) then Some x else None
                         | None => None
                         end.
Proof.
  induction l; simpl. trivial.
  intros. destruct a as [j a]. simpl in L; inv L.
  remember (f (j,a)) as d; destruct d; simpl.
  + if_tac; [ subst; rewrite <- Heqd; trivial | auto].
  + specialize (IHl H2). apply find_id_None_iff in H1.
    if_tac; [ subst; rewrite <- Heqd, IHl, H1; trivial | auto].
Qed. 

Lemma find_id_filter_Some {A f i l} {a:A}: find_id i (filter f l) = Some a -> 
      list_norepet (map fst l) -> find_id i l = Some a /\ f (i,a) = true.
Proof. 
  intros. rewrite find_id_filter_char in H; trivial.
  destruct (find_id i l) as [b |]; [ | discriminate].
  remember (f (i, b)) as c; destruct c; [ inv H; rewrite Heqc; split; trivial | discriminate] .
Qed.

Lemma find_id_in_split {A i} {a:A}: forall {l} (Hi: find_id i l = Some a) (LNR: list_norepet (map fst l)),
  exists l1 l2, l=l1++(i,a)::l2 /\ find_id i l1 = None /\ find_id i l2=None.
Proof.
  induction l; simpl; intros. inv Hi. inv LNR; destruct a0 as [j b]; simpl in *.
  if_tac in Hi; [inv Hi |].
+ exists nil, l. split3; trivial. apply find_id_None_iff; trivial.
+ destruct (IHl Hi H2) as [l1 [l2 [Ha [L1 L2]]]]; clear IHl; subst.
  exists ((j, b) :: l1), l2; split3; trivial; simpl.
  rewrite if_false; trivial.
Qed.

Lemma id_in_list_false_i i l: ~ In i l -> id_in_list i l = false.
Proof.
  induction l; simpl; intros; trivial.
  remember (Pos.eqb i a) as b; symmetry in Heqb; destruct b; simpl.
  + apply Peqb_true_eq in Heqb; subst. elim H; left; trivial. 
  + apply IHl. intros N. apply H; right; trivial.
Qed.

Lemma id_in_list_true_i i l: In i l -> id_in_list i l = true.
Proof.
  induction l; simpl; intros. contradiction.
  destruct H; subst.
  + remember (Pos.eqb i i) as b; destruct b; simpl. trivial.
    symmetry in Heqb. apply Pos.eqb_neq in Heqb. congruence. 
  + rewrite (IHl H), orb_true_r; trivial. 
Qed.


Lemma find_id_cons_char {A} l i (a:ident*A): find_id i (a::l) = if ident_eq i (fst a) then Some(snd a) else find_id i l.
Proof. destruct a; reflexivity. Qed.

Lemma In_map_fst_find_id {A i l} (Hi: In i (map fst l)) (L:list_norepet (map fst l)): exists a:A, find_id i l = Some a.
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[j a] [J Ha]]. simpl in J; subst. 
  apply find_id_i in Ha. exists a; trivial. trivial.
Qed.


Lemma list_norepet_map_fst_filter {A f}: forall (l: list (ident * A)),
 list_norepet (map fst l) ->
 list_norepet (map fst (filter f l)).
Proof.
  induction l; simpl; intros; trivial. inv H. specialize (IHl H3).
  remember (f a) as q; destruct q; trivial. simpl.
  constructor; trivial. intros N; apply H2; clear H2.
  destruct a as [i a]; simpl in *.
  apply list_in_map_inv in N. destruct N as [x [X F]]; subst.
  destruct x as [j x]; simpl in *.
  apply filter_In in F. destruct F. apply (in_map fst) in H. apply H.
Qed.

Lemma find_id_app_char {A}: forall l1 l2 i,
  find_id i (l1 ++ l2) = match @find_id A i l1 with
                           Some x => Some x
                         | None => find_id i l2
                         end.
Proof.
  induction l1; simpl. trivial.
  intros. destruct a as [j a].
  if_tac. trivial. auto.
Qed.

Lemma list_disjoint_map_fst_find_id1 {A B l1 l2} (D: list_disjoint (map fst l1) (map fst l2)) i a:
      @find_id A i l1 = Some a -> @find_id B i l2 = None.
Proof.
  intros. remember (find_id i l2) as q; destruct q; [symmetry in Heqq | trivial].
  apply find_id_e in H. apply (in_map fst) in H.
  apply find_id_e in Heqq. apply (in_map fst) in Heqq.
  elim (D i i); trivial.
Qed.

Lemma list_disjoint_map_fst_find_id2 {A B l1 l2} (D: list_disjoint (map fst l1) (map fst l2)) i a:
      @find_id A i l2 = Some a -> @find_id B i l1 = None.
Proof.
  intros. apply list_disjoint_sym in D. eapply list_disjoint_map_fst_find_id1; eassumption. 
Qed.

Lemma list_norepet_find_id_app_exclusive1 {A B} {l1 : list (ident *A)} {l2:list (ident * B)} 
      (LNR: list_norepet (map fst l1 ++ map fst l2)) {i a} (Hi: find_id i l1 = Some a): find_id i l2 = None.
Proof. clear - LNR Hi.
  apply find_id_None_iff; intros N. apply find_id_In_map_fst in Hi.
  apply list_norepet_app in LNR. destruct LNR as [_ [_ D]]. apply (D i i); trivial.
Qed.

Lemma list_norepet_find_id_app_exclusive2 {A B} {l1 : list (ident *A)} {l2:list (ident * B)} 
      (LNR: list_norepet (map fst l1 ++ map fst l2)) {i b} (Hi: find_id i l2 = Some b): find_id i l1 = None.
Proof. clear - LNR Hi.
  apply find_id_None_iff; intros N. apply find_id_In_map_fst in Hi.
  apply list_norepet_app in LNR. destruct LNR as [_ [_ D]]. apply (D i i); trivial.
Qed.

Lemma id_in_list_map_filter {A f i} {l:list (ident *A)} (Hi:id_in_list i (map fst l) = false):
      id_in_list i (map fst (filter f l)) = false.
Proof.
  apply id_in_list_false in Hi. apply id_in_list_false_i. intros N; apply Hi; clear Hi.
  apply list_in_map_inv in N. destruct N as [[j fd] [HI F]]; simpl in HI; subst.
  apply filter_In in F. destruct F as [F _]. apply (in_map fst) in F; apply F.
Qed.

Lemma negb_ident_eq_symm j i: negb (ident_eq j i) = negb (ident_eq i j).
Proof.
  destruct (ident_eq j i); subst; simpl.
+ destruct (ident_eq i i); subst; simpl; trivial. congruence.
+ destruct (ident_eq i j); subst; simpl; trivial. congruence.
Qed.


Lemma sublist_map_fst {A B} {f:A->B}: forall l k, sublist l k -> sublist (map f l) (map f k).
Proof.
  induction l; simpl; intros. inv H; simpl; constructor.
  + induction l2; simpl. constructor. inv H0. constructor. auto.
  + induction k.
    - inv H; simpl; constructor.
    - inv H; simpl; constructor; auto.
Qed.

Lemma sublist_nil_l {A}: forall (l:list A), sublist nil l.
Proof. induction l; constructor; trivial. Qed.

Lemma sublist_filter {A f}: forall l:list A, sublist (filter f l) l.
Proof.
  intros. remember (filter f l) as fl. generalize dependent l.
  induction fl; simpl; intros; try constructor.
  + apply sublist_nil_l.
  + induction l; simpl in Heqfl. congruence.
    destruct (f a0).
    - inv Heqfl. constructor. auto.
    - constructor. auto.
Qed.

Lemma list_disjoint_sublist {A}: forall l1 k1, sublist k1 l1 -> forall l2 k2, sublist k2 l2 -> @list_disjoint A l1 l2 -> list_disjoint k1 k2.
Proof.
  intros. intros ? ? ? ? ?; subst. 
  specialize (sublist_In _ _ _ H H2); intros.
  specialize (sublist_In _ _ _ H0 H3); intros.
  apply (H1 y y); trivial.
Qed.

Lemma sublist_refl {A}: forall (l:list A), sublist l l.
Proof. induction l; constructor; trivial. Qed.

Lemma list_disjoint_mono {A} (l1 l1' l2 l2': list A) (L: list_disjoint l1' l2')
      (H1: forall x, In x l2 -> In x l2') (H2: forall x, In x l1 -> In x l1'):
      list_disjoint l1 l2.
Proof. do 4 intros ?; subst. apply (L x y); eauto. Qed. 

Lemma list_disjoint_app_L {A} (l1 l2 l: list A)
      (L1: list_disjoint l1 l) (L2: list_disjoint l2 l): list_disjoint (l1++l2) l.
Proof.
  do 4 intros ?. apply in_app_or in H; destruct H.
  apply (L1 x y); trivial. apply (L2 x y); trivial.
Qed.

Lemma list_disjoint_app_R {A} (l l2 l3: list A)
      (L2: list_disjoint l l2) (L3: list_disjoint l l3): list_disjoint l (l2++l3).
Proof.
  apply list_disjoint_sym. apply list_disjoint_sym in L2. apply list_disjoint_sym in L3.
  apply list_disjoint_app_L; trivial. 
Qed.

Lemma sublist_trans {A}: forall {l3 l2:list A} (L23: sublist l2 l3) l1 (L12: sublist l1 l2),
      sublist l1 l3.
Proof.
 intros l3 l2 L23. induction L23.
+ trivial.
+ intros. inv L12; constructor; auto.
+ rename l2 into l3. rename l1 into l2. intros l1 L12.
  apply IHL23 in L12. constructor; trivial.
Qed.

Lemma sublist_app {A}: forall {l l1 l2:list A} (L: sublist l1 l2), sublist (l++l1) (l++l2).
Proof. induction l; simpl; intros; [trivial | constructor; auto]. Qed.

Lemma sublist_app_R1 {A}: forall {l l':list A}, sublist l (l++l').
Proof. induction l; simpl; intros; [ apply sublist_nil_l | constructor; auto]. Qed.

Lemma sublist_app_R2 {A}: forall {l l':list A}, sublist l' (l++l').
Proof. induction l; simpl; intros; [ apply sublist_refl | constructor; auto]. Qed.

Lemma sublist_snoc {A}: forall l l' (L : sublist l l') (a:A), 
      sublist (l ++ a :: nil) (l' ++ a :: nil).
Proof.
  intros l l' L.
  induction L.
+ simpl; intros. constructor. constructor.
+ simpl; intros. constructor. auto.
+ simpl; intros. eapply sublist_trans. 2: apply (IHL a0).
  constructor; apply sublist_refl.
Qed.

Lemma sublist_snoc_R {A}: forall l l' (L : sublist l l') (a:A), 
      sublist l (l' ++ a :: nil).
Proof.
  intros l l' L.
  induction L; simpl; intros; [ apply sublist_nil_l | | ]; constructor; auto.
Qed.

Lemma sublist_app_split {A}: forall {l2 l2':list A} (L2: sublist l2 l2') {l1 l1'}
      (L1: sublist l1 l1'), sublist (l1++l2) (l1'++l2').
Proof. 
  intros l2 l2' L2. induction L2. 
+ intros. rewrite 2 app_nil_r; trivial.
+ rename l2 into l2'. rename l1 into l2. intros.
  specialize (IHL2 (l1 ++ (cons a nil)) (l1' ++ (cons a nil))).
  do 2 rewrite <- app_assoc in IHL2. apply IHL2; clear IHL2.
  apply sublist_snoc; trivial.
+ rename l2 into l2'. rename l1 into l2. intros.
  specialize (IHL2 l1 (l1' ++ (cons a nil))).
  rewrite <- app_assoc in IHL2. apply IHL2; clear IHL2.
  apply sublist_snoc_R; trivial.
Qed.

Lemma sublist_app_right1 {A}: forall {l1 l l2: list A}, sublist l l2 -> sublist l (l1 ++ l2).
Proof.
  induction l1; simpl; intros. trivial.
  constructor. auto.
Qed.

Lemma sublist_app_right2 {A} {l2 l l1: list A} (L:sublist l l1): sublist l (l1 ++ l2).
Proof. eapply sublist_trans. apply sublist_app_R1. eassumption. Qed.

Lemma sublist_filter_true {A f}: forall {l k: list A}, sublist l k -> 
      (forall x, In x l -> f x = true) -> sublist l (filter f k).
Proof.
  intros. induction H; simpl. apply sublist_nil_l.
  rewrite (H0 a). constructor. apply IHsublist. intros. apply H0; right; trivial. left; trivial.
  destruct (f a). constructor; auto. auto.
Qed.

Lemma find_id_filter_None_I {A} f (l:list(ident *A)) i: find_id i l = None -> list_norepet (map fst l) -> find_id i (filter f l) = None.
Proof. intros. rewrite find_id_filter_char, H; trivial. Qed. 

Lemma filter_fg {A f g} (l: list A) (FG: forall x, In x l -> f x = g x): filter f l = filter g l.
Proof. induction l; simpl; trivial. rewrite IHl, FG. trivial. left; trivial. intros. apply FG. right; trivial. Qed.
