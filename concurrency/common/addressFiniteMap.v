Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.OrderedType.

Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.

Require Import VST.msl.eq_dec.
Require Import VST.msl.Coqlib2.
(* Require Import VST.sepcomp.semantics_lemmas. *)
Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.lksize.
Set Bullet Behavior "Strict Subproofs".

  Module MiniAddressOrdered <: MiniOrderedType.

    Definition t:= address.
    Definition eq:= @eq t.
    Definition lt' (x y:t): bool :=
      (match x, y with (x1,x2),(y1,y2) =>
        if peq x1 y1 then zlt x2 y2 else plt x1 y1
      end).
    Definition lt x y:= is_true (lt' x y).

    Lemma eq_refl : forall x : t, eq x x. Proof. reflexivity. Qed.
    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. intros; symmetry; assumption. Qed.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros. rewrite H, H0; reflexivity. Qed.
    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof. intros x y z; destruct x, y, z.
           unfold lt; simpl.
           destruct (peq b b0), (peq b0 b1), (peq b b1),
           (plt b b0), (plt b0 b1), (plt b b1),
           (zlt z0 z1), (zlt z1 z), (zlt z0 z); subst;
             simpl; intros; auto; try omega; (*Solves most*)
             exfalso;
           (* solves al Plt x y /\ Plt y x *)
           try match goal with
             [H1:Plt ?x ?y, H2:Plt ?y ?x |- _ ]=>
             pose (Plt_trans x y x H1 H2)
               end;
           (* solves Plt x x*)
           try match goal with
             [H1:Plt ?x ?x  |- _ ]=>
             apply (Plt_strict x); assumption
               end;
           (* solves al Plt x y /\ Plt y z /\ ~ Plt x z *)
           match goal with
             [H1:Plt ?x ?y, H2:Plt ?y ?z |- _ ]=>
             pose (Plt_trans x y z H1 H2)
           end; auto.
    Qed.
    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof. unfold lt, lt'.
           destruct x, y.
           unfold not; intros.
           inversion H0; subst.
           rewrite peq_true in H.
           assert (HH: z0 >= z0) by omega.
           destruct zlt as [a|b]; auto.
    Qed.
   Lemma compare : forall x y : t, Compare lt eq x y.
          destruct x as [x1 x2].
          destruct y as [y1 y2].
          destruct (peq x1 y1) eqn:H0.
          - destruct (Z_dec x2 y2) eqn:H1; [destruct s|].
            + constructor 1.
              unfold lt, lt'.
              rewrite H0; simpl.
              unfold is_true.
              destruct (zlt x2 y2); auto; omega.
            + constructor 3.
              unfold lt, lt'.
              destruct (peq x1 y1); try solve[inversion H0]; subst.
              destruct (peq y1 y1); simpl. clear e e0 H0.
              destruct (zlt y2 x2); auto; omega.
              destruct (zlt x2 y2); auto; omega.
            + constructor 2.
              subst; reflexivity.
          - destruct (plt x1 y1).
            + constructor 1.
              unfold lt, lt'; rewrite H0; simpl.
              destruct (plt x1 y1); auto.
            + constructor 3.
              unfold lt, lt'.
              destruct (peq x1 y1); try solve[inversion H0]; subst.
              destruct (peq y1 x1); simpl.
              exfalso; apply n; symmetry; assumption.
              destruct (plt y1 x1); auto.
              unfold Plt in *.
              destruct (x1 <? y1)%positive eqn:AAA.
              apply Pos.ltb_lt in AAA. auto.
              apply Pos.ltb_ge in AAA.
              apply Pos.le_lteq in AAA; destruct AAA; auto.
   Qed.
  End MiniAddressOrdered.


  Module AddressOrdered <: OrderedType.
     Include MiniAddressOrdered.

     Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
     Proof. unfold eq; destruct x, y. simpl.
            destruct (peq b b0);
              destruct (zeq z z0); subst; try solve[left; reflexivity];
              right; unfold not; intros H; inversion H; apply n; auto.
     Qed.
  End AddressOrdered.


  (*This is my map!*)
  Require Import FMaps.
  Module AMap:= Make AddressOrdered.


  Section AMap2PMap.
    (*Need to build a permission map from a finite map*)
    (*The pmap is used in the compcert memory. *)
    Context {lock_info: Type}.
    Variable am: AMap.t lock_info.



    Definition A2PMap (*: Map.PMap*) :=
      fold_left
        (fun (pmap:access_map) (a:address * lock_info)=>
           match a with
           | ((b, ofs), _) => setPermBlock (Some Memtype.Writable) b ofs pmap LKSIZE_nat
           end)
        (AMap.elements am)
        (PMap.init (fun _ => None)).
    End AMap2PMap.

Lemma AMap_find_map {A B} m (f : A -> B) k (x : A) :
  AMap.find k m = Some x ->
  AMap.find k (AMap.map f m) = Some (f x).
Proof.
  destruct m as [l sorted].
  unfold AMap.Raw.t, AMap.find in *.
  simpl.
  clear sorted.
  induction l as [| [addr a] l IHl]; simpl.
  - intro. discriminate.
  - destruct (AddressOrdered.compare k addr); intros E.
    + discriminate.
    + injection E as <-. eauto.
    + eauto.
Qed.

Lemma AMap_find_map_None {A B} m (f : A -> B) k :
  AMap.find k m = None ->
  AMap.find k (AMap.map f m) = None.
Proof.
  destruct m as [l sorted].
  unfold AMap.Raw.t, AMap.find in *.
  simpl.
  clear sorted.
  induction l as [| [addr a] l IHl]; simpl.
  - auto.
  - destruct (AddressOrdered.compare k addr); intros E; auto.
    discriminate.
Qed.

Lemma AMap_find_map_inv {A B} m (f : A -> B) k (y : B) :
  AMap.find k (AMap.map f m) = Some y ->
  exists x,
    AMap.find k m = Some x /\
    y = f x.
Proof.
  destruct m as [l sorted].
  unfold AMap.Raw.t, AMap.find in *.
  simpl.
  clear sorted.
  induction l as [| [addr a] l IHl]; simpl.
  - intro. discriminate.
  - destruct (AddressOrdered.compare k addr); intros E.
    + discriminate.
    + injection E as <-. eauto.
    + eauto.
Qed.

Lemma AMap_map {A B} (f : A -> B) m :
  map snd (AMap.elements (AMap.map f m)) =
  map f (map snd (AMap.elements m)).
Proof.
  destruct m as [l sorted].
  unfold AMap.Raw.t, AMap.find in *.
  simpl.
  clear sorted.
  induction l as [| [addr a] l IHl]; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma AMap_find_map_option_map {A B} m (f : A -> B) k :
  AMap.find k (AMap.map f m) =
  option_map f (AMap.find k m).
Proof.
  destruct (AMap.find k m) eqn:E.
  - apply AMap_find_map, E.
  - apply AMap_find_map_None, E.
Qed.

Instance EqDec_AMap_key : EqDec AMap.key.
Proof.
  compute.
  change (forall a a' : positive * Z, {a = a'} + {a <> a'}).
  repeat decide equality.
Qed.

Lemma AMap_find_add {A} m x (y : A) x' :
  AMap.find x' (AMap.add x y m) =
  if eq_dec x x' then Some y else AMap.find x' m.
Proof.
  pose proof AMap.add_1.
  pose proof AMap.add_2.
  pose proof AMap.add_3.
  pose proof AMap.find_1.
  pose proof AMap.find_2.
  assert (SN : forall A, forall o : option A, (forall x, o <> Some x) <-> o = None).
  { intros ? []; split; congruence. }

  destruct (eq_dec x x') as [d|d].
  - eauto.
  - destruct (AMap.find (elt:=A) x' m) eqn:E.
    + eauto.
    + rewrite <-SN in E |- *.
      intros y' Ey'; eapply E.
      eauto.
Qed.

Lemma AMap_find_remove {A} (m : AMap.t A) x x' :
  AMap.find x' (AMap.remove x m) =
  if eq_dec x x' then None else AMap.find x' m.
Proof.
  pose proof AMap.add_1.
  pose proof AMap.add_2.
  pose proof AMap.add_3.
  pose proof AMap.find_1.
  pose proof AMap.find_2.
  pose proof AMap.remove_1.
  pose proof AMap.remove_2.
  pose proof AMap.remove_3.
  assert (SN : forall A, forall o : option A, (forall x, o <> Some x) <-> o = None).
  { intros ? []; split; congruence. }

  destruct (eq_dec x x') as [d|d].
  - destruct (AMap.find _ _) as [o|] eqn:Eo; auto; exfalso.
    apply AMap.find_2 in Eo.
    eapply H4; eauto.
    exists o. apply Eo.
  - destruct (AMap.find (elt:=A) x' m) eqn:E.
    + eauto.
    + rewrite <-SN in E |- *.
      intros y' Ey'; eapply E.
      eauto.
Qed.

Lemma AMap_Raw_map_app {A} (f : A -> A) l1 l2 :
  AMap.Raw.map (option_map f) (app l1 l2) =
  app (AMap.Raw.map (option_map f) l1)
      (AMap.Raw.map (option_map f) l2).
Proof.
  induction l1; simpl; auto.
  rewrite IHl1. destruct a; auto.
Qed.

Lemma AMap_Raw_map_rev {A} (f : A -> A) l :
  AMap.Raw.map (option_map f) (rev l) =
  rev (AMap.Raw.map (option_map f) l).
Proof.
  induction l; simpl; auto.
  rewrite AMap_Raw_map_app. simpl. destruct a.
  rewrite IHl. auto.
Qed.

Lemma A2PMap_option_map {A} (m : AMap.t (option A)) (f : A -> A) :
  A2PMap (AMap.map (option_map f) m) = A2PMap m.
Proof.
  destruct m as [l sorted].
  unfold A2PMap in *.
  do 2 rewrite <-fold_left_rev_right.
  unfold AMap.elements in *.
  unfold AMap.map in *.
  unfold AMap.Raw.elements in *.
  simpl AMap.this.
  clear sorted.
  unfold AMap.Raw.t in *.
  rewrite <-AMap_Raw_map_rev.
  induction (rev l). reflexivity.
  simpl in *. rewrite <-IHl0.
  destruct a. reflexivity.
Qed.

Lemma AMap_map_add {A B} (f : A -> B) m x y :
  AMap.Equal
    (AMap.map f (AMap.add x y m))
    (AMap.add x (f y) (AMap.map f m)).
Proof.
  intros k.
  rewrite AMap_find_map_option_map.
  rewrite AMap_find_add.
  rewrite AMap_find_add.
  rewrite AMap_find_map_option_map.
  destruct (AMap.find (elt:=A) k m); destruct (eq_dec x k); auto.
Qed.

Lemma AMap_Raw_add_fold_left A (EQ : A -> A -> Prop) B f k (x : B) l (e : A) :
  (forall e, EQ e e) ->
  (forall e e', EQ e e' -> EQ e' e) ->
  (forall e e' e'', EQ e e' -> EQ e' e'' -> EQ e e'') ->
  (forall a e e', EQ e e' -> EQ (f e a) (f e' a)) ->
  (forall a b e, fst a = fst b -> EQ (f (f e a) b) (f e a)) ->
  (forall a b e, EQ (f (f e a) b) (f (f e b) a)) ->
  EQ
    (fold_left f (AMap.Raw.add k x l) e)
    (fold_left f ((k, x) :: l) e).
Proof.
  intros re sy tr congr idem comm.
  assert (congr' : forall l e e', EQ e e' -> EQ (fold_left f l e) (fold_left f l e')). {
    clear -congr; intros l; induction l; intros e e' E.
    - apply E.
    - apply IHl, congr, E.
  }
  revert e. induction l; intros e. apply re. simpl.
  destruct a as (k', y).
  destruct (AddressOrdered.compare k k').
  - apply re.
  - simpl. apply congr'. apply sy. apply idem. assumption.
  - simpl. eapply tr. apply IHl. simpl. apply congr'. apply comm.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma AMap_Raw_add_fold_left_permut A (EQ : A -> A -> Prop) B f (l l' : list B) (e : A) :
  (forall e, EQ e e) ->
  (forall e e', EQ e e' -> EQ e' e) ->
  (forall e e' e'', EQ e e' -> EQ e' e'' -> EQ e e'') ->
  (forall a e e', EQ e e' -> EQ (f e a) (f e' a)) ->
  (forall a b e, EQ (f (f e a) b) (f (f e b) a)) ->
  Permutation l l' ->
  EQ
    (fold_left f l e)
    (fold_left f l' e).
Proof.
  intros re sy tr congr comm permut.
  assert (congr' : forall l e e', EQ e e' -> EQ (fold_left f l e) (fold_left f l e')). {
    clear -congr; intros l; induction l; intros e e' E.
    - apply E.
    - apply IHl, congr, E.
  }
  revert e. induction permut; intros e.
  - apply re.
  - apply IHpermut.
  - simpl. eapply tr. apply congr'. 2:apply re. apply comm.
  - eapply tr. apply IHpermut1. apply IHpermut2.
Qed.

Lemma AMap_Raw_add_fold_left_right A (EQ : A -> A -> Prop) B f (l : list B) (e : A) :
  (forall e, EQ e e) ->
  (forall e e', EQ e e' -> EQ e' e) ->
  (forall e e' e'', EQ e e' -> EQ e' e'' -> EQ e e'') ->
  (forall a e e', EQ e e' -> EQ (f e a) (f e' a)) ->
  (forall a b e, EQ (f (f e a) b) (f (f e b) a)) ->
  EQ
    (fold_left f l e)
    (fold_right (fun x y => f y x) e l).
Proof.
  intros re sy tr congr comm.
  replace l with (rev (rev l)) at 2. 2:apply rev_involutive.
  rewrite fold_left_rev_right.
  apply AMap_Raw_add_fold_left_permut; auto.
  apply Permutation_rev.
Qed.

Lemma setPerm_b_comm o b ofs1 ofs2 t :
  setPerm o b ofs1 (setPerm o b ofs2 t) =
  setPerm o b ofs2 (setPerm o b ofs1 t).
Proof.
  unfold setPerm. do 2 rewrite PMap.set2. f_equal.
  extensionality z. do 2 rewrite PMap.gsspec.
  destruct (zeq ofs1 z); destruct (zeq ofs2 z); simpl.
  - auto.
  - if_tac. 2:tauto. destruct (zeq ofs1 z); simpl; auto. tauto.
  - if_tac. 2:tauto. destruct (zeq ofs2 z); simpl; auto. tauto.
  - if_tac. 2:tauto. destruct (zeq ofs2 z); simpl; auto. tauto.
    destruct (zeq ofs1 z); simpl; auto. tauto.
Qed.

Lemma setPerm_b_idem o b ofs t :
  setPerm o b ofs (setPerm o b ofs t) =
  setPerm o b ofs t.
Proof.
  unfold setPerm. rewrite PMap.set2. f_equal.
  extensionality z. rewrite PMap.gsspec.
  destruct (zeq ofs z); simpl; auto. if_tac. 2:tauto. destruct (zeq ofs z); auto. tauto.
Qed.

Definition PMap_eq {A} (m m' : PMap.t (Z -> A)) := forall b' ofs', m !! b' ofs' = m' !! b' ofs'.

Lemma PMap_eq_refl {A} : reflexive _ (@PMap_eq A). intros f g. reflexivity. Qed.
Lemma PMap_eq_sym {A} : symmetric _ (@PMap_eq A). intros f g. unfold PMap_eq; symmetry; auto. Qed.
Lemma PMap_eq_trans {A} : transitive _ (@PMap_eq A). intros ? ? ? E E' ? ?. rewrite E, E'. auto. Qed.

Definition A2P {A} :=
 (fun (pmap : access_map) (a : address * A) =>
      let (a0, _) := a in let (b0, ofs0) := a0 in setPermBlock (Some Writable) b0 ofs0 pmap LKSIZE_nat).

Lemma setPermBlock_lookup : forall p b o a n b' o', (setPermBlock p b o a n) !! b' o' =
  if adr_range_dec (b, o) (Z.of_nat n) (b', o') then p else a !! b' o'.
Proof.
  intros; if_tac; simpl in H.
  - destruct H; subst; apply setPermBlock_same; auto.
  - destruct (peq b b'); [|apply setPermBlock_other_2; auto].
    subst; destruct (zle o o'); [|apply setPermBlock_other_1; omega].
    destruct (zlt o' (o + Z.of_nat n)); [tauto | apply setPermBlock_other_1; omega].
Qed.

Lemma A2P_congr A e e' a : PMap_eq e e' -> PMap_eq (A2P e a) (@A2P A e' a).
Proof.
  destruct a as ((b_, ofs_), a). intros E b'' ofs''. simpl.
  rewrite !setPermBlock_lookup; if_tac; auto.
Qed.

Lemma A2P_overwrite A : forall a b e, fst a = fst b -> PMap_eq (@A2P A (A2P e a) b) (@A2P A e a).
Proof.
  intros ((b1, ofs1), x1) (k2, x2) e; simpl. intros <- b'' ofs''.
  rewrite !setPermBlock_lookup; if_tac; auto.
Qed.

Lemma setPerm_comm b1 o1 b2 o2 e:
  PMap_eq (setPerm (Some Writable) b1 o1 (setPerm (Some Writable) b2 o2 e))
          (setPerm (Some Writable) b2 o2 (setPerm (Some Writable) b1 o1 e)).
Proof.
  intros b' o'.
  unfold setPerm in *.
  repeat rewrite PMap.gsspec.
  destruct (peq b1 b2) as [B|B];
  destruct (peq b2 b1) as [B'|B']; try tauto;
  destruct (peq b' b1) as [B1|B1];
  destruct (peq b' b2) as [B2|B2];
  destruct (zeq o1 o') as [O1|O1];
  destruct (zeq o2 o') as [O2|O2]; simpl; auto; congruence.
Qed.

Lemma setPerm_congr b o e e':
  PMap_eq e e' ->
  PMap_eq (setPerm (Some Writable) b o e)
          (setPerm (Some Writable) b o e').
Proof.
  intros E b' o'; simpl.
  unfold setPerm in *.
  repeat rewrite PMap.gsspec.
  if_tac; destruct (zeq o o'); simpl. auto.
  all: rewrite E; auto.
Qed.

Lemma A2P_comm A e a b : PMap_eq (@A2P A (A2P e a) b) (@A2P A (A2P e b) a).
Proof.
  destruct a as ((b1, o1), a1), b as ((b2, o2), a2); simpl.
  intros ??.
  rewrite !setPermBlock_lookup; if_tac; if_tac; auto.
Qed.

Lemma fold_right_cons : forall A B (f : A -> B -> B) (z : B) (x : A) (y : list A),
    fold_right f z (x :: y) = f x (fold_right f z y).
Proof. reflexivity. Qed.

Lemma setPerm_spec perm m b ofs b' ofs' :
  (setPerm perm b ofs m) !! b' ofs' =
  if eq_dec (b, ofs) (b', ofs') then
    perm
  else
    m !! b' ofs'.
Proof.
  unfold setPerm. rewrite PMap.gsspec.
  if_tac; destruct (zeq ofs ofs'); simpl; if_tac [?|ne]; try congruence.
  destruct ne; auto.
Qed.

Lemma A2PMap_found A m b ofs ofs' o :
  AMap.find (elt:=A) (b, ofs) m = Some o ->
  (ofs <= ofs' < ofs + LKSIZE)%Z ->
  (A2PMap m) !! b ofs' = Some Writable.
Proof.
  unfold AMap.find, A2PMap, AMap.elements, AMap.Raw.elements.
  rewrite (AMap_Raw_add_fold_left_right (PMap.t (Z -> option permission)) PMap_eq).
  2: now apply PMap_eq_refl.
  2: now apply PMap_eq_sym.
  2: now apply PMap_eq_trans.
  2: now intros; eapply A2P_congr; auto.
  2: now intros; eapply A2P_comm; auto.

  induction (@AMap.this A m) as [ | ((b0, ofs0), a) ]; [ discriminate | ].
  simpl (AMap.Raw.find _ _).
  destruct (AddressOrdered.compare (b, ofs) (b0, ofs0)) as [C|C|C].
  - discriminate.
  - injection 1 as <-.
    rewrite fold_right_cons, setPermBlock_lookup.
    if_tac; auto.
    injection C as <- <- .
    intros r.
    exfalso.
    contradiction H; split; auto.
  - rewrite fold_right_cons, setPermBlock_lookup.
    if_tac; auto.
Qed.

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
intros. rewrite fold_left_rev_right.
f_equal; extensionality x y; auto.
Qed.

Lemma A2PMap_add_outside T b b' ofs ofs' set o :
  (@A2PMap T (AMap.add (b, ofs) o set)) !! b' ofs' =
  if adr_range_dec (b, ofs) LKSIZE (b', ofs') then
    Some Writable
  else
    (@A2PMap T set) !! b' ofs'.
Proof.
  unfold A2PMap in *.
  unfold AMap.elements in *.
  unfold AMap.Raw.elements in *.
  unfold AMap.add in *.
  simpl (AMap.this _).

  etransitivity.
  {
    apply (AMap_Raw_add_fold_left _ (fun t t' => forall b' ofs', t !! b' ofs' = t' !! b' ofs')).
    - apply PMap_eq_refl.
    - apply PMap_eq_sym.
    - apply PMap_eq_trans.
    - intros; eapply A2P_congr; auto.
    - intros; eapply A2P_overwrite; auto.
    - intros; eapply A2P_comm; auto.
  }
  assert (P : Permutation ((b, ofs, o) :: AMap.this set) (AMap.this set ++ (b, ofs, o) :: nil)).
  { apply Permutation_cons_append. }
  etransitivity.
  {
    eapply (AMap_Raw_add_fold_left_permut _ (fun t t' => forall b' ofs', t !! b' ofs' = t' !! b' ofs')).
    - apply PMap_eq_refl.
    - apply PMap_eq_sym.
    - apply PMap_eq_trans.
    - intros; eapply A2P_congr; auto.
    - intros; eapply A2P_comm; auto.
    - apply P.
  }
  remember (AMap.this set) as l. clear set Heql.
  do 2 rewrite fold_right_rev_left.
  rewrite rev_app_distr. simpl (app _ _).
  remember (rev l) as l'; clear l Heql' P.
  rewrite (* canon. *)fold_right_cons.
  set (fold_right _ _ _) as m; clearbody m; clear.
  apply setPermBlock_lookup.
Qed.

Lemma find_too_small A y a x l :
  (AddressOrdered.lt y a \/ AddressOrdered.eq y a) ->
  Sorted (AMap.Raw.PX.ltk (elt:=A)) l ->
  HdRel (AMap.Raw.PX.ltk (elt:=A)) (a, x) l ->
  AMap.Raw.find (elt:=A) y l = None.
Proof.
  intros toosmall.
  induction l as [ | [b z] l]; auto.
  intros sorted below.
  inversion below as [ | b0 l0 Hab H ]; subst.
  change (AddressOrdered.lt a b) in Hab.
  simpl.
  destruct (AddressOrdered.compare y b).
  - reflexivity.
  - exfalso.
    destruct toosmall as [t|t].
    + pose proof AddressOrdered.lt_trans t Hab.
      eapply AddressOrdered.lt_not_eq; eauto.
    + hnf in t. subst.
      eapply AddressOrdered.lt_not_eq; eauto.
  - apply IHl; auto.
    inv sorted; eauto.
    inv sorted; eauto.
    eapply AMap.Raw.PX.Inf_lt; eauto.
    simpl; auto.
Qed.

Lemma sorted_find A a x l l'
      (sorted : Sorted (AMap.Raw.PX.ltk (elt:=A)) ((a, x) :: l))
      (sorted' : Sorted (AMap.Raw.PX.ltk (elt:=A)) ((a, x) :: l')) :
  (forall y : AMap.key,
      AMap.Raw.find (elt:=A) y ((a, x) :: l) =
      AMap.Raw.find (elt:=A) y ((a, x) :: l')) ->
  forall y : AMap.key,
    AMap.Raw.find (elt:=A) y l =
    AMap.Raw.find (elt:=A) y l'.
Proof.
  intros E.
  inversion sorted as [ | a0 l0 S B ]; subst. clear sorted.
  inversion sorted' as [ | a0 l0 S' B' ]; subst. clear sorted'.
  intros y; specialize (E y).
  simpl in E.
  destruct (AddressOrdered.compare y a).
  - erewrite find_too_small; eauto.
    erewrite find_too_small; eauto.
  - erewrite find_too_small; eauto.
    erewrite find_too_small; eauto.
  - auto.
Qed.

Lemma AMap_Equal_PMap_eq {A} m m' : AMap.Equal m m' -> @A2PMap A m = @A2PMap A m'.
Proof.
  intros E.
  unfold A2PMap in *.
  f_equal.
  unfold AMap.elements in *.
  destruct m as [l sorted], m' as [l' sorted']; simpl in *.
  unfold AMap.Equal in *.
  unfold AMap.find in *.
  unfold AMap.Raw.elements in *.
  simpl in *.
  revert l' sorted' E.
  induction l as [ | [a x] l]; intros l' sorted' E.
  - destruct l' as [ | [a' x] l']; auto. exfalso.
    specialize (E a'). simpl in E.
    destruct (AMap.Raw.MX.elim_compare_eq (eq_refl a')) as [p R]. rewrite R in E.
    discriminate.
  - destruct l' as [ | [a' x'] l'].
    + specialize (E a). simpl in E.
      destruct (AMap.Raw.MX.elim_compare_eq (eq_refl a)) as [p R]. rewrite R in E.
      discriminate.
    + assert (Ea : a = a' /\ x = x'). {
        pose (E a) as Ea. simpl in Ea.
        destruct (AMap.Raw.MX.elim_compare_eq (eq_refl a)) as [p R]. rewrite R in Ea.
        pose (E a') as Ea'. simpl in Ea'.
        destruct (AMap.Raw.MX.elim_compare_eq (eq_refl a')) as [p' R']. rewrite R' in Ea'.
        destruct (AddressOrdered.compare a a') eqn:Ec; try (split; congruence).
        destruct (AddressOrdered.compare a' a) eqn:Ec'; try (split; congruence).
        exfalso. eapply (@AddressOrdered.lt_not_eq a' a); eauto.
        exfalso. eapply (@AddressOrdered.lt_not_eq a a); auto.
        eapply AddressOrdered.lt_trans; eauto.
      }
      destruct Ea as [<- <-].
      f_equal.
      apply IHl.
      * inv sorted; auto.
      * inv sorted'; auto.
      * eapply sorted_find; eauto.
Qed.

Lemma AMap_remove_add {A} (m : AMap.t A) x y :
  AMap.find x m = Some y ->
  AMap.Equal m (AMap.add x y (AMap.remove x m)).
Proof.
  intros find.
  intros x'.
  rewrite AMap_find_add, AMap_find_remove.
  if_tac.
  - subst x'. auto.
  - reflexivity.
Qed.
