Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.OrderedType.

Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Coqlib.

Require Import msl.eq_dec.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.sepcomp. Import SepComp.
Require Import concurrency.permissions.
Require Import concurrency.lksize.
  
  
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
