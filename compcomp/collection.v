Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finfun tuple.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import cast.

Require Import ExtAxioms Arith Omega.

Lemma lt_incr n : n < n.+1. Proof. by []. Qed.
Lemma le_incr n : n <= n.+1. Proof. by []. Qed.

Definition Pred (T : Type) := T -> Prop.

Module COL. 
Record class (T t : Type) := Class 
  { size_ : t -> nat
  ; empty_: t
  ; sizeempty_ : size_ empty_ = 0

  (* get, set *)
  ; get_  : forall (r : t), 'I_(size_ r) -> T
  ; set_  : forall (r : t), 'I_(size_ r) -> T -> t
  ; setsize_ : 
      forall (r : t) (i : 'I_(size_ r)) x, 
      size_ r = size_ (@set_ r i x)
  ; gss_ : 
      forall (r : t) (i : 'I_(size_ r)) x, 
      @get_ (@set_ r i x) (cast_ord (setsize_ i x) i) = x
  ; gso_ : forall (r : t) (i j : 'I_(size_ r)) x, 
      i != j ->       
      @get_ (@set_ r i x) (cast_ord (setsize_ i x) j) = @get_ r j

  (* bump, unbump *)
  ; bump_ : t -> T -> t
  ; bumpoldord_ : forall (r : t) (i : 'I_(size_ r)) x, 'I_(size_ (bump_ r x))
  ; bumpoldord_charact_ :
      forall (r : t) (i : 'I_(size_ r)) x, 
      nat_of_ord (bumpoldord_ i x) = nat_of_ord i
  ; bumpneword_ : forall (r : t) x, 'I_(size_ (bump_ r x))
  ; bumpneword_charact_ : 
      forall (r : t) x, nat_of_ord (bumpneword_ r x) = size_ r
  ; bumpsize_ : forall (r : t) x, size_ (bump_ r x) = (size_ r).+1
  ; bumpgetold_ :
      forall (r : t) (i : 'I_(size_ r)) x, 
      @get_ (bump_ r x) (bumpoldord_ i x) = @get_ r i
  ; bumpgetnew_ : forall (r : t) x, @get_ (bump_ r x) (bumpneword_ r x) = x
  ; unbump_ : t -> t
  ; unbumpsize_ : forall r : t, size_ (@unbump_ r) = (size_ r).-1
  ; unbumpbump_ : forall (r : t) x, unbump_ (bump_ r x) = r 
  ; unbumpord_ : forall (r : t) (i : 'I_(size_ r).-1), 'I_(size_ (unbump_ r))
  ; unbumpord_charact_ :
      forall (r : t) (i : 'I_(size_ r).-1), 
      nat_of_ord (unbumpord_ i) = nat_of_ord i
  ; unbumpget_ : 
      forall (r : t) (i : 'I_(size_ r).-1) (pf : i < size_ r), 
      @get_ (unbump_ r) (unbumpord_ i) = @get_ r (Ordinal pf)

  (* all *)
  ; all_  : t -> Pred T -> Prop
  ; allget_ : 
      forall (r : t) p, all_ r p = forall i : 'I_(size_ r), p (get_ i)
  ; allset_ : 
      forall (r : t) (i : 'I_(size_ r)) p x,
      all_ (set_ i x) p = 
      [/\ p x & (forall i0 : 'I_(size_ r), (i0 == i) \/ p (get_ i0))]
  ; allbump_ : 
      forall (r : t) p x, all_ (bump_ r x) p = [/\ all_ r p & p x]
  ; allunbump_ : 
      forall (r : t) p, 
      all_ (unbump_ r) p
      = forall i : 'I_(size_ r), 
        (nat_of_ord i == (size_ r).-1) \/ p (get_ i)

  (* allb *)
  ; allb_  : t -> pred T -> bool
  ; allbget_ : 
      forall (r : t) p, allb_ r p = [forall i : 'I_(size_ r), p (get_ i)]
  ; allbset_ : 
      forall (r : t) (i : 'I_(size_ r)) p x,
      allb_ (set_ i x) p = 
      p x && [forall i0 : 'I_(size_ r), (i0 == i) || p (get_ i0) ]
  ; allbbump_ : 
      forall (r : t) p x, allb_ (bump_ r x) p = [&& allb_ r p & p x]
  ; allbunbump_ : 
      forall (r : t) p, 
      allb_ (unbump_ r) p
      = [forall i : 'I_(size_ r), 
         (nat_of_ord i == (size_ r).-1) || p (get_ i)]

  ; extensionality_ : 
      forall (r1 r2 : t) (pf : size_ r1 = size_ r2),
      (forall i, @get_ r1 i = @get_ r2 (cast_ord pf i)) ->
      r1 = r2
  }.
Structure type := Pack { val : Type; col : Type; class_of : class val col }.
Definition size (e : type) : col e -> nat :=
  let 'Pack _ _ r0 := e in size_ r0.
Definition empty (e : type) : col e :=
  let 'Pack _ _ r0 := e in empty_ r0.
Definition get (e : type) : forall (r : col e), 'I_(size r) -> val e :=
  let 'Pack _ _ r0 := e in @get_ _ _ r0.
Definition set (e : type) : forall (r : col e), 'I_(size r) -> val e -> col e :=
  let 'Pack _ _ r0 := e in @set_ _ _ r0.
Definition setsize (e : type) : 
  forall (r : col e) (i : 'I_(size r)) x, size r = size (set i x) :=
  let 'Pack _ _ r0 := e in @setsize_ _ _ r0.
Definition bump (e : type) : col e -> val e -> col e :=
  let 'Pack _ _ r0 := e in bump_ r0.
Definition bumpoldord (e : type) : 
  forall r : col e, 'I_(size r) -> forall x : val e, 'I_(size (bump r x)) :=
  let 'Pack _ _ r0 := e in @bumpoldord_ _ _ r0.
Definition bumpoldord_charact (e : type) : 
  forall (r : col e) (i : 'I_(size r)) (x : val e), 
  nat_of_ord (bumpoldord i x) = nat_of_ord i :=
  let 'Pack _ _ r0 := e in @bumpoldord_charact_ _ _ r0.
Definition bumpneword (e : type) : 
  forall (r : col e) (x : val e), 'I_(size (bump r x)) :=
  let 'Pack _ _ r0 := e in @bumpneword_ _ _ r0.
Definition bumpneword_charact (e : type) : 
  forall (r : col e) (x : val e), 
  nat_of_ord (bumpneword r x) = size r :=
  let 'Pack _ _ r0 := e in @bumpneword_charact_ _ _ r0.
Definition unbump (e : type) : col e -> col e := 
  let 'Pack _ _ r0 := e in @unbump_ _ _ r0.
Definition unbumpord (e : type) : 
  forall r : col e, 'I_(size r).-1 -> 'I_(size (unbump r)) :=
  let 'Pack _ _ r0 := e in @unbumpord_ _ _ r0.
Definition unbumpord_charact (e : type) :
  forall (r : col e) (i : 'I_(size r).-1),
  nat_of_ord (unbumpord i) = nat_of_ord i :=
  let 'Pack _ _ r0 := e in @unbumpord_charact_ _ _ r0.
Definition all (e : type) : col e -> Pred (val e) -> Prop :=
  let 'Pack _ _ r := e in all_ r.
Definition allb (e : type) : col e -> pred (val e) -> bool :=
  let 'Pack _ _ r := e in allb_ r.
Arguments size {e} _ : simpl never.
Arguments empty {e} : simpl never.
Arguments get {e} _ _ : simpl never.
Arguments set {e} _ _ _ : simpl never.
Arguments setsize {e} _ _ _ : simpl never.
Arguments bump {e} _ _ : simpl never.
Arguments bumpoldord {e} _ _ _ : simpl never.
Arguments bumpoldord_charact {e} _ _ _ : simpl never.
Arguments bumpneword {e} _ _ : simpl never.
Arguments bumpneword_charact {e} _ _ : simpl never.
Arguments unbump {e} _ : simpl never.
Arguments unbumpord {e} _ _ : simpl never.
Arguments unbumpord_charact {e} _ _ : simpl never.
Arguments all {e} _ _ : simpl never.
Arguments allb {e} _ _ : simpl never.
Arguments Class {T} 
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Module theory.
  Lemma sizeempty e : size (@empty e) = 0.
  Proof. refine (let 'Pack _ _ r := e in _)=> /=.
         apply: (@sizeempty_ _ _ r). Qed.

  Lemma gss e (r : col e) i x : 
    get (set r i x) (cast_ord (setsize r i x) i) = x.
  Proof. move: r i x; refine (let 'Pack _ _ r := e in _)=> /= r0 i x.
         apply: (@gss_ _ _ r r0 i x). Qed.
  Lemma gso e (r : col e) i j x : 
    i != j -> 
    get (set r i x) (cast_ord (setsize r i x) j) = get r j.
  Proof. move: r i j x; refine (let 'Pack _ _ r := e in _)=> /= r0 i j x.
         apply: (@gso_ _ _ r r0 i j x). Qed.

  Lemma bumpsize e (r : col e) x : size (bump r x) = (size r).+1.
  Proof. move: r x; refine (let 'Pack _ _ r := e in _)=> /= r0 x.
         apply: (@bumpsize_ _ _ r r0 x). Qed.
  Lemma bumpgetold e (r : col e) x i : 
    get (bump r x) (bumpoldord r i x) = get r i.
  Proof. move: r x i; refine (let 'Pack _ _ r := e in _)=> /= r0 x i.
         apply: (@bumpgetold_ _ _ r r0 i). Qed.
  Lemma bumpgetnew e (r : col e) x : get (bump r x) (bumpneword r x) = x.
  Proof. move: r x; refine (let 'Pack _ _ r := e in _)=> /= r0 x.
         apply: (@bumpgetnew_ _ _ r r0 x). Qed.
  Lemma unbumpsize e (r : col e) : size (unbump r) = (size r).-1.
  Proof. move: r; refine (let 'Pack _ _ r := e in _)=> /= r0.
         apply: (@unbumpsize_ _ _ r r0). Qed.
  Lemma unbumpbump e (r : col e) x : unbump (bump r x) = r.
  Proof. move: r x; refine (let 'Pack _ _ r := e in _)=> /= r0 x.
         apply (@unbumpbump_ _ _ r r0). Qed.
  Lemma unbumpget e (r : col e) (i : 'I_(size r).-1) (pf : i < size r) :
    get (unbump r) (unbumpord r i) = get r (Ordinal pf).
  Proof. move: r i pf; refine (let 'Pack _ _ r := e in _)=> /= r0 i pf.
         apply (@unbumpget_ _ _ r r0). Qed.

  Lemma allget e (r : col e) p : 
    all r p = forall i : 'I_(size r), p (get r i).
  Proof. move: r p; refine (let 'Pack _ _ r := e in _)=> /= r0 p.
         apply: (@allget_ _ _ r r0). Qed.
  Lemma allset e (r : col e) (p : pred (val e)) i x : 
    all (set r i x) p 
    = [/\ p x & forall i0 : 'I_(size r), (i0 == i) \/ p (get r i0)].
  Proof. move: r p i x; refine (let 'Pack _ _ r := e in _)=> /= r0 p i x.
         apply: (@allset_ _ _ r r0 i p x). Qed.
  Lemma allbump e (r : col e) p x : all (bump r x) p = [/\ all r p & p x].
  Proof. move: r p x; refine (let 'Pack _ _ r := e in _)=> /= r0 p x.
         apply: (@allbump_ _ _ r r0 p x). Qed.
  Lemma allunbump e (r : col e) p : 
    all (unbump r) p
    = forall i : 'I_(size r), 
      (nat_of_ord i == (size r).-1) \/ p (get r i).
  Proof. move: r p; refine (let 'Pack _ _ r := e in _)=> /= r0 p.
         apply: (@allunbump_ _ _ r r0 p). Qed.

  Lemma allbget e (r : col e) p : 
    allb r p = [forall i : 'I_(size r), p (get r i)].
  Proof. move: r p; refine (let 'Pack _ _ r := e in _)=> /= r0 p.
         apply: (@allbget_ _ _ r r0). Qed.
  Lemma allbset e (r : col e) (p : pred (val e)) i x : 
    allb (set r i x) p 
    = p x && [forall i0 : 'I_(size r), (i0 == i) || p (get r i0)].
  Proof. move: r p i x; refine (let 'Pack _ _ r := e in _)=> /= r0 p i x.
         apply: (@allbset_ _ _ r r0 i p x). Qed.
  Lemma allbbump e (r : col e) p x : allb (bump r x) p = [&& allb r p & p x].
  Proof. move: r p x; refine (let 'Pack _ _ r := e in _)=> /= r0 p x.
         apply: (@allbbump_ _ _ r r0 p x). Qed.
  Lemma allbunbump e (r : col e) p : 
    allb (unbump r) p
    = [forall i : 'I_(size r), 
       (nat_of_ord i == (size r).-1) || p (get r i)].
  Proof. move: r p; refine (let 'Pack _ _ r := e in _)=> /= r0 p.
         apply: (@allbunbump_ _ _ r r0 p). Qed.

  Lemma extensionality e (r1 r2 : col e) (pf : size r1 = size r2) :
    (forall i, get r1 i = get r2 (cast_ord pf i)) ->
    r1 = r2.
  Proof. move: r1 r2 pf; refine (let 'Pack _ _ r := e in _)=> /= r1 r2 pf H.
         by apply: (@extensionality_ _ _ r r1 r2 pf). Qed.

  (* derived operations *)

  Lemma lastord (e : type) (r : col e) (sizeinv : 0 < size r) : 
    {i : 'I_(size r) | i.+1 = size r}.
  Proof.
    have ltpf : (size r).-1 < size r by case: (size r) sizeinv.
    by exists (Ordinal ltpf)=> /=; rewrite prednK.
  Qed.

  Definition peek (e : type) (r : col e) (sizeinv : 0 < size r) : val e := 
    get r (projT1 (lastord sizeinv)).

  Lemma bumpsize' e (r : col e) (x : val e) : 0 < size (bump r x).
  Proof. by rewrite bumpsize. Qed.

  Lemma bumppeek (e : type) (r : col e) x : 
    @peek _ (bump r x) (bumpsize' r x) = x.
  Proof. 
    rewrite /peek. 
    case: (lastord _)=> /= x0 H.
    have H2: x0 = bumpneword r x.
    { suff: nat_of_ord x0 = nat_of_ord (bumpneword r x); 
        first by apply: ord_inj.
      rewrite (bumpneword_charact r x).
      by move: x0 H; rewrite bumpsize=> x0; case. }
    by subst x0; rewrite bumpgetnew.
  Qed.
End theory.
End COL.
Import COL.theory.

Module FunCollection. Section FunCollection.
Variable T : Type.

Record col : Type := mk { 
  size  : nat;
  thefun: size.-tuple T
}.

Definition empty : col := mk [tuple].

Lemma sizeempty : size empty = 0.
Proof. by []. Qed.

Definition get (r : col) (i : 'I_(size r)) := tnth (thefun r) i.

Lemma extensionality (r1 r2 : col) (pf : size r1 = size r2) :
  (forall i, @get r1 i = @get r2 (cast_ord pf i)) ->
  r1 = r2.
Proof.
rewrite /get => H.
case: r1 pf H=> sz1 fn1 /=; case: r2=> sz2 fn2 /= pf; subst=> H.
have H2: tnth fn1 =1 tnth fn2.
{ by move=> i; move: (H i); rewrite cast_ord_id. }
by move: (eq_from_tnth H2)=> H3; subst.
Qed.

Definition set (r : col) (i : 'I_(size r)) (v : T) :=
  mk [tuple (if i0 == i then v else tnth (thefun r) i0) | i0 < size r].

Lemma setsize r (i : 'I_(size r)) x : size r = size (set i x).
Proof. by []. Qed.

Lemma gss r (i : 'I_(size r)) x : get (cast_ord (setsize i x) i) = x.
Proof. by rewrite /get /= tnth_mktuple cast_ord_id eq_refl. Qed.

Lemma gso r (i j : 'I_(size r)) x : 
  i != j -> get (cast_ord (setsize i x) j) = get j.
Proof.
rewrite /get /= tnth_mktuple cast_ord_id; case H: (j == i)=> //.
by rewrite eq_sym in H; rewrite H.
Qed.

Definition bump (r : col) (v : T) := 
  let: new_size := (size r).+1 in
  let: new_idx  := Ordinal (lt_incr (size r)) in
  mk [ tuple (match unlift new_idx i with
                | None => v
                | Some i' => tnth (thefun r) i'
              end)
     | i < new_size ].

Program Definition bumpoldord r (i : 'I_(size r)) (v : T) : 
  'I_(size (bump r v)) :=
  @widen_ord (size r) (size (bump r v)) _ i.

Lemma bumpoldord_charact r (i : 'I_(size r)) x : 
  nat_of_ord (bumpoldord i x) = nat_of_ord i.
Proof. by []. Qed.

Definition bumpneword r (v : T) : 'I_(size (bump r v)) :=  ord_max.

Lemma bumpneword_charact r x : nat_of_ord (bumpneword r x) = size r.
Proof. by []. Qed.

Lemma bumpsize r x : size (bump r x) = (size r).+1.
Proof. by []. Qed.

Lemma bumpgetold r (i : 'I_(size r)) v : get (bumpoldord i v) = get i.
Proof. 
rewrite /get /bumpoldord tnth_mktuple /=.
case: (unliftP 
  (Ordinal (n:=(size r).+1) (m:=size r) (lt_incr (size r)))
  (widen_ord (m:=(size r).+1) (bumpoldord_obligation_1 (r:=r) i v) i)).
{ rewrite /widen_ord /lift /= => j; case=> H.
  have ->: i = j.
  { apply: ord_inj; rewrite H /fintype.bump /nat_of_bool.
    by have ->: (size r <= j) = false
    by move {H}; case: j=> /= m /ltP=> H; apply/leP; omega.
  } by [].
}
rewrite /widen_ord; case; case: i=> m H /= H2.
by elimtype False; subst; move: (ltP H)=> H2; omega.
Qed.

Lemma bumpgetnew r x : get (bumpneword r x) = x.
Proof.
rewrite /get /bumpneword /bump /= tnth_mktuple.
case: (unliftP 
  (Ordinal (n:=(size r).+1) (m:=size r) (lt_incr (size r))) ord_max)=> //.
move=> /= j; case; rewrite /fintype.bump /nat_of_bool.
have H: (size r <= j) = false
by case: j=> /= m /ltP=> H; apply/leP; omega.
rewrite H=> H2; elimtype False; rewrite /addn /= in H2.
by move: H; case: j H2=> m pf; case: r pf=> /= size0 H H2 ->; move/leP.
Qed.

Program Definition unbump (r : col) :=
  mk [ tuple (tnth (thefun r) (@Ordinal (size r) i _))
     | i < (size r).-1 ].
Next Obligation. 
by case: (size r) i=> //= n; case=> /= m /ltP H; apply/ltP; omega.
Qed.

Lemma unbumpsize (r : col) : size (unbump r) = (size r).-1.
Proof. by []. Qed.

Definition unbumpord (r : col) (i : 'I_(size r).-1) : 'I_(size (unbump r)) :=
  cast_ord (unbumpsize r) i.

Lemma unbumpord_charact (r : col) (i : 'I_(size r).-1) : 
  nat_of_ord (unbumpord i) = nat_of_ord i.
Proof. by rewrite /unbumpord cast_ord_id. Qed.

Lemma unbumpget' (r : col) (i : 'I_(size (unbump r))) (pf : i < size r) : 
  @get (unbump r) i = @get r (Ordinal pf).
Proof.
rewrite /get /unbump /= tnth_mktuple.
by do 2 f_equal; apply: proof_irr.
Qed.

Lemma unbumpget (r : col) (i : 'I_(size (unbump r))) (pf : i < size r) : 
  @get (unbump r) (unbumpord i) = @get r (Ordinal pf).
Proof.
rewrite /get /unbump /= tnth_mktuple.
by do 2 f_equal; apply: proof_irr.
Qed.
 
Lemma unbumpbump (r : col) x : unbump (bump r x) = r.
Proof.
apply: extensionality=> i; rewrite cast_ord_id unbumpget'.
by move: (ltn_ord i); move: i; rewrite unbumpsize=> i /ltP H; apply/ltP; omega.
move=> lt; have ->: Ordinal (m:=i) _ = bumpoldord i x.
{ move=> pf; rewrite /bumpoldord /widen_ord /=; f_equal.
  by apply: proof_irr.
}
by rewrite bumpgetold.
Qed.

Definition all (r : col) (p : Pred T) : Prop := 
  forall i : 'I_(size r), p (get i).

Lemma allget r p : 
  all r p = forall i : 'I_(size r), p (get i).
Proof. by []. Qed.

Lemma allset r (i : 'I_(size r)) p x : 
  all (set i x) p 
  = [/\ p x & forall i0 : 'I_(size r), (i0 == i) \/ p (get i0)]. 
Proof.
rewrite /all; apply: prop_ext; split=> H.
{ split; first by move: (H (cast_ord (setsize i x) i)); rewrite gss.
  move=> i0; case H2: (i0 == i); first by left.
  right; move: (H (cast_ord (setsize i x) i0)); rewrite gso=> //.
  by apply/eqP=> H3; rewrite H3 eq_refl in H2.
}
{ case: H=> H H2 i0; case eq: (i == i0).
  { move: (eqP eq)=> <-.
    have H3: i = cast_ord (setsize i x) i by rewrite cast_ord_id.
    by rewrite {2}H3 gss.    
  }
  { have ->: i0 = cast_ord (setsize i x) i0 by rewrite cast_ord_id.
    move: eq; case: (H2 i0); first by move/eqP=> <-; move/eqP.
    move=> H3 H4; rewrite gso=> //; apply/eqP=> H5; subst i0.
    by rewrite eq_refl in H4.
  }
}
Qed.

Lemma allbump r p x : all (bump r x) p = [/\ all r p & p x].
Proof.
rewrite /all; apply: prop_ext; split=> H.
{ split.
  { by move=> i; move: (H (bumpoldord i x)); rewrite bumpgetold. }
  { by move: (H (bumpneword r x)); rewrite bumpgetnew. }
}
{ move=> i; case: H=> H H2; case lt: (i < size r).
  { move: (H (Ordinal lt))=> H3.
    move: (bumpgetold (Ordinal lt) x).
    have H4: bumpoldord (Ordinal lt) x = i.
    { by apply: ord_inj; rewrite bumpoldord_charact. }
    by rewrite H4=> ->.
  }
  { have H3: i = bumpneword r x.
    { apply: ord_inj; rewrite bumpneword_charact.
      move: lt; move/ltP; move: (ltP (ltn_ord i)); clear.
      move: i; rewrite bumpsize=> i H H2; omega.
    }
    by rewrite H3 bumpgetnew.
  }
}
Qed.     

Lemma allunbump' r p : 
  all (unbump r) p
  = forall i : 'I_(size r), (nat_of_ord i == (size r).-1) \/ p (get i).
Proof.
rewrite /all; apply: prop_ext; split=> H.
{ move=> i; case H2: (nat_of_ord i == (size r).-1); first by left.
  have H3: i < (size r).-1.
  { 
    apply/ltP; move: (ltP (ltn_ord i))=> H3.
    have H4: nat_of_ord i <> (size r).-1. 
    { by move=> C; rewrite C eq_refl in H2. }
    omega.
  }
  move {H2}; rewrite -unbumpsize in H3.  
  move: (H (Ordinal H3)); rewrite unbumpget'. 
  { apply/ltP; move: (ltP H3)=> H4; rewrite unbumpsize in H4; simpl; omega. }
  move=> pf /= H4; right.
  by move: H4; have ->: Ordinal pf = i by apply: ord_inj.
}
{ move=> i; have lt: i < size r. 
  { move: i; rewrite unbumpsize=> i; move: (ltP (ltn_ord i))=> H2.
    apply/ltP; omega.
}
  case: (H (Ordinal lt))=> /=.
  { move/eqP=> H2; elimtype False; move: (ltn_ord i); rewrite H2; clear.
    by rewrite unbumpsize; move/ltP=> H; omega.
  }
  { by move=> H2; rewrite unbumpget'. }
}
Qed.

Definition allb (r : col) (p : pred T) : bool := seq.all p (thefun r).

Lemma allbget r p : 
  allb r p = [forall i : 'I_(size r), p (get i)].
Proof. by rewrite /allb /get /= -forallb_tnth. Qed.

Lemma allbset r (i : 'I_(size r)) p x : 
  allb (set i x) p 
  = p x && [forall i0 : 'I_(size r), (i0 == i) || p (get i0)]. 
Proof.
rewrite /allb /set -forallb_tnth /=; case H: (p x)=> /=. 
{ f_equal; extensionality y; do 2 f_equal; rewrite tnth_mktuple.
  by case H2: (y == i).
}
rewrite forallb_tnth; case: (@all_tnthP _ T p [tuple _ | i0 < size r])=> //.
by move/(_ i); rewrite tnth_mktuple eqxx H. 
Qed.

Lemma allbbump r p x : allb (bump r x) p = [&& allb r p & p x].
Proof.
rewrite !allbget.
rewrite andbC.
case H: (p x)=> /=.
rewrite !forallb_tnth.
case: (@all_tnthP _ _ p (thefun _)).
{ move=> H2; apply/all_tnthP=> i. 
  case H3: (i == bumpneword r x).
  - by move: (eqP H3)=> ->; move: (bumpgetnew r x); rewrite /get => ->.
  - have lt: i < size r. 
    { move: H3; rewrite /bumpneword=> /eqP H3.
      have H4: (i < (size r).+1)%coq_nat.
      { move {H3}; case: i=> m H3; move: (ltP H3)=> H4 /=; omega. }
      have H5: nat_of_ord (@ord_max (size r)) = size r by [].
      have H6: nat_of_ord i <> nat_of_ord (@ord_max (size r)).
      { move=> H6; apply: H3; apply: ord_inj; rewrite H6=> //. }
      apply/ltP; omega.
    }
    set i0 := Ordinal lt.
    move: (bumpgetold i0 x); rewrite /get.
    have H4: bumpoldord i0 x = i.
    { apply: ord_inj; apply: bumpoldord_charact. }
    by rewrite H4 => ->.
}
{
  move=> H2; apply/all_tnthP=> C; apply: H2=> i.
  by move: (C (bumpoldord i x)); move: (bumpgetold i x); rewrite /get => ->.
}
rewrite forallb_tnth.
case: (@all_tnthP _ _ p (thefun (bump r x)))=> // H2.
move: (H2 (bumpneword r x)). 
by move: (bumpgetnew r x); rewrite /get => ->; rewrite H.
Qed.

Lemma allbunbump r p : allb r p -> allb (unbump r) p.
Proof.
rewrite /allb /set /unbump /thefun.
case: r=> sz fn.
case: (@all_tnthP _ _ p _)=> // H _.
case: (@all_tnthP _ _ p _)=> // H2; elimtype False; apply: H2.
move=> /= i; rewrite tnth_mktuple.
have lt: i < sz by apply/ltP; move: (ltn_ord i)=> /ltP H2; omega.
move: (H (Ordinal lt)); move {H}.
generalize (unbump_obligation_1 (r:={| size := sz; thefun := fn |}) i)=> /=.
by move=> lt'; have ->: lt = lt' by apply: proof_irr.
Qed.

Lemma allbunbump' r p : 
  allb (unbump r) p
  = [forall i : 'I_(size r), (nat_of_ord i == (size r).-1) || p (get i)].
Proof.
rewrite /allb /set /unbump /thefun.
case: (@all_tnthP _ _ p _)=> //= H.
suff H2: [forall i, (nat_of_ord i == (size r).-1) || p (get (r:=r) i)].
by rewrite H2.
apply/forallP=> i.
case H2: (nat_of_ord i == (size r).-1)=> //=.
have lt: i < (size r).-1. 
{ move: (negbT H2)=> /negP; clear.
  case: i=> m lt /= H; suff: m <> (size r).-1.
  by move=> H2; move: {lt}(ltP lt)=> lt; apply/ltP; omega.
  by move=> H2; apply: H; apply/eqP.
}
move: (H (Ordinal lt)).
rewrite tnth_mktuple.
move: (unbump_obligation_1 _)=> pf.
rewrite /get.
generalize dependent r.
case=> /= sz fn _; case=> m pf' _ _ pf /=.
by have ->: pf = pf' by apply: proof_irr.
suff H2: ~~ [forall i, (nat_of_ord i == (size r).-1) || p (get (r:=r) i)].
by apply: sym_eq; apply: negbTE.
apply/negP=> H2.
apply: H.
move: {H2} (forallP H2)=> H2 i.
generalize dependent r.
case=> sz fn /= H i.
have lt: i < sz. 
{ case: i=> m H2; move: (ltP H2)=> H3 /=; apply/ltP; omega.
}
move: {H} (H (Ordinal lt))=> /=; case/orP.
{ move=> /eqP H; elimtype False. 
  by case: i lt H=> m H; move: (ltP H)=> H2 /= ? H3; rewrite H3 in H2; omega.
}
{ rewrite /get /= tnth_mktuple; move: (unbump_obligation_1 _)=> pf.
  by have ->: pf = lt by apply: proof_irr.
}
Qed.

End FunCollection. 

End FunCollection.

Section FunCollectionClass.

Import FunCollection.

Variable T : Type.

Definition fun_COLcl : COL.class T (col T) := 
  COL.Class (col T) 
    (@size T) (@empty T) (@sizeempty T) (@get T) (@set T) 
    (@setsize T) (@gss T) (@gso T) 
    (@bump T) (@bumpoldord T) (@bumpoldord_charact T) 
    (@bumpneword T) (@bumpneword_charact T)
    (@bumpsize T) (@bumpgetold T) (@bumpgetnew T) 
    (@unbump T) (@unbumpsize T) (@unbumpbump T) 
    (@unbumpord T) (@unbumpord_charact T) (@unbumpget T)
    (@all T) (@allget T) (@allset T) (@allbump T) (@allunbump' T)
    (@allb T) (@allbget T) (@allbset T) (@allbbump T) (@allbunbump' T)
    (@extensionality T).

End FunCollectionClass.

Canonical Structure fun_COLty (T : Type) : COL.type := 
  COL.Pack (fun_COLcl T).

Notation "[ 'collection' aTy ]" := (COL.col (fun_COLty aTy)).

Section test.

Import COL.

Lemma xx : @peek _ (bump empty 0) (bumpsize' empty 0) = 0.
Proof. by rewrite bumppeek. Qed.

End test.  
