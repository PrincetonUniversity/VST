(** * Functional model of hash tables *)
Require Import VST.floyd.proofauto.

Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec. 

Fixpoint hashfun_aux (h: Z) (s: string) : Z :=
 match s with
 | nil => h
 | c :: s' =>  hashfun_aux ((h * 65599 + Byte.signed c) mod Int.modulus) s'
end.

Definition hashfun (s: string) := hashfun_aux 0 s.

Definition hashtable_contents := list (list (string * Z)).

Definition N := 109.
Lemma N_eq : N = 109. 
Proof. reflexivity. Qed.
Hint Rewrite N_eq : rep_omega.
Global Opaque N.

Definition empty_table : hashtable_contents :=
  list_repeat (Z.to_nat N) nil.

Fixpoint list_get (s: string) (al: list (string * Z)) : Z :=
  match al with
 | (k,i) :: al' => if eq_dec s k then i else list_get s al'
 | nil => 0
 end.

Fixpoint list_incr (s: string) (al: list (string * Z)) :  list (string * Z) :=
  match al with
 | (k,i) :: al' => if eq_dec s k 
                      then (k, i +1)::al'
                      else (k,i)::list_incr s al'
 | nil => (s, 1)::nil
 end.

Definition hashtable_get  (s: string) (contents: hashtable_contents) : Z :=
  list_get s (Znth (hashfun s mod (Zlength contents)) contents).

Definition hashtable_incr (s: string) (contents: hashtable_contents) : hashtable_contents :=
  let h := hashfun s mod (Zlength contents)
  in let al := Znth h contents
  in upd_Znth h contents (list_incr s al).

Lemma hashfun_inrange: forall s, 0 <= hashfun s <= Int.max_unsigned.
Proof.
  intros s. unfold hashfun. set (n := 0).
  unfold n at 1.
  assert (0 <= n <= Int.max_unsigned) by rep_omega.
  generalize dependent n.
  induction s.
  * (* s = [] *)
     simpl. intros. rep_omega.
  * (* s = .. *)
    simpl. intros.
    apply IHs.
    enough (0 <= (n * 65599 + Byte.signed a) mod Int.modulus < Int.modulus).
    rep_omega.
    apply Z.mod_pos_bound.
    rep_omega.
Qed.

Lemma hashtable_get_unfold:
 forall sigma (cts: list (list (string * Z) * val)),
 hashtable_get sigma (map fst cts) =
  list_get sigma (Znth (hashfun sigma mod (Zlength cts)) (map fst cts)).
Proof.
  unfold hashtable_get.
  intros. rewrite Zlength_map.
  reflexivity.
Qed.

Lemma Zlength_hashtable_incr:
 forall sigma cts, 
      0 < Zlength cts -> 
      Zlength (hashtable_incr sigma cts) = Zlength cts.
Proof.
  intros. unfold hashtable_incr.
  apply upd_Znth_Zlength. apply Z.mod_pos_bound. auto.
Qed.
Hint Rewrite Zlength_hashtable_incr using list_solve : sublist.

Module Int.
Lemma repr_mod_modulus_eq: forall x,
  Int.repr (x mod Int.modulus) = Int.repr x.
Proof.
  intros. apply unsigned_eq_eq. unfold Int.unsigned. simpl.
  do 2 rewrite Int.Z_mod_modulus_eq.
  apply Z.mod_mod. rep_omega.
Qed.
End Int.

Lemma hashfun_snoc:
  forall sigma h lo i,
    0 <= lo ->
    lo <= i < Zlength sigma ->
  Int.repr (hashfun_aux h (sublist lo (i + 1) sigma)) =
  Int.repr (hashfun_aux h (sublist lo i sigma) * 65599 + Byte.signed (Znth i sigma)).
Proof.
  intros. remember (Z.to_nat (i-lo)) as len.
  assert (0 <= i-lo) by omega.
  apply Z2Nat.id in H1. rewrite <- Heqlen in *. clear Heqlen.
  revert h lo i H H0 H1.
  induction len; intros.
  * (* len = 0 *)
    simpl in H1. assert (i = lo) by omega. subst.
    rewrite sublist_one; try omega.
    rewrite sublist_nil.
    simpl. apply Int.repr_mod_modulus_eq.
  * (* len > 0 *)
    assert (i - lo > 0). { rewrite <- H1. simpl. apply Zgt_pos_0. }
    erewrite sublist_split; [rewrite sublist_one | ..]; auto; try omega.
    erewrite (sublist_split lo); [rewrite (sublist_one lo) | .. ]; auto; try omega.
    simpl. apply IHlen; try rep_omega.
    rewrite Nat2Z.inj_succ in H1. unfold Z.succ in H1. omega.
Qed.

Module Type COUNT_TABLE.
 Parameter table: Type.
 Parameter key : Type.
 Parameter empty: table.
 Parameter get: key -> table -> Z.
 Parameter incr: key -> table -> table.
 Axiom gempty: forall k,   (* get-empty *)
       get k empty = 0.
 Axiom gss: forall k t,      (* get-set-same *)
      get k (incr k t) = 1+(get k t).
 Axiom gso: forall j k t,    (* get-set-other *)
      j <> k -> get j (incr k t) = get j t.
End COUNT_TABLE.

(** This means:  in any [Module] that satisfies this [Module Type],
   there's a type [table] of count-tables,
   and operators [empty], [get], [set] that satisfy the axioms
   [gempty], [gss], and [gso].
  
  It's easy to make a slow implementation of [COUNT_TABLE], using functions. *)

Module FunTable <: COUNT_TABLE.
 Definition table: Type := nat -> Z.
 Definition key : Type := nat.
 Definition empty: table := fun k => 0.
 Definition get (k: key) (t: table) : Z := t k.
 Definition incr (k: key) (t: table) : table :=
    fun k' => if Nat.eqb k' k then 1 + t k' else t k'.
 Lemma gempty: forall k,  get k empty = 0.
 Proof. auto. Qed.
 Lemma gss: forall k t,  get k (incr k t) = 1+(get k t).
 Proof. intros. unfold incr, get. rewrite Nat.eqb_refl. auto. Qed.
 Lemma gso: forall j k t,  j <> k -> get j (incr k t) = get j t.
 Proof. intros. unfold incr, get. replace (j =? k)%nat with false. auto. symmetry. rewrite Nat.eqb_neq. auto.
Qed.
End FunTable.

(**  Now we make a "fast" implementation using hash tables.  We
  put "fast" in quotes because, unlike the imperative implementation,
 the purely functional implementation takes linear time, not constant time,
 to select the the i'th bucket.  That is, [Znth i al] takes time proportional to [i].
 But that is no problem, because we are not using [hashtable_get] and
 [hashtable_incr] as our real implementation; they are serving as the 
 _functional model_ of the fast implementation in C.  *)

Module IntHashTable <: COUNT_TABLE.
 Definition hashtable_invariant (cts: hashtable_contents) : Prop :=
  Zlength cts = N /\
  forall i, 0 <= i < N ->
             list_norepet (map fst (Znth i cts))
             /\ Forall (fun s => hashfun s mod N = i) (map fst (Znth i cts)).
 Definition table := sig hashtable_invariant.
 Definition key := string.

 Lemma empty_invariant: hashtable_invariant empty_table.
 Proof.
  unfold hashtable_invariant.
  split; auto. intros.
  assert (Znth i empty_table = []). { unfold empty_table. apply Znth_list_repeat_inrange; auto. }
  rewrite H0.
  simpl. split; auto. constructor.
 Qed.

 Lemma incr_invariant: forall k cts, hashtable_invariant cts -> hashtable_invariant (hashtable_incr k cts).
 Proof.
  unfold hashtable_invariant. intros.
  destruct H.
  split. rewrite Zlength_hashtable_incr; rep_omega.
  intros. specialize (H0 i H1).
  unfold hashtable_incr.
  set (h := hashfun k mod Zlength cts).
  assert (0 <= h < N). { subst h. rewrite H. apply Z.mod_pos_bound. rep_omega. }
  destruct (i =? h) eqn:Heqb;
    [ apply Z.eqb_eq in Heqb | apply Z.eqb_neq in Heqb ];
    subst;
    [ rewrite upd_Znth_same; try omega | rewrite upd_Znth_diff; try omega ];
    auto.
  assert (In_list_incr: forall s al, In s (map fst (list_incr k al)) -> s = k \/ In s (map fst al)). {
    intros. induction al; simpl in *.
    - destruct H3; auto.
    - destruct a. destruct (EqDec_string k s0) eqn:?; auto.
      inversion H3; auto. apply IHal in H4. destruct H4; auto.
  }
  remember (Znth h cts) as al.
  clear Heqal.
  induction al; simpl.
  - (* al = [] *)
    split.
    (* list_norepet [k] *)
    repeat constructor; auto.
    (* Forall (fun s : string => hashfun s mod N = h) [k] *)
    repeat constructor. subst h. rewrite H. auto.
  - (* al = .. *)
    destruct a. destruct (EqDec_string k s) eqn:?.
    + (* k = s *)
      auto.
    + (* k <> s *)
      simpl. destruct H0. inversion H0. inversion H3.
      split; constructor; auto.
      * intro. apply In_list_incr in H12. destruct H12; auto.
      * eapply proj1. apply IHal. auto.
      * eapply proj2. apply IHal. auto.
 Qed.

 Definition empty : table := exist _ _ empty_invariant.
 Definition get : key -> table -> Z := fun k tbl => hashtable_get k (proj1_sig tbl).
 Definition incr : key -> table -> table := 
       fun k tbl => exist _ _ (incr_invariant k _ (proj2_sig tbl)).


 Theorem gempty: forall k, get k empty = 0. 
 Proof.
  intros. unfold get. simpl. unfold empty_table. unfold hashtable_get.
  rewrite Znth_list_repeat_inrange; auto. rewrite Zlength_list_repeat; try rep_omega.
  apply Z.mod_pos_bound; try rep_omega.
 Qed.

 Theorem gss: forall k t,  get k (incr k t) =  1 + (get k t).
 Proof.
  intros. unfold get. simpl.
  remember (proj1_sig t) as ht.
  pose proof (proj2_sig t). rewrite <- Heqht in *. unfold hashtable_invariant in *.
  unfold hashtable_get, hashtable_incr.
  rewrite upd_Znth_Zlength by (apply Z.mod_pos_bound; rep_omega).
  remember (hashfun k mod Zlength ht) as h.
  rewrite upd_Znth_same by (subst h; apply Z.mod_pos_bound; rep_omega).
  remember (Znth h ht) as al.
  clear Heqal Heqh h H Heqht ht t.
  induction al.
  - (* al = [] *)
    simpl. destruct (EqDec_string k k) eqn:?; auto. contradiction.
  - (* al = .. *)
    simpl. destruct a. destruct (EqDec_string k s) eqn:?.
    + (* k = s *)
      subst s. simpl. destruct (EqDec_string k k) eqn:?; auto; try omega. contradiction.
    + (* k <> s *)
      simpl. rewrite Heqs0. auto.
 Qed.

 Theorem gso: forall j k t,    (* get-set-other *)
      j <> k -> get j (incr k t) = get j t.
 Proof.
  intros. unfold get. simpl.
  remember (proj1_sig t) as ht.
  pose proof (proj2_sig t). rewrite <- Heqht in *. unfold hashtable_invariant in *.
  unfold hashtable_get, hashtable_incr.
  rewrite upd_Znth_Zlength by (apply Z.mod_pos_bound; rep_omega).
  remember (hashfun k mod Zlength ht) as h.
  remember (hashfun j mod Zlength ht) as h'.
  destruct (h =? h') eqn:Heqb;
    [ apply Z.eqb_eq in Heqb | apply Z.eqb_neq in Heqb ].
  2: rewrite upd_Znth_diff; auto; subst h; subst h'; apply Z.mod_pos_bound; rep_omega.
  rewrite <- Heqb. rewrite upd_Znth_same by (subst h; apply Z.mod_pos_bound; rep_omega).
  remember (Znth h ht) as al.
  clear Heqal Heqb Heqh Heqh' h h' H0 Heqht ht t.
  induction al.
  - (* al = [] *)
    simpl. destruct (EqDec_string j k) eqn:?; auto. contradiction.
  - (* al = .. *)
    simpl. destruct a. destruct (EqDec_string k s) eqn:?.
    + (* k = s *)
      subst s. simpl. destruct (EqDec_string j k) eqn:?; auto; try omega. contradiction.
    + (* k <> s *)
      simpl. destruct (EqDec_string j s) eqn:?; auto; try omega.
 Qed.

End IntHashTable.
