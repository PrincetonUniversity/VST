Require Import FunInd.
Require Import VST.zlist.sublist.
Require Import VST.veric.log_normalize.
Require Import VST.veric.juicy_base.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas (*VST.veric.juicy_mem_ops*).
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.initial_world.
Require Import VST.veric.Clight_initial_world.

Import Clight.

Section mpred.

Context `{!heapGS Σ}.

Lemma rev_prog_vars': forall {F V} vl, rev (@prog_vars' F V vl) = prog_vars' (rev vl).
Proof.
   intros.
   induction vl. simpl; auto.
   destruct a. destruct g.
   simpl. rewrite IHvl.
   clear. induction (rev vl); simpl; intros; auto. destruct a; destruct g; simpl; auto.
    rewrite IHl. auto.
   simpl.
   transitivity (prog_vars' (rev vl) ++ (@prog_vars' F V ((i,Gvar v)::nil))).
    rewrite IHvl. f_equal.
    simpl.
    clear.
    induction (rev vl); simpl; intros; auto.
    destruct a. destruct g.
    auto.
    rewrite <- IHl.
    simpl. auto.
Qed.


Local Notation globals := (ident -> val).

Definition init_data2pred (gv: globals) (d: init_data)  (sh: share) (a: val) : mpred :=
 match d with
  | Init_int8 i => mapsto sh (Tint I8 Unsigned noattr) a (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh (Tint I16 Unsigned noattr) a (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh (Tint I32 Unsigned noattr) a (Vint i)
  | Init_int64 i => mapsto sh (Tlong Unsigned noattr) a (Vlong i)
  | Init_float32 r =>  mapsto sh (Tfloat F32 noattr) a (Vsingle r)
  | Init_float64 r =>  mapsto sh (Tfloat F64 noattr) a (Vfloat r)
  | Init_space n => mapsto_zeros n sh a
  | Init_addrof symb ofs =>
        match gv symb with
        | Vptr b i => mapsto sh (Tpointer Tvoid noattr) a (Vptr b (Ptrofs.add i ofs))
        | _ => mapsto_ sh (Tpointer Tvoid noattr) a
        end 
 end.

Fixpoint init_data_list2pred  (gv: globals)  (dl: list init_data)
                           (sh: share) (v: val) : mpred :=
  match dl with
  | d::dl' => init_data2pred gv d sh v ∗
                  init_data_list2pred gv dl' sh (offset_val (init_data_size d) v)
  | nil => emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Ers else Ews.

Definition globals_of_env (rho: environ) (i: ident) : val := 
  match Map.get (ge_of rho) i with Some b => Vptr b Ptrofs.zero | None => Vundef end.

Definition globvar2pred (gv: ident->val) (idv: ident * globvar type) : mpred :=
   if (gvar_volatile (snd idv))
                       then  True
                       else    init_data_list2pred gv (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) (gv (fst idv)).


Definition globvars2pred (gv: ident->val) (vl: list (ident * globvar type)) : mpred :=
   [∗] (map (globvar2pred gv) vl).

Lemma big_sepL_rev : forall {A} (f : A -> mpred) (l : list A), ([∗ list] v ∈ (rev l), f v) ⊣⊢ [∗ list] v ∈ l, f v.
Proof.
  induction l; simpl; first done.
  rewrite big_sepL_app IHl /=.
  rewrite right_id comm //.
Qed.

Lemma globvars2pred_rev:
  forall gv l, globvars2pred gv (rev l) ⊣⊢ globvars2pred gv l.
Proof.
  intros; rewrite /globvars2pred map_rev big_sepL_rev //.
Qed.

(*Lemma writable_blocks_rev:
  forall rho l, writable_blocks l rho = writable_blocks (rev l) rho.
Proof.
induction l; simpl; auto.
destruct a.
rewrite writable_blocks_app.
rewrite <- IHl.
simpl.
rewrite sepcon_emp.
apply sepcon_comm.
Qed.*)

Lemma add_variables_nextblock:
  forall F V vl (ge: Genv.t F V) i g ul, list_norepet (map (@fst _ _) (vl++(i,g)::ul)) ->
   Genv.find_symbol (Genv.add_globals ge (vl++(i,g)::ul)) i =
          Some (Genv.advance_next vl (Genv.genv_next ge)).
Proof.
 induction vl; intros.
 inv H. clear H3. simpl.
 change positive with block.
 replace (Some (Genv.genv_next ge)) with (Genv.find_symbol (Genv.add_global ge (i,g)) i).
 2:{
  unfold Genv.add_global, Genv.find_symbol; simpl. rewrite Maps.PTree.gss. f_equal; unfold block; lia.
  }
  forget (Genv.add_global ge (i, g)) as ge1.
  revert H2 ge1; induction ul; simpl; intros; auto.
  spec IHul; [tauto |].
  rewrite IHul.
  unfold Genv.find_symbol, Genv.add_global. simpl.
  rewrite Maps.PTree.gso; auto.
  simpl length. simpl Genv.advance_next.
  simpl.
  rewrite (IHvl  (Genv.add_global ge a) i g ul).
  f_equal.
  simpl in H. inv H; auto.
Qed.

Definition load_store_init_data1 (ge: Genv.t fundef type) (m: mem) (b: block) (p: Z) (d: init_data) : Prop :=
  match d with
  | Init_int8 n =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
  | Init_int16 n =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
  | Init_int32 n =>
      Mem.load Mint32 m b p = Some(Vint n)
  | Init_int64 n =>
      Mem.load Mint64 m b p = Some(Vlong n)
  | Init_float32 n =>
      Mem.load Mfloat32 m b p = Some(Vsingle n)
  | Init_float64 n =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
  | Init_addrof symb ofs =>
      Mem.load Mptr m b p = Some
             match Genv.find_symbol ge symb with
                | Some b' => Vptr b' ofs
                | None => Vint Int.zero
              end
  | Init_space n =>
      forall z, 0 <= z < Z.max n 0 ->
           Mem.load Mint8unsigned m b (p+z) = Some (Vint Int.zero)
  end.

Definition initializer_aligned (z: Z) (d: init_data) : bool :=
  match d with
  | Init_int16 n => Zeq_bool (z mod 2) 0
  | Init_int32 n => Zeq_bool (z mod 4) 0
  | Init_int64 n => Zeq_bool (z mod 8) 0
  | Init_float32 n =>  Zeq_bool (z mod 4) 0
  | Init_float64 n =>  Zeq_bool (z mod 8) 0
  | Init_addrof symb ofs =>  Zeq_bool (z mod (size_chunk Mptr)) 0
  | _ => true
  end.

Fixpoint initializers_aligned (z: Z) (dl: list init_data) : bool :=
  match dl with
  | nil => true
  | d::dl' => andb (initializer_aligned z d) (initializers_aligned (z + init_data_size d) dl')
  end.

Lemma init_data_list_size_pos: forall dl, init_data_list_size dl >= 0.
Proof. induction dl; simpl; intros. lia.
 pose proof (init_data_size_pos a); lia.
Qed.

Remark store_zeros_load_outside:
  forall m b p n m',
  store_zeros m b p n = Some m' ->
  forall chunk b' p',
  b' <> b \/ p' + size_chunk chunk <= p \/ p + n <= p' ->
  Mem.load chunk m' b' p' = Mem.load chunk m b' p'.
Proof.
  intros until n.  functional induction (store_zeros m b p n); intros.
  inv H; auto.
  transitivity (Mem.load chunk m' b' p').
  apply IHo. auto. intuition lia.
  eapply Mem.load_store_other; eauto. simpl. intuition lia.
  discriminate.
Qed.

Lemma load_store_zeros:
  forall m b z N m', store_zeros m b z N = Some m' ->
         forall z', z <= z' < z + N -> load Mint8unsigned m' b z' = Some (Vint Int.zero).
Proof.
 intros.
 symmetry in H; apply R_store_zeros_correct in H.
  remember (Some m') as m1.
  revert z'  m' Heqm1 H0; induction H; intros. lia.
  subst _res.
 destruct (Z.eq_dec z' p).
 2:{ apply IHR_store_zeros; auto.
   clear - H0 n0.  destruct H0. lia.
  }
  subst z'.
  destruct (load_store_similar _ _ _ _ _ _ e0) with Mint8unsigned; simpl; auto.
  lia.
  destruct H1.
 simpl in H2. subst x.
  replace (Int.zero_ext 8 Int.zero) with (Int.zero) in H1 by reflexivity.
  rewrite <- H1.
  clear - H. apply R_store_zeros_complete in H.
 symmetry.
 symmetry in H; symmetry; eapply store_zeros_load_outside; eauto.
 right. simpl; lia.
  inv Heqm1.
Qed.

Lemma read_as_zero_lem1:
 forall m b z len,
  (forall i, z <= i < z+len ->
     load Mint8unsigned m b i = Some (Vint Int.zero)) ->
  Genv.read_as_zero m b z len.
Proof.
intros; hnf; intros.
transitivity
  (Some (decode_val chunk (repeat (Byte Byte.zero) (size_chunk_nat chunk)))).
2: destruct chunk; (
     simpl repeat;
     cbv delta [decode_val decode_int proj_bytes rev_if_be rev] iota beta zeta;
     try rewrite Tauto.if_same;
     reflexivity).
apply loadbytes_load; auto.
clear H2.
rewrite -> size_chunk_conv in *.
forget (size_chunk_nat chunk) as n.
assert (forall i, p <= i < p + (Z.of_nat n) ->
                     loadbytes m b i 1 = Some (Byte Byte.zero::nil)).
intros.
specialize (H i).
spec H; [ lia |].
apply load_loadbytes in H.
destruct H as [j [? ?]].
destruct j; inv H3;
 try solve [apply loadbytes_length in H;inv H].
destruct j; inv H5;
 try solve [apply loadbytes_length in H;inv H].
destruct m0; try solve [inv H4].
rewrite (decode_byte_val i0) in H4.
simpl in H.
rewrite H. repeat f_equal.
clear - H4.
rewrite zero_ext_inrange in H4.
assert (Int.unsigned Int.zero = Int.unsigned (Int.repr (Byte.unsigned i0))) by congruence.
rewrite Int.unsigned_zero in H.
rewrite Int.unsigned_repr in H.
assert (Byte.repr 0 = Byte.repr (Byte.unsigned i0)) by congruence.
rewrite Byte.repr_unsigned in H0.
rewrite <- H0. reflexivity.
clear.
pose proof (Byte.unsigned_range i0).
destruct H;
 split; auto.
apply Z.le_trans with Byte.modulus.
lia.
compute; congruence.
rewrite Int.unsigned_repr.
pose proof (Byte.unsigned_range i0).
change (two_p 8) with Byte.modulus; lia.
pose proof (Byte.unsigned_range i0).
assert (Byte.modulus < Int.max_unsigned) by (compute; congruence).
lia.
clear - H2.
revert p H2; induction n; intros.
simpl.
apply loadbytes_empty. lia.
rewrite inj_S. unfold Z.succ.
rewrite Z.add_comm.
change (repeat (Byte Byte.zero) (S n)) with
 (repeat (Byte Byte.zero) 1 ++ repeat (Byte Byte.zero) n).
apply loadbytes_concat.
apply H2. rewrite inj_S; lia.
apply IHn.
intros.
apply H2.  rewrite inj_S; lia.
lia. lia.
Qed.

Remark store_init_data_outside:
  forall {F V} genv b i m p m',
  @Genv.store_init_data F V genv m b p i = Some m' ->
  forall chunk b' q,
  b' <> b \/ q + size_chunk chunk <= p \/ p + init_data_size i <= q ->
  Mem.load chunk m' b' q = Mem.load chunk m b' q.
Proof.
  intros. destruct i; simpl in *;
  try (eapply Mem.load_store_other; eauto; fail).
  inv H; auto.
  destruct (Genv.find_symbol genv i); try congruence.
  eapply Mem.load_store_other; eauto; intuition.
Qed.

Remark store_init_data_list_outside:
  forall {F V} genv b il m p m',
  @Genv.store_init_data_list F V genv m b p il = Some m' ->
  forall chunk b' q,
  b' <> b \/ q + size_chunk chunk <= p ->
  Mem.load chunk m' b' q = Mem.load chunk m b' q.
Proof.
  induction il; simpl.
  intros; congruence.
  intros. destruct (Genv.store_init_data genv m b p a) as [m1|] eqn:?; try congruence.
  transitivity (Mem.load chunk m1 b' q).
  eapply IHil; eauto. generalize (init_data_size_pos a). intuition lia.
  eapply store_init_data_outside; eauto. tauto.
Qed.

Lemma store_zeros_0 : forall m b o, store_zeros m b o 0 = Some m.
Proof.
  intros; rewrite store_zeros_equation.
  destruct (zle 0 0); done.
Qed.

Lemma store_zeros_add : forall m b o z1 z2 m', z1 >= 0 -> z2 >= 0 -> store_zeros m b o (z1 + z2) = Some m' ->
  exists m'', store_zeros m b o z1 = Some m'' /\ store_zeros m'' b (o + z1) z2 = Some m'.
Proof.
  intros until 1; revert m o z2.
  eapply (natlike_ind (fun z1 => ∀ (m : Memory.mem) (o z2 : Z) (Hz2 : z2 >= 0) (Hstore : store_zeros m b o (z1 + z2) = Some m'),
    ∃ m'' : Memory.mem, (store_zeros m b o z1 = Some m'' ∧ store_zeros m'' b (o + z1) z2 = Some m'))%type); last lia; intros.
  - rewrite Z.add_0_l in Hstore; rewrite Z.add_0_r store_zeros_0; eauto.
  - rewrite store_zeros_equation in Hstore.
    destruct (zle _ _); first lia.
    destruct (store Mint8unsigned m b o Vzero) eqn: Hstore1; last done.
    replace (Z.succ x + z2 - 1) with (x + z2) in Hstore by lia.
    apply H1 in Hstore as (m'' & ? & ?); last done.
    exists m''; split.
    + rewrite store_zeros_equation.
      destruct (zle _ _); first lia.
      rewrite Hstore1.
      replace (Z.succ x - 1) with x by lia; done.
    + replace (o + Z.succ x) with (o + 1 + x) by lia; done.
Qed.

Lemma load_store_init_data_lem1:
  forall {ge m1 b D m2 m3},
   store_zeros m1 b 0 (init_data_list_size D) = Some m2 ->
   Genv.store_init_data_list ge m2 b 0 D = Some m3 ->
   forall dl' a dl, dl' ++ a :: dl = D ->
   load_store_init_data1 ge m3 b (init_data_list_size dl') a.
Proof.
  intros.
  pose proof (Genv.store_init_data_list_charact _ _ H0).
  subst D.
  change (init_data_list_size dl') with (0 + init_data_list_size dl').
  forget 0 as z.
  assert (forall z', z <= z' < z + init_data_list_size (dl' ++ a :: dl) ->
               Mem.load Mint8unsigned m2 b z' = Some (Vint Int.zero))
    by (eapply load_store_zeros; eauto).
  clear H m1.
  revert z m2 H0 H1 H2; induction dl'; intros.
  simpl app in *. simpl init_data_list_size in *.
  replace (z+0) with z by lia.
  simpl in H0.
  invSome.
  spec H2. {
    clear - H1.
    apply read_as_zero_lem1; intros; apply H1.
    lia.
  }
  destruct a; simpl in H2|-*; try solve [destruct H2; auto]; intros.
  rewrite -> (store_init_data_list_outside _ _ _ _ _ _ H4) by (right; simpl; lia).
  simpl in H0. inv H0. apply H1.
  simpl.
  pose proof (init_data_list_size_pos dl).
  lia.
  destruct H2 as [[b' [? ?]] ?].
  rewrite H. auto.
  simpl.
  simpl in H0. invSome.
  rewrite Zplus_assoc. apply IHdl' with m; auto.
  intros.
  rewrite <- (H1 z').
  destruct (store_init_data_list_outside' _ _ ge b (a0::nil) m2 z m).
  simpl. rewrite H0; auto.
  destruct (H3 b z').
  destruct H6. simpl in H7. lia.
  destruct H5. clear - H6 H5; unfold access_at,contents_at in *.
  Transparent load. unfold load. Opaque load.
  simpl in *. rewrite H6.
  destruct (valid_access_dec m Mint8unsigned b z' Readable);
   destruct (valid_access_dec m2 Mint8unsigned b z' Readable);
  unfold valid_access in *; try congruence.
  contradiction n. clear - v H5.
  unfold range_perm, perm in *.
  destruct v; split; auto; intros.
  apply (equal_f ) with (b,ofs) in H5. apply equal_f with Cur in H5. simpl in H5.
  rewrite H5; auto.
  contradiction n. clear - v H5.
  unfold range_perm, perm in *.
  destruct v; split; auto; intros.
  apply (equal_f ) with (b,ofs) in H5.  apply equal_f with Cur in H5. simpl in H5. rewrite <- H5; auto.
  simpl.
  pose proof (init_data_size_pos a0).
  lia.
  simpl app in H2.
  spec H2. {
     clear - H1.
     apply read_as_zero_lem1; intros.
     apply H1. simpl; auto.
  }
  clear - H2.
  forget (dl'++a::dl) as D.
  simpl in H2. destruct a0; simpl in *; try solve [destruct H2; auto]; intros.
Qed.

Lemma zero_ext_inj: forall i,
   Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.zero ->
   i = Byte.zero.
Proof.
intros.
assert (MU: 256 < Int.max_unsigned).
 unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
  unfold two_power_nat, shift_nat in *; simpl in *.
 replace (Zpos (4294967296 - 1)) with (4294967295). lia. reflexivity.
rewrite -> Int.zero_ext_and in H by lia.
pose proof (Int.modu_and (Int.repr (Byte.unsigned i)) (Int.repr (two_p 8)) (Int.repr 8)).
 spec H0.
 apply Int.is_power2_two_p; simpl. by compute.
 replace (Int.sub (Int.repr (two_p 8)) Int.one) with (Int.repr (two_p 8 - 1)) in H0.
 rewrite <- H0 in H. clear H0.
 rewrite Int.modu_divu in H.
 replace (Int.divu (Int.repr (Byte.unsigned i)) (Int.repr (two_p 8))) with Int.zero in H.
 rewrite Int.sub_zero_l in H.
 pose proof (Int.unsigned_repr (Byte.unsigned i)).
 assert (Int.unsigned (Int.repr (Byte.unsigned i)) = Int.unsigned Int.zero).
 rewrite H; auto.
 rewrite H0 in H1.
 clear - MU H1. rewrite Int.unsigned_zero in H1.
rewrite <- (Byte.repr_unsigned i). unfold Byte.zero. f_equal. auto.
 clear - MU. pose proof (Byte.unsigned_range i).
 unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize in *.
  unfold two_power_nat, shift_nat in *; simpl in *. lia.
 clear - MU.
 unfold Int.divu. unfold Int.zero. f_equal.
 symmetry. apply Zdiv_small.
 split.
 destruct (Int.unsigned_range (Int.repr (Byte.unsigned i))); auto.
 repeat rewrite Int.unsigned_repr.
 destruct (Byte.unsigned_range i).
 apply H0. simpl.  unfold two_power_pos, shift_pos; simpl. lia.
 destruct (Byte.unsigned_range i).
 split; auto. replace Byte.modulus with 256 in H0 by reflexivity. lia.
 clear - MU. replace (two_p 8) with 256 by reflexivity.
 unfold Int.zero. intro.
 pose proof (Int.unsigned_repr 256).
 spec H0. split; lia.
 rewrite H in H0. rewrite -> Int.unsigned_repr in H0 by lia. inv H0.
 replace (two_p 8) with 256 by reflexivity.
 unfold Int.one.
 rewrite Int.sub_signed.
 pose proof (Int.min_signed_neg).
 assert (Int.max_signed = 2147483647).
 clear.  unfold Int.max_signed, Int.half_modulus, Int.modulus, Int.wordsize, two_power_nat; simpl.
 reflexivity.
  repeat rewrite Int.signed_repr; auto;  split; try lia.
Qed.

Lemma max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof.
 unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
  simpl. unfold shift_nat. simpl. reflexivity.
Qed.

(*Lemma decode_val_getN_lem1:
  forall j i b,
          decode_val Mint32 (getN 4 i b) = Vint Int.zero ->
          0 <= j-i < 4 ->
          nth (Z.to_nat (j-i)) (getN 4 i b) Undef = Byte Byte.zero.
Proof.
 intros.
 unfold decode_val in H.
 revert H; case_eq (getN 4 i b); intros. inv H.
 unfold getN in H. destruct l; inv H.
 destruct (proj_bytes
         (Maps.ZMap.get i b
          :: Maps.ZMap.get (i + 1) b
             :: Maps.ZMap.get (i + 1 + 1) b :: ZMap.get (i + 1 + 1 + 1) b :: nil))
    eqn:PB.
*
 simpl proj_bytes in PB.
 destruct (ZMap.get i b); inv PB.
 destruct (ZMap.get (i+1) b); inv H2.
 destruct (ZMap.get (i+1+1) b); inv H3.
 destruct (ZMap.get (i+1+1+1) b); inv H2.
 unfold decode_int in H1.
 assert (Int.repr (int_of_bytes (rev_if_be (i0 :: i1 :: i2 :: i3 :: nil))) = Int.repr 0) by
    (forget (Int.repr (int_of_bytes (rev_if_be (i0 :: i1 :: i2 :: i3 :: nil)))) as foo; inv H1; auto).
 clear H1.
 assert (forall b0 b1 b2 b3, Int.repr (int_of_bytes (b0::b1::b2::b3::nil)) = Int.repr 0 ->
      (Byte.unsigned b0=0/\Byte.unsigned b1=0/\Byte.unsigned b2=0/\Byte.unsigned b3=0)).
 clear. intros.
   simpl in H.
  pose proof (Byte.unsigned_range b0).
  pose proof (Byte.unsigned_range b1).
  pose proof (Byte.unsigned_range b2).
  pose proof (Byte.unsigned_range b3).
  replace (Byte.modulus) with 256 in * by reflexivity.
  pose proof (Int.unsigned_repr  (Byte.unsigned b0 +
       (Byte.unsigned b1 +
        (Byte.unsigned b2 + (Byte.unsigned b3 + 0) * 256) * 256) * 256)).
  spec H4.
  clear H. rewrite max_unsigned_eq; lia.
  rewrite H in H4.
 rewrite -> Int.unsigned_repr in H4 by (rewrite max_unsigned_eq; lia).
  lia.
 assert (Byte.unsigned i0=0/\Byte.unsigned i1=0/\Byte.unsigned i2=0/\Byte.unsigned i3=0).
 unfold rev_if_be in H. destruct Archi.big_endian; simpl in H; apply H1 in H; tauto.
 clear H1 H.
  assert (forall i, Byte.unsigned i = 0 -> i = Byte.zero).
  clear. intros. pose proof (Byte.repr_unsigned i). rewrite H in H0. symmetry; auto.
 destruct H2 as [? [? [? ?]]]. apply H in H1; apply H in H2; apply H in H3; apply H in H4.
 subst.
 assert (j-i=0 \/ j-i=1 \/ j-i=2 \/ j-i=3) by lia.
 destruct H1 as [? | [?|[?|?]]]; rewrite H1; simpl; auto.
*
 unfold proj_value in H1.
 unfold Val.load_result in H1.
 clear PB.
 destruct (ZMap.get i b); inv H1.
(* Not true if Archi.ptr64=false *)
Abort.*)

Lemma Zmax_Z_of_nat:
 forall n, Z.max (Z_of_nat n) 0 = Z_of_nat n.
Proof.
intros.
apply Z.max_l.
lia.
Qed.

Lemma snd_split_fullshare_not_bot: snd (Share.split fullshare) <> Share.bot.
Proof.
intro.
case_eq (Share.split fullshare); intros.
rewrite H0 in H. simpl in H. subst.
apply Share.split_nontrivial in H0; auto.
by apply Share.nontrivial.
Qed.

Lemma readable_readonly2share: forall ro, readable_share (readonly2share ro).
Proof.
  intros.
  unfold readable_share. intro.
  apply identity_share_bot in H.
  assert (H9: Share.Rsh <> Share.bot). {
    unfold Share.Rsh. intro.
    destruct (Share.split Share.top) eqn:?.
    pose proof (Share.split_nontrivial _ _ _ Heqp). spec H1; auto; contradiction Share.nontrivial.
  }
  clear H9.
  destruct ro; simpl in *.
  unfold Ers in H.
  rewrite Share.distrib1 in H.
  apply lub_bot_e in H. destruct H as [_ ?].
  rewrite glb_split_x in H.
  destruct (Share.split Share.Rsh) eqn:H0. simpl in *.
  subst.
  pose proof (Share.split_nontrivial _ _ _ H0). spec H; auto.
  apply snd_split_fullshare_not_bot in H. auto.
  unfold Ews in H.
  rewrite Share.distrib1 in H.
  apply lub_bot_e in H. destruct H as [_ ?].
  rewrite Share.glb_idem in H.
  apply snd_split_fullshare_not_bot in H. auto.
Qed.

Definition genviron2globals (g: genviron) (i: ident) : val :=
  match Map.get g i with Some b => Vptr b Ptrofs.zero | None => Vundef end.

Lemma getN_seq : forall n z c, getN n z c = map (fun i => Maps.ZMap.get (z + Z.of_nat i) c) (seq 0 n).
Proof.
  induction n; simpl; intros; first done.
  rewrite Z.add_0_r IHn -seq_shift map_map.
  f_equal; apply map_ext; intros.
  f_equal; lia.
Qed.

Lemma init_data_lem:
forall (ge: genv) (v : globvar type) (b : block)
  (m3 : Memory.mem) G (a : init_data) (z : Z),
   load_store_init_data1 ge m3 b z a ->
  forall (Haccess : forall loc, adr_range (b, z) (init_data_size a) loc -> access_at m3 loc Cur = Some (Genv.perm_globvar v))
    (VOL:  gvar_volatile v = false)
    (AL: initializer_aligned z a = true)
    (LO: 0 <= z) (HI: z + init_data_size a < Ptrofs.modulus),
([∗ list] y ∈ seq (Z.to_nat z) (Z.to_nat (init_data_size a)), inflate_loc m3 ge G (b, 0 + Z.of_nat y)) ⊢
init_data2pred (genviron2globals (filter_genv ge)) a (readonly2share (gvar_readonly v))
  (Vptr b (Ptrofs.repr z)).
Proof.
  intros.
  assert (APOS:= init_data_size_pos a).
  assert (READABLE:= readable_readonly2share (gvar_readonly v)).
  unfold init_data2pred, mapsto; simpl.
  destruct (readable_share_dec _); last done.
  unfold mapsto_zeros, address_mapsto, res_predicates.address_mapsto, fst, snd.
  rewrite -> Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  unfold mapsto, tc_val, is_int, is_long, is_float.
  rewrite -(Nat.add_0_r (Z.to_nat z)) -fmap_add_seq big_sepL_fmap.
  rewrite (big_sepL_proper _ (fun _ y => adr_add (b, z) (Z.of_nat y) ↦{#readonly2share (gvar_readonly v)} VAL (contents_at m3 (b, z + Z.of_nat y)))).
Transparent load.
  iIntros "H"; destruct a; repeat rewrite -> prop_true_andp by 
    first [apply I
            | apply sign_ext_range'; compute; split; congruence
            | apply zero_ext_range'; compute; split; congruence
            ];
  try iLeft; simpl in H; unfold load in H;
  try (if_tac in H; [ | discriminate H]);
  repeat rewrite -> prop_true_andp by apply I;
  try match type of H with Some (decode_val ?ch ?B) = Some (?V) =>
            iExists B; replace V with (decode_val ch B) by (inversion H; auto);
            clear H
       end; try (iSplit; last (by simpl; rewrite ?Z.add_0_r -?Z.add_assoc);
                 iPureIntro; repeat split; auto; try solve [apply Zmod_divide; [intro Hx; inv Hx | apply Zeq_bool_eq; auto]]).
Opaque load.
* (* Int8 *)
  apply Zone_divide.
* (* Float64 *)
  clear - AL.
  simpl in AL. apply Zmod_divide. intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  rewrite <- Zeq_is_eq_bool in *; simpl.
  apply Zmod_divides; [ lia | ].
  apply Zmod_divides in AL; [ | lia].
  destruct AL as [c ?]. exists (2 * c)%Z. rewrite Z.mul_assoc. apply H.
* (* address_mapsto_zeros *)
  rewrite address_mapsto_zeros_eq /=.
  iSplit.
  { iPureIntro; split; auto. simpl in HI. clear - HI. destruct (Z.max_spec z0 0); destruct H; lia. }
  rewrite Z_to_nat_max; iApply (big_sepL_mono with "H").
  intros ?? (-> & ?)%lookup_seq; simpl.
  assert (contents_at m3 (b, z + Z.of_nat k) = Byte Byte.zero) as ->; last done.
  specialize (H (Z.of_nat k)).
  spec H; first lia.
  if_tac in H; inv H.
  rewrite /decode_val /= in H3.
  rewrite /contents_at.
  destruct (Maps.ZMap.get _ _); try done.
  rewrite /decode_int in H3.
  replace (rev_if_be [i]) with [i] in H3 by (unfold rev_if_be; destruct Archi.big_endian; auto).
  rewrite /= Z.add_0_r in H3.
  f_equal; apply zero_ext_inj; congruence.
* (* symbol case *)
  injection H as H.
  rewrite /genviron2globals /filter_genv /Map.get.
  assert (align_chunk Mptr | z).
  { simpl in AL. apply Zmod_divide. intro Hx; inv Hx. apply Zeq_bool_eq; auto. }
  destruct (Genv.find_symbol (genv_genv ge) i) eqn: Hi.
  + iLeft. iSplit; first done. rewrite Ptrofs.add_zero_l.
    iExists (getN (size_chunk_nat Mptr) z (Maps.PMap.get b (mem_contents m3))).
    iSplit; first by iPureIntro.
    rewrite getN_seq (big_sepL_fmap _ _ (seq 0 (size_chunk_nat Mptr))).
    replace (Z.to_nat (init_data_size (Init_addrof i i0))) with (size_chunk_nat Mptr)
      by (rewrite /Mptr /=; simple_if_tac; done).
    done.
  + erewrite mapsto__exp_address_mapsto by (auto; reflexivity).
    rewrite exp_address_mapsto_VALspec_range_eq.
    rewrite -> Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with (Ptrofs.modulus-1); lia).
    iSplit; first by iPureIntro.
    rewrite /VALspec_range.
    replace (Z.to_nat (init_data_size (Init_addrof i i0))) with (size_chunk_nat Mptr)
      by (rewrite /Mptr /=; simple_if_tac; done).
    iApply (big_sepL_mono with "H"); intros.
    rewrite /VALspec; eauto.
* intros ?? (-> & ?)%lookup_seq.
  rewrite /= Z.add_0_l Nat2Z.inj_add Z2Nat.id //.
  rewrite /inflate_loc Haccess; last by split; auto; lia.
  rewrite /readonly2share /Genv.perm_globvar VOL; simple_if_tac; done.
Qed.

Lemma init_data_list_size_app:
  forall dl1 dl2, init_data_list_size (dl1++dl2) =
                   init_data_list_size dl1 + init_data_list_size dl2.
Proof. induction dl1; intros; simpl; auto. rewrite IHdl1; lia.
Qed.


Lemma max_unsigned_modulus:
  Ptrofs.max_unsigned + 1 = Ptrofs.modulus.
Proof.
 unfold Ptrofs.max_unsigned. lia.
Qed.

Lemma drop_perm_contents : forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  contents_at m = contents_at m'.
Proof.
  rewrite /drop_perm; intros.
  destruct (range_perm_dec _ _ _ _ _ _); inv H; done.
Qed.

Lemma drop_perm_access : forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall l k, access_at m' l k = if adr_range_dec (b, lo) (hi - lo) l then Some p else access_at m l k.
Proof.
  rewrite /drop_perm; intros.
  destruct (range_perm_dec _ _ _ _ _ _); inv H.
  rewrite /access_at /=.
  destruct l as (b0, z); if_tac.
  - destruct H; subst.
    rewrite Maps.PMap.gss /=.
    destruct (zle lo z); simpl; last lia.
    destruct (zlt z hi); simpl; last lia; done.
  - destruct (eq_dec b0 b); last by rewrite Maps.PMap.gso.
    subst; rewrite Maps.PMap.gss /=.
    destruct (zle lo z); last done.
    destruct (zlt z hi); last done.
    contradiction H; split; auto; lia.
Qed.

Lemma store_zeros_other_block : forall m b lo hi m' b', store_zeros m b lo hi = Some m' ->
  b' ≠ b -> Maps.PMap.get b' (mem_contents m') = Maps.PMap.get b' (mem_contents m).
Proof.
  eapply (store_zeros_ind (fun m b p n m1 => forall m' b', m1 = Some m' -> b' ≠ b ->
    Maps.PMap.get b' (mem_contents m') = Maps.PMap.get b' (mem_contents m))); intros.
  - by inv H.
  - eapply H in H0 as ->; last done.
    apply store_mem_contents in e0 as ->.
    rewrite Maps.PMap.gso //.
  - done.
Qed.

Lemma store_init_data_list_other_block : forall {F V} ge m b o dl m' b', Genv.store_init_data_list(F := F)(V := V) ge m b o dl = Some m' ->
  b' ≠ b -> Maps.PMap.get b' (mem_contents m') = Maps.PMap.get b' (mem_contents m).
Proof.
  intros until dl; revert m o.
  induction dl; simpl; intros; first congruence.
  destruct (Genv.store_init_data) eqn: Hd; last done.
  eapply IHdl in H as ->; last done.
  unfold Genv.store_init_data in Hd.
  destruct a; try solve [erewrite store_mem_contents by eassumption; rewrite Maps.PMap.gso //].
  - by inv Hd.
  - destruct (Genv.find_symbol ge i); last done.
    erewrite store_mem_contents by eassumption; rewrite Maps.PMap.gso //.
Qed.

Lemma init_data_list_lem':
forall (ge: genv) G (v : globvar type) (b : block)
  (m : Memory.mem) (a dl0 : list init_data),
   Genv.load_store_init_data ge m b (init_data_list_size dl0) a ->
   forall (Haccess: forall loc, adr_range (b, init_data_list_size dl0) (init_data_list_size a) loc -> access_at m loc Cur = Some (Genv.perm_globvar v))
     (Hinit: ∀ (dl' : list init_data) (a1 : init_data) (dl : list init_data),
       dl' ++ a1 :: dl = dl0 ++ a
       → load_store_init_data1 (genv_genv ge) m b (init_data_list_size dl') a1)
     (VOL:  gvar_volatile v = false)
     (AL: initializers_aligned (init_data_list_size dl0) a = true)
     (HI: init_data_list_size dl0 + init_data_list_size a < Ptrofs.modulus),
([∗ list] o ∈ seq (Z.to_nat (init_data_list_size dl0)) (Z.to_nat (init_data_list_size a)), inflate_loc m ge G (b, 0 + Z.of_nat o)) ⊢
init_data_list2pred (genviron2globals (filter_genv ge)) a (readonly2share (gvar_readonly v))
  (Vptr b (Ptrofs.repr (init_data_list_size dl0))).
Proof.
  induction a as [|a la]; simpl; intros; first done.
  apply andb_true_iff in AL as [??].
  iIntros "H".
  assert (0 <= init_data_size a) by (pose proof (init_data_size_pos a); lia).
  assert (0 <= init_data_list_size la) by (pose proof (init_data_list_size_pos la); lia).
  assert (0 <= init_data_list_size dl0) by (pose proof (init_data_list_size_pos dl0); lia).
  rewrite Z2Nat.inj_add // seq_app big_sepL_app.
  specialize (IHla (dl0 ++ [a])); rewrite init_data_list_size_app /= Z.add_0_r in IHla.
  rewrite -Z2Nat.inj_add // IHla //; try lia.
  rewrite /Ptrofs.add !Ptrofs.unsigned_repr; [| rewrite /Ptrofs.max_unsigned; lia..].
  iDestruct "H" as "(H & $)".
  iApply (init_data_lem with "H"); try assumption.
  - by eapply Hinit.
  - intros (?, ?) (? & ?); apply Haccess; lia.
  - lia.
  - destruct a; tauto.
  - intros (?, ?) (? & ?); apply Haccess; lia.
  - intros ???; rewrite -app_assoc; eauto.
Qed.

Lemma load_store_init_data1_invariant: ∀ ge (m m' : Memory.mem) (b : block),
         (∀ (chunk : memory_chunk) (ofs : Z), load chunk m' b ofs = load chunk m b ofs)
         → ∀ (i : init_data) (p : Z),
             load_store_init_data1 ge m b p i → load_store_init_data1 ge m' b p i.
Proof.
  destruct i; simpl; intros; rewrite H //; eauto.
Qed.

Lemma init_data_list_lem:
  forall (ge: genv) m0 (v: globvar type) m1 b m2 m3 m4,
     alloc m0 0 (init_data_list_size (gvar_init v)) = (m1,b) ->
     store_zeros m1 b 0 (init_data_list_size (gvar_init v)) = Some m2 ->
     Genv.store_init_data_list ge m2 b 0 (gvar_init v) = Some m3 ->
     drop_perm m3 b 0 (init_data_list_size (gvar_init v))
               (Genv.perm_globvar v) = Some m4 ->
  forall {F} (gl : list (ident * globdef F _)) i G
   (SANITY: init_data_list_size (gvar_init v) < Ptrofs.modulus)
   (AL: initializers_aligned 0 (gvar_init v) = true)
   (Hgl: nextblock m0 = Z.to_pos (Z.succ (Zlength gl))),
     inflate_initial_mem m4 (globals_bounds 1 (gl ++ [(i, Gvar v)])) ge G ⊢ inflate_initial_mem m0 (globals_bounds 1 gl) ge G ∗
     if gvar_volatile v then True else init_data_list2pred (genviron2globals (filter_genv ge)) (gvar_init v) (readonly2share (gvar_readonly v)) (Vptr b Ptrofs.zero).
Proof.
  intros.
  rewrite /inflate_initial_mem.
  erewrite nextblock_drop, Genv.store_init_data_list_nextblock, Genv.store_zeros_nextblock, nextblock_alloc by done.
  rewrite Pos2Nat.inj_succ /= Nat.sub_0_r.
  destruct (Pos2Nat.is_succ (nextblock m0)) as (n & Hnext).
  rewrite Hnext seq_S big_sepL_app /=.
  pose proof (alloc_result _ _ _ _ _ H) as ->.
  iIntros "(Hrest & Hb & _)"; iSplitL "Hrest".
  - rewrite Nat.sub_0_r; iApply (big_sepL_mono with "Hrest").
    intros ?? (-> & ?)%lookup_seq.
    rewrite globals_bounds_app1; last by rewrite Zlength_correct in Hgl; lia.
    destruct (globals_bounds _ _ _); apply big_sepL_mono; intros.
    rewrite /drop_perm in H2; destruct range_perm_dec; inv H2; rewrite /inflate_loc /access_at /contents_at /=.
    assert (Pos.of_nat (S k) ≠ nextblock m0) by lia.
    erewrite store_init_data_list_other_block; [| eassumption..].
    erewrite store_zeros_other_block; [| eassumption..].
    erewrite mem_lemmas.AllocContentsOther; [| eassumption..].
    rewrite Maps.PMap.gso //.
    apply (alloc_dry_unchanged_on _ _ (Pos.of_nat (S k), z + y)) in H as (Haccess & Hcontents); last by intros [??].
    rewrite {1}/access_at /= in Haccess; apply equal_f with Cur in Haccess; rewrite Haccess.
    erewrite <- store_zeros_access by eassumption.
    by apply store_init_data_list_outside' in H1 as (Hcontents3 & -> & _).
  - destruct (gvar_volatile v) eqn: VOL; first done.
    rewrite -Hnext Pos2Nat.id.
    pose proof (nth_error_app gl [(i, Gvar v)] O) as Hv.
    replace (base.length gl) with (Pos.to_nat (nextblock m0) - 1)%nat in Hv by (rewrite Zlength_correct in Hgl; lia).
    rewrite Nat.add_0_r /= in Hv.
    erewrite globals_bounds_nth; [| lia | done]; simpl.
    pose proof (load_store_init_data_lem1 H0 H1).
    assert (∀ (chunk : memory_chunk) (ofs : Z), load chunk m4 (nextblock m0) ofs = load chunk m3 (nextblock m0) ofs).
    { intros; eapply load_drop; eauto.
      right; right; right; rewrite /Genv.perm_globvar VOL.
      simple_if_tac; constructor. }
    rewrite seq_app big_sepL_app; iDestruct "Hb" as "(Hb & H1)".
    iAssert emp with "[H1]" as "_".
    { rewrite /inflate_loc /=.
      pose proof (init_data_list_size_pos (gvar_init v)); rewrite Z.add_0_l Z2Nat.id; last lia.
      erewrite <- access_drop_3; [| eauto | lia].
      edestruct store_init_data_list_outside' as (_ & <- & _); first done.
      erewrite store_zeros_access by done.
      erewrite <- alloc_access_other; [| eauto | lia].
      rewrite nextblock_access_empty //; last lia. }
    iApply (init_data_list_lem' _ _ _ _ _ _ [] with "Hb"); try done.
    + eapply Genv.load_store_init_data_invariant, Genv.store_init_data_list_charact; try done.
      eapply Genv.store_zeros_read_as_zero; eauto.
    + intros; erewrite drop_perm_access by done.
      rewrite Z.sub_0_r if_true //.
    + intros; eapply load_store_init_data1_invariant; eauto.
Qed.

Definition all_initializers_aligned (prog: program) :=
  forallb (fun idv => andb (initializers_aligned 0 (gvar_init (snd idv)))
                                 (Zlt_bool (init_data_list_size (gvar_init (snd idv))) Ptrofs.modulus))
                      (prog_vars prog) = true.

Lemma forallb_rev: forall {A} f (vl: list A), forallb f (rev vl) = forallb f vl.
Proof. induction vl; simpl; auto.
  rewrite forallb_app. rewrite IHvl. simpl. rewrite andb_comm.
  rewrite <- andb_assoc. f_equal; auto.
Qed.

Lemma store_init_data_list_access:
  forall  {F V} (ge: Genv.t F V) m b z dl m',
     Genv.store_init_data_list ge m b z dl = Some m' ->
     access_at m = access_at m'.
Proof.
  intros. revert z m m' H; induction dl; simpl; intros.
  inv H; auto.
 invSome.
  transitivity (access_at m0).
  clear - H.
  destruct a; simpl in H;
   try solve [unfold access_at; extensionality loc; rewrite (Mem.store_access _ _ _ _ _ _ H); auto].
  inv H; auto. invSome.
  unfold access_at; extensionality loc; rewrite (Mem.store_access _ _ _ _ _ _ H2); auto.
  eapply IHdl; eauto.
Qed.

Lemma rev_prog_funct': forall {F V} vl, rev (@prog_funct' F V vl) = prog_funct' (rev vl).
Proof.
   intros.
   induction vl. simpl; auto.
   destruct a. destruct g.
   simpl.
   transitivity (prog_funct' (rev vl) ++ (@prog_funct' F V ((i,Gfun f)::nil))).
    rewrite IHvl. f_equal.
    simpl.
    clear.
    induction (rev vl); simpl; intros; auto.
    destruct a. destruct g.
    auto.
    rewrite <- IHl.
    simpl. auto.
    simpl; auto.
    simpl. rewrite IHvl.
    clear.
    induction (rev vl); simpl; intros; auto. destruct a. destruct g.
    f_equal; auto. auto.
Qed.

Transparent alloc.

Lemma alloc_global_beyond2:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, (fst loc > nextblock m)%positive ->
        access_at m' loc Cur = None.
Proof.
 intros.
 destruct loc as [b ofs]; simpl in *.
 unfold access_at, Genv.alloc_global in *.
 destruct iv; destruct g; simpl @fst; simpl @ snd;
 [forget 1 as N |  forget  (init_data_list_size (gvar_init v)) as N];
 revert H; case_eq (alloc m 0 N); intros; repeat invSome;
 match goal with H: drop_perm ?m _ _ _ _ = _ |- _ =>
   unfold drop_perm in H;
  destruct (range_perm_dec m b0 0 N Cur Freeable); inv H
 end;
  inv H; simpl in *;
 repeat rewrite Maps.PMap.gss;
 rewrite -> !Maps.PMap.gso by (intro Hx; inv Hx; unfold Plt in *; lia);
 try (apply nextblock_noaccess; unfold Plt in *; lia).
 apply store_zeros_access in H1.
 apply store_init_data_list_outside' in H4.
 destruct H4 as [? [? ?]]. rewrite H2 in H1.
 change (access_at m2 (b,ofs) Cur = None).
 rewrite H1. unfold access_at; simpl.
 repeat rewrite -> Maps.PMap.gso by (intro Hx; inv Hx; lia).
 apply nextblock_noaccess.
clear - H0.
unfold Plt. lia.
Qed.

Lemma alloc_global_access:
 forall {F V} (ge: Genv.t F V) m i v m', Genv.alloc_global ge m (i, Gvar v) = Some m' ->
  forall z, access_at m' (nextblock m, z) Cur =
                    if range_dec 0 z (init_data_list_size (gvar_init v))
                    then Some (Genv.perm_globvar v) else None.
Proof.
intros.
unfold Genv.alloc_global in H.
forget (init_data_list_size (gvar_init v)) as N.
revert H; case_eq (alloc m 0 N); intros.
invSome. invSome.
unfold drop_perm in H4.
destruct (range_perm_dec m2 b 0 N Cur Freeable); inv H4.
unfold access_at. simpl.
apply store_zeros_access in H0.
apply store_init_data_list_access in H3.
rewrite H0 in H3. clear m1 H0.
inv H. unfold access_at in H3. simpl in *.
apply equal_f with (nextblock m, z) in H3. apply equal_f with Cur in H3.
simpl in H3. rewrite -> Maps.PMap.gss in *.
destruct (zle 0 z). simpl. destruct (zlt z N).
simpl in *.
rewrite if_true; auto. rewrite if_false; auto.
 intros [? ?]. lia.
simpl. rewrite -> if_false by lia.
simpl in H3; auto.
Qed.

Opaque alloc.

Lemma find_id_rev {A}: forall i G,
 list_norepet (map fst G) -> find_id i (rev G) = @find_id A i G.
Proof.
intros.
induction G; simpl; intros; auto.
inv H. destruct a. simpl in *. specialize (IHG H3).
if_tac. subst.
clear - H2.
rewrite In_rev in H2. rewrite <- map_rev in H2.
 induction (rev G); simpl; auto. rewrite if_true; auto.
 destruct a0;  simpl in *.
 if_tac. subst. tauto. apply IHl; tauto.
 rewrite <- IHG. clear IHG.
 clear - H.
 induction (rev G); simpl; auto. rewrite if_false; auto.
 destruct a0; simpl in *. if_tac; auto.
Qed.

Lemma find_id_firstn {A} i fs: forall n G (N: find_id i (firstn n G) = Some fs), @find_id A i G = Some fs.
Proof.
induction n; simpl; intros. inv N.
destruct G; simpl in *. inv N.
destruct p as [j gs]; simpl in *.
destruct (eq_dec i j); subst; trivial. auto.
Qed.

Lemma find_id_skipn {A} i fs: forall n G (HG: list_norepet (map fst G))
                             (N: find_id i (skipn n G) = Some fs), @find_id A i G = Some fs.
Proof.
induction n; simpl; intros; trivial.
destruct G; simpl in *; trivial.
destruct p as [j gs]; simpl in *. inv HG.
destruct (eq_dec i j); [ subst | auto].
apply IHn in N; [clear IHn; exfalso| trivial].
apply find_id_e in N. apply in_map_fst in N; auto.
Qed.

Lemma In_firstn {A} (a:A): forall n l, In a (firstn n l) -> In a l.
Proof.
induction n; simpl; intros. contradiction.
destruct l; inv H. left; trivial. right; auto.
Qed.
Lemma In_skipn {A} (a:A): forall n l, In a (skipn n l) -> In a l.
Proof.
induction n; simpl; intros. trivial. 
destruct l. inv H. right; auto.
Qed.

Definition prog_var_block (rho: environ) (il: list ident) (b: block) : Prop :=
  Exists (fun id => match ge_of rho id with Some b' => b'=b | _ => False%type end) il.

Lemma match_fdecs_in:
  forall i vl G,
     In i (map (@fst _ _) G) ->
     @match_fdecs Σ vl G ->
     In i (map (@fst _ _) vl).
Proof.
 induction vl; simpl; intros; auto.
 inv H0. inv H.
 inv H0.
 destruct H. inv H. simpl; auto.
 right. apply (IHvl G0); auto.
Qed.

Lemma list_norepet_prog_funct':
  forall A B (vl: list (ident * globdef A B)),
        list_norepet (map (@fst _ _) vl) ->
       list_norepet (map (@fst _ _) (prog_funct' vl)).
Proof.
 induction vl; simpl; intros.
 constructor.
 inv H. destruct a as [i [?|?]].
 simpl. constructor; auto.
 simpl in H2. contradict H2.
 clear - H2; induction vl; simpl in *; auto. destruct a.
 destruct g; simpl in *; auto. destruct H2; auto.
 apply IHvl; auto.
Qed.

Lemma match_fdecs_rev':
  forall vl G vl' G',
   list_norepet (map (@fst _ _) (rev vl ++ vl')) ->
   @match_fdecs Σ vl G ->
   match_fdecs vl' G' ->
   match_fdecs (rev vl ++ vl') (rev G ++ G').
Proof.
induction vl; intros.
simpl in *.
destruct G; inv H0. apply H1.
destruct a.
inv H0.
simpl. do 2 rewrite <- app_assoc.
simpl.
apply IHvl.
clear - H.
simpl rev in *.
repeat rewrite map_app in H.
repeat rewrite map_app.
simpl in H|-*.
repeat rewrite map_app in H.
simpl in H.
rewrite list_norepet_app.
repeat rewrite list_norepet_app in H.
decompose [and] H; clear H.
clear H0.
repeat split; auto.
constructor; auto.
intro.
apply (H5 i i); auto.
apply in_app. right; left; auto.
intros j k ? ? ?; subst k.
apply (H5 j j).
rewrite in_app.
destruct H0. right; left; auto.
left; rewrite map_rev -in_rev; auto.
rewrite map_rev -in_rev in H; auto.
destruct H0; auto.
subst j. specialize (H4 i i). contradiction H4; auto.
left; auto.
auto.
auto.
constructor 2; auto.
Qed.

Lemma match_fdecs_rev:
  forall vl G,
   list_norepet (map (@fst _ _) vl) ->
   @match_fdecs Σ (rev vl) (rev G) = match_fdecs vl G.
Proof.
  intros; apply prop_ext; split; intros.
*
  rewrite <- (app_nil_r vl).
  rewrite <- (app_nil_r G).
  rewrite <- (rev_involutive vl), <- (rev_involutive G).
  apply match_fdecs_rev'; auto.
  rewrite rev_involutive app_nil_r; auto.
  constructor.
*
  rewrite <- (app_nil_r (rev vl)).
  rewrite <- (app_nil_r (rev G)).
  apply match_fdecs_rev'; auto.
  rewrite app_nil_r.
  rewrite map_rev. rewrite list_norepet_rev; auto.
  constructor.
Qed.

Lemma initial_core_rev:
  forall m (gev: Genv.t fundef type) G (vl: list (ident * globdef fundef type)),
    list_norepet (map fst G) →
    initial_core m gev G ⊣⊢ initial_core m gev (rev G).
Proof.
  intros.
  rewrite /initial_world.initial_core.
  apply big_sepL_proper; intros.
  rewrite /funspec_of_loc /=.
  destruct (Genv.invert_symbol _ _); last done.
  rewrite find_id_rev //.
Qed.

Lemma inflate_initial_mem_rev:
  forall m bounds (gev: Genv.t fundef type) G (vl: list (ident * globdef fundef type))
    (H: list_norepet (map fst (rev vl)))
    (SAME_IDS : match_fdecs (prog_funct' vl) (rev G)),
    inflate_initial_mem m bounds gev G ⊣⊢ inflate_initial_mem m bounds gev (rev G).
Proof.
  intros.
  rewrite /inflate_initial_mem.
  apply big_sepL_proper; intros.
  destruct (bounds _).
  apply big_sepL_proper; intros.
  rewrite /inflate_loc.
  destruct (access_at _ _ _); last done.
  destruct p; try done.
  rewrite /funspec_of_loc.
  if_tac; try done.
  destruct (Genv.invert_symbol _ _) eqn: Hb; last done.
  rewrite find_id_rev //.
  { rewrite -list_norepet_rev -map_rev -match_fdecs_norepet //.
    apply list_norepet_prog_funct'.
    rewrite -list_norepet_rev -map_rev //. }
Qed.

Lemma Pos_to_nat_eq_S:
  forall b, Pos.to_nat b = S (Z.to_nat (Z.pos b) - 1).
Proof. intros. simpl; pose proof (Pos2Nat.is_pos b); lia.
Qed.

Lemma global_initializers:
  forall (prog: program) G m
     (Hnorepet : list_norepet (prog_defs_names prog))
     (AL : all_initializers_aligned prog)
     (SAME_IDS : match_fdecs (prog_funct prog) G)
     (Hinit : Genv.init_mem prog = Some m),
    inflate_initial_mem m (block_bounds prog) (globalenv prog) G ⊢
    globvars2pred (genviron2globals (filter_genv (globalenv prog))) (prog_vars prog).
Proof.
  intros.
  set (gp := globalenv prog).
  unfold all_initializers_aligned in AL.
  unfold Genv.init_mem in Hinit.
  unfold globalenv, Genv.globalenv in *.
  unfold prog_vars, prog_funct in *.
  change (prog_defs prog) with (AST.prog_defs prog) in AL, SAME_IDS |- *.
  destruct (program_of_program prog) as [fl prog_pub main].
  forget (prog_comp_env prog) as cenv.
  clear prog.
  simpl in * |-. simpl prog_vars'. simpl initial_core.
  remember (Genv.add_globals _ fl) as gev.
  rewrite <- (rev_involutive fl) in *.
  rewrite alloc_globals_rev_eq in Hinit.
  forget (rev fl) as vl.
  unfold prog_defs_names in Hnorepet. simpl in Hnorepet.

  rewrite <- rev_prog_vars' in AL|-*.
  rewrite <- rev_prog_funct' in SAME_IDS.
  rewrite globvars2pred_rev.
  rewrite forallb_rev in AL.
  rewrite <- (rev_involutive G) in  SAME_IDS.
  rewrite match_fdecs_rev in SAME_IDS.
  2:{ apply list_norepet_prog_funct'.
      rewrite <- list_norepet_rev, <- map_rev; auto. }
  rewrite -> inflate_initial_mem_rev with (vl:=vl) by auto.
  rewrite map_rev in Hnorepet. rewrite list_norepet_rev in Hnorepet.
  forget (rev G) as G'; clear G; rename G' into G.
  assert (Hsymb := add_globals_hack _ _ prog_pub Hnorepet Heqgev).
  assert (H1: forall j, In j (map (@fst _ _) G) -> ~ In j (map (@fst _ _) (prog_vars' vl))). {
    intros.
    pose proof (match_fdecs_in j _ _ H SAME_IDS) as Hin'.
    clear - Hnorepet Hin'.
    intro.
    induction vl. inv H.
    inv Hnorepet. specialize (IHvl H3).
    destruct a as [i [a|a]]; simpl in *.
    destruct Hin'.
    * subst j.
      clear - H H2.
      apply H2; clear H2. induction vl; simpl in *; auto.
      destruct a as [i' [a|a]]; auto.
      destruct H; auto.
    * apply IHvl; auto.
    * destruct H; subst.
      apply H2; clear - Hin'. induction vl; simpl in *; auto.
      destruct a as [i' [a|a]]; auto .
      destruct Hin'; auto.
      apply IHvl; auto.
  }
  assert (H1': forall j, In j (map fst (prog_funct' vl)) -> In j (map fst G)). {
    clear - SAME_IDS.
    forget (prog_funct' vl) as fs. intro.
    induction SAME_IDS. auto. simpl. tauto.
  }
  assert (NRG: list_norepet (map fst G)). {
    clear - SAME_IDS Hnorepet.
    eapply match_fdecs_norepet; eauto.
    apply list_norepet_prog_funct'; auto.
  }
  clear SAME_IDS Heqgev.
  change (map fst vl) with (map fst (@nil (ident*@funspec Σ)) ++ map fst vl) in Hnorepet.
  change G with (nil++G).
  set (G0 := @nil (ident*funspec)) in *.
  change G with (G0++G) in NRG.
  clearbody G0.

  revert Hsymb m G0 G NRG Hnorepet Hinit H1 H1'; induction vl; intros; simpl.
  { inv Hinit.
    rewrite /globvars2pred /=.
    by iIntros "_". }
  simpl in Hinit.
  revert Hinit; case_eq (alloc_globals_rev gev Mem.empty vl); intros; try congruence.
  spec IHvl. { clear - AL. simpl in AL. destruct a. destruct g; auto. simpl in AL.
    apply andb_true_iff in AL; destruct AL; auto. }
  spec IHvl. { intros.
    assert (H4': (Pos.to_nat b <= length vl)%nat). {
    clear - H0. rewrite Zlength_correct in H0. lia. }
    fold fundef in *.
    assert (POS := Pos2Z.is_pos b).
    rewrite Hsymb.
    rewrite Pos_to_nat_eq_S /=.
    replace (length vl - (Z.to_nat (Z.pos b) - 1))%nat with (S (length vl - S (Z.to_nat (Z.pos b) - 1)))%nat
      by (simpl; pose proof (Pos2Nat.is_pos b); lia).
    simpl.
    apply iff_refl.
    rewrite Zlength_cons. lia.
  }
  destruct a.
  assert (FS: Genv.find_symbol gev i = Some (nextblock m0)).
  { assert (Genv.find_symbol gev i = Some (nextblock m0)); auto.
    apply Hsymb. apply alloc_globals_rev_nextblock in H. rewrite H.
    rewrite Zlength_cons.
    rewrite Z2Pos.id.
    rewrite Zlength_correct. lia.
    rewrite Zlength_correct. lia.
    simpl.
    apply alloc_globals_rev_nextblock in H. rewrite H.
    replace (Pos.to_nat (Z.to_pos (Z.succ (Zlength vl))))
      with (S (length vl)) by (rewrite Pos_to_nat_eq_S Zlength_correct; lia).
    rewrite Nat.sub_diag. reflexivity. }
  specialize (IHvl m0 G0 G NRG).
  spec IHvl.
  { clear - Hnorepet. apply list_norepet_app in Hnorepet as [? [? ?]].
    inv H0.
    apply list_norepet_app; split3; auto.
    apply list_disjoint_cons_right in H1; auto. }
  specialize (IHvl H).
  spec IHvl.
  { intros ? Hin%H1 ?; contradiction Hin; destruct g; simpl; auto. }
  spec IHvl.
  { intros; apply H1'; destruct g; simpl; auto. }
  destruct g.
* (* Gfun case *)
  simpl.
  iIntros "Hmem"; iApply IHvl.
  simpl in Hinit.
  destruct (alloc m0 0 1) eqn: Halloc.
  rewrite /inflate_initial_mem.
  erewrite nextblock_drop, nextblock_alloc by eassumption.
  replace (Pos.to_nat (Pos.succ _) - 1)%nat with (S (Pos.to_nat (nextblock m0) - 1))%nat by lia.
  rewrite seq_S big_sepL_app /= -Nat.sub_succ_l /=; last lia.
  iDestruct "Hmem" as "(Hmem & Hnew & _)"; iPoseProof (affine with "Hnew") as "_".
  { destruct (block_bounds _).
    apply big_sepL_affine; intros.
    rewrite /inflate_loc.
    rewrite Nat.sub_0_r Pos2Nat.id.
    erewrite drop_perm_access by eassumption.
    if_tac; first by destruct (funspec_of_loc _ _ _); apply _.
    eapply alloc_dry_unchanged_on in H2 as [Ha _]; last done.
    rewrite -Ha nextblock_access_empty //; last lia.
    apply _. }
  iApply (big_sepL_mono with "Hmem").
  intros ?? (-> & ?)%lookup_seq.
  rewrite /block_bounds /=.
  apply alloc_globals_rev_nextblock in H.
  rewrite globals_bounds_app1; last by rewrite Zlength_correct in H; rewrite rev_length; lia.
  destruct (globals_bounds _ _ _); apply big_sepL_mono; intros.
  rewrite /inflate_loc.
  pose proof (alloc_result _ _ _ _ _ Halloc) as ->.
  assert (Pos.of_nat (S k) ≠ nextblock m0) by lia.
  erewrite <- access_drop_3; [| eassumption | auto].
  erewrite <- alloc_access_other; [| eassumption | auto].
  erewrite <- drop_perm_contents by eassumption.
  rewrite /contents_at; erewrite mem_lemmas.AllocContentsOther1; done.
* (* Gvar case *)
  rewrite /globvars2pred /globvar2pred /=.
  simpl in Hinit.
  destruct (alloc m0 0) eqn: Halloc.
  destruct (store_zeros m1 b 0 _) eqn: Hstore; last done.
  destruct (Genv.store_init_data_list _ _ _ _ _) eqn: Hinit_data; last done.
  rewrite /= !andb_true_iff in AL; destruct AL as ((? & ?%Z.ltb_lt) & ?).
  rewrite (init_data_list_lem gp) //.
  rewrite IHvl; iIntros "($ & ?)".
  rewrite /genviron2globals /Map.get /filter_genv FS.
  apply alloc_result in Halloc as ->; done.
  { rewrite Zlength_rev; eapply alloc_globals_rev_nextblock; eauto. }
Qed.

Definition globals_of_genv (g : genviron) (i : ident):=
  match Map.get g i with
| Some b => Vptr b Ptrofs.zero
| None => Vundef
end.

End mpred.
