Require Import VST.veric.juicy_base.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.Clight_initial_world.

Definition only_blocks {S: block -> Prop} (S_dec: forall b, {S b}+{~S b}) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (fun loc => if S_dec (fst loc) then w @ loc else core (w @ loc))
                              _ (level w) _ (ghost_of_approx w))).
Proof.
  hnf; auto.
 extensionality loc;  unfold compose.
 if_tac; try apply resource_at_approx.
 repeat  rewrite core_resource_at. rewrite <- level_core.
apply resource_at_approx.
Defined.

Definition not_dec: forall {S: block -> Prop} (f: forall b, {S b}+{~S b}),
                            forall b, {~S b}+{~ ~ S b}.
Proof. intros. destruct (f b). right; intuition. left; auto.
Qed.

Lemma join_only_blocks:
  forall {S} S_dec phi, identity (ghost_of phi) -> join (@only_blocks S S_dec phi)
                        (only_blocks (not_dec S_dec) phi) phi.
Proof. intros.
  unfold only_blocks.
  apply resource_at_join2.
  repeat rewrite level_make_rmap. auto.
  repeat rewrite level_make_rmap. auto.
 intro;   repeat rewrite resource_at_make_rmap. unfold compose.
 destruct (S_dec (fst loc)); simpl.
  try rewrite if_false by intuition. apply join_comm; apply core_unit.
  rewrite if_true by intuition; apply core_unit.
  rewrite !ghost_of_make_rmap.
  apply identity_unit'; auto.
Qed.

Lemma Exists_dec: forall {T} (f: T -> Prop)(f_dec: forall x, {f x}+{~f x}) (l: list T),
                   {Exists f l}+{~Exists f l}.
  Proof. intros. induction l; simpl. right; intro. inv H.
         destruct IHl. left; constructor 2; auto. destruct (f_dec a). left; constructor 1; auto.
        right; intro Hx; inv Hx; auto.
  Qed.

Lemma only_blocks_at: forall {S} S_dec phi loc,
   @only_blocks S S_dec phi @ loc =
    if S_dec (fst loc) then phi @ loc else core (phi @ loc).
Proof.
   unfold only_blocks; intros.
 rewrite resource_at_make_rmap. auto.
Qed.

Lemma level_only_blocks: forall {S} S_dec phi,
   level (@only_blocks S S_dec phi) = level phi.
Proof. intros. apply level_make_rmap.
Qed.

Definition upto_block (b: block) (w: rmap) : rmap :=  only_blocks (fun b' => plt b' b) w.

Definition beyond_block (b: block) (w: rmap) : rmap := only_blocks (not_dec (fun b' => plt b' b)) w.


Lemma join_upto_beyond_block:
  forall b phi, identity (ghost_of phi) -> join  (upto_block b phi)  (beyond_block b phi) phi.
Proof.  intros; apply join_only_blocks; auto.
Qed.


Lemma split_range:
  forall phi base n,
    (forall loc, adr_range base n loc ->
       match phi @ loc with YES _ _ k _ => isVAL k | _ => True end) ->
    noghost phi ->
   exists phi1, exists phi2,
      join phi1 phi2 phi /\
      forall loc, if adr_range_dec base n loc then identity (phi2 @ loc)
                                                      else identity (phi1 @ loc).
Proof.
  intros ???? Hg.
  pose proof I.
  destruct (make_rmap (fun loc => if adr_range_dec base n loc then phi @ loc else core (phi @ loc)) (ghost_of phi) (level phi)) as [phi1 [J1 J2]].
  extensionality loc;   unfold compose.
  if_tac.  apply resource_at_approx.
  repeat rewrite core_resource_at. rewrite <- level_core. apply resource_at_approx.
  { apply ghost_of_approx. }
  clear H0.
  pose proof I.
 destruct (make_rmap (fun loc => if adr_range_dec base n loc then core (phi @ loc) else phi @ loc) (ghost_of phi) (level phi)) as [phi2 [J3 J4]].
  extensionality loc;   unfold compose.
  if_tac.
  repeat rewrite core_resource_at. rewrite <- level_core. apply resource_at_approx.
  apply resource_at_approx.
  { apply ghost_of_approx. }
 clear H0.
  destruct J2 as [J2 Hg1], J4 as [J4 Hg2].
  exists phi1; exists phi2; split; auto.
  apply resource_at_join2; [congruence | congruence | | ].
  intros; rewrite J2; rewrite J4.
  if_tac.
    apply join_unit2. apply core_unit. auto.
    apply join_unit1. apply core_unit. auto.
  rewrite Hg1, Hg2; apply identity_unit'; auto.
  intros. rewrite J2; rewrite J4. if_tac; apply core_identity.
Qed.

Definition blockslice_rmap (S: block -> Prop) (phi: rmap) :=
    forall loc: address, ~S (fst loc) -> identity (phi @ loc).

Definition eq_mod_blockslice (S: block -> Prop) (phi phi': rmap) :=
 forall loc, (S (fst loc) -> phi @ loc = phi' @ loc) .

Definition blockslice_mpred (S: block -> Prop) (P: mpred) :=
  (forall phi, P phi -> forall loc, ~S (fst loc) -> identity (phi @ loc)) /\
  (forall phi phi', blockslice_rmap S phi -> blockslice_rmap S phi' ->
                        eq_mod_blockslice S phi phi' ->
         P phi -> P phi').

Definition blockslice_mpred_rmap:
  forall S (Sdec: forall b, {S b}+{~S b}) P phi,
   blockslice_mpred S P -> P phi -> blockslice_rmap S phi.
Proof.
 unfold blockslice_mpred, blockslice_rmap; intros.
 destruct H.
 eapply H; eauto.
Qed.


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

Definition init_data2pred (d: init_data)  (sh: share) (a: val) (rho: environ) : mpred :=
 match d with
  | Init_int8 i => mapsto sh (Tint I8 Unsigned noattr) a (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh (Tint I16 Unsigned noattr) a (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh (Tint I32 Unsigned noattr) a (Vint i)
  | Init_int64 i => mapsto sh (Tlong Unsigned noattr) a (Vlong i)
  | Init_float32 r =>  mapsto sh (Tfloat F32 noattr) a (Vsingle r)
  | Init_float64 r =>  mapsto sh (Tfloat F64 noattr) a (Vfloat r)
  | Init_space n => mapsto_zeros n sh a
  | Init_addrof symb ofs =>
       match Map.get (ge_of rho) symb with
       | Some b => mapsto sh (Tpointer Tvoid noattr) a (Vptr b ofs)
       | _ => mapsto_ sh (Tpointer Tvoid noattr) a
       end
 end.

Fixpoint init_data_list2pred  (dl: list init_data)
                           (sh: share) (v: val)  : environ -> pred rmap :=
  match dl with
  | d::dl' => 
      lift2 sepcon (init_data2pred d sh v) 
                  (init_data_list2pred dl' sh (offset_val (init_data_size d) v))
  | nil => lift0 emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Ers else Ews.

Definition globals_of_env (rho: environ) (i: ident) : val := 
  match Map.get (ge_of rho) i with Some b => Vptr b Ptrofs.zero | None => Vundef end.

Definition globvar2pred (gv: ident->val) (idv: ident * globvar type) : assert :=
   if (gvar_volatile (snd idv))
                       then  lift0 TT
                       else    init_data_list2pred (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) (gv (fst idv)).


Definition globvars2pred (gv: ident->val) (vl: list (ident * globvar type)) : assert :=
  (lift2 andp) (fun rho => prop (gv = globals_of_env rho))
  (fold_right (lift2 sepcon) (lift0 emp) (map (globvar2pred gv) vl)).

Lemma globvars2pred_rev:
  forall gv l, globvars2pred gv (rev l) = globvars2pred gv l.
Proof.
 intros. unfold globvars2pred.
 rewrite map_rev.
  rewrite fold_left_rev_right.
 rewrite fold_symmetric.
 f_equal.
 f_equal. extensionality x y rho; apply sepcon_comm.
 intros; extensionality rho; apply sepcon_assoc.
 intros; extensionality rho; apply sepcon_comm.
Qed.

Lemma writable_blocks_rev:
  forall rho l, writable_blocks l rho = writable_blocks (rev l) rho.
Proof.
induction l; simpl; auto.
destruct a.
rewrite writable_blocks_app.
rewrite <- IHl.
simpl.
rewrite sepcon_emp.
apply sepcon_comm.
Qed.

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
  unfold Genv.add_global, Genv.find_symbol; simpl. rewrite PTree.gss. f_equal; unfold block; omega.
  }
  forget (Genv.add_global ge (i, g)) as ge1.
  revert H2 ge1; induction ul; simpl; intros; auto.
  spec IHul; [intuition |].
  rewrite IHul.
  unfold Genv.find_symbol, Genv.add_global. simpl.
  rewrite PTree.gso; auto.
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
Proof. induction dl; simpl; intros. omega.
 pose proof (init_data_size_pos a); omega.
Qed.

Require Import FunInd.

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
  apply IHo. auto. intuition omega.
  eapply Mem.load_store_other; eauto. simpl. intuition omega.
  discriminate.
Qed.

Lemma load_store_zeros:
  forall m b z N m', store_zeros m b z N = Some m' ->
         forall z', z <= z' < z + N -> load Mint8unsigned m' b z' = Some (Vint Int.zero).
Proof.
 intros.
 symmetry in H; apply R_store_zeros_correct in H.
  remember (Some m') as m1.
  revert z'  m' Heqm1 H0; induction H; intros. omegaContradiction.
  subst _res.
 destruct (Z.eq_dec z' p).
 2:{ apply IHR_store_zeros; auto.
   clear - H0 n0.  destruct H0. omega.
  }
  subst z'.
  destruct (load_store_similar _ _ _ _ _ _ e0) with Mint8unsigned; simpl; auto.
  omega.
  destruct H1.
 simpl in H2. subst x.
  replace (Int.zero_ext 8 Int.zero) with (Int.zero) in H1 by reflexivity.
  rewrite <- H1.
  clear - H. apply R_store_zeros_complete in H.
 symmetry.
 symmetry in H; symmetry; eapply store_zeros_load_outside; eauto.
 right. simpl; omega.
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
  (Some (decode_val chunk (list_repeat (size_chunk_nat chunk) (Byte Byte.zero)))).
2: destruct chunk; reflexivity.
apply loadbytes_load; auto.
clear H2.
rewrite size_chunk_conv in *.
(* pose proof (loadbytes_load Mint8unsigned m b). *)
forget (size_chunk_nat chunk) as n.
assert (forall i, p <= i < p + (Z.of_nat n) ->
                     loadbytes m b i 1 = Some (Byte Byte.zero::nil)).
intros.
specialize (H i).
spec H; [ omega |].
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
omega.
compute; congruence.
rewrite Int.unsigned_repr.
pose proof (Byte.unsigned_range i0).
change (two_p 8) with Byte.modulus; omega.
pose proof (Byte.unsigned_range i0).
assert (Byte.modulus < Int.max_unsigned) by (compute; congruence).
omega.
clear - H2.
revert p H2; induction n; intros.
simpl.
apply loadbytes_empty. omega.
rewrite inj_S. unfold Z.succ.
rewrite Z.add_comm.
change (list_repeat (S n) (Byte Byte.zero)) with
 (list_repeat 1 (Byte Byte.zero) ++ list_repeat n (Byte Byte.zero)).
apply loadbytes_concat.
apply H2. rewrite inj_S; omega.
apply IHn.
intros.
apply H2.  rewrite inj_S; omega.
omega. omega.
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
  eapply IHil; eauto. generalize (init_data_size_pos a). intuition omega.
  eapply store_init_data_outside; eauto. tauto.
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
  replace (z+0) with z by omega.
  simpl in H0.
  invSome.
  spec H2. {
    clear - H1.
    apply read_as_zero_lem1; intros; apply H1.
    omega.
  }
  destruct a; simpl in H2|-*; try solve [destruct H2; auto]; intros.
  rewrite (store_init_data_list_outside _ _ _ _ _ _ H4) by (right; simpl; omega).
  simpl in H0. inv H0. apply H1.
  simpl.
  pose proof (init_data_list_size_pos dl).
  omega.
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
  destruct H6. simpl in H7. omegaContradiction.
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
  omega.
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

(*
Lemma read_sh_readonly:
  forall NU, read_sh = mk_lifted (readonly2share true) NU.
Proof.
  simpl. unfold read_sh. simpl. f_equal; auto with extensionality.
Qed.  
*)

Lemma zero_ext_inj: forall i,
   Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.zero ->
   i = Byte.zero.
Proof.
intros.
assert (MU: 256 < Int.max_unsigned).
 unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
  unfold two_power_nat, shift_nat in *; simpl in *.
 replace (Zpos (4294967296 - 1)) with (4294967295). omega. reflexivity.
rewrite Int.zero_ext_and in H by omega.
(*
 by (unfold Int.wordsize, Wordsize_32.wordsize; split; simpl in *; omega). *)
pose proof (Int.modu_and (Int.repr (Byte.unsigned i)) (Int.repr (two_p 8)) (Int.repr 8)).
 spec H0.
 apply Int.is_power2_two_p; simpl.  unfold Int.zwordsize; simpl. omega.
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
  unfold two_power_nat, shift_nat in *; simpl in *. omega.
 clear - MU.
 unfold Int.divu. unfold Int.zero. f_equal.
 symmetry. apply Zdiv_small.
 split.
 destruct (Int.unsigned_range (Int.repr (Byte.unsigned i))); auto.
 repeat rewrite Int.unsigned_repr.
 destruct (Byte.unsigned_range i).
 apply H0. simpl.  unfold two_power_pos, shift_pos; simpl. omega.
 destruct (Byte.unsigned_range i).
 split; auto. replace Byte.modulus with 256 in H0 by reflexivity. omega.
 clear - MU. replace (two_p 8) with 256 by reflexivity.
 unfold Int.zero. intro.
 pose proof (Int.unsigned_repr 256).
 spec H0. split; omega.
 rewrite H in H0. rewrite Int.unsigned_repr in H0 by omega. inv H0.
 replace (two_p 8) with 256 by reflexivity.
 unfold Int.one.
 rewrite Int.sub_signed.
 pose proof (Int.min_signed_neg).
 assert (Int.max_signed = 2147483647).
 clear.  unfold Int.max_signed, Int.half_modulus, Int.modulus, Int.wordsize, two_power_nat; simpl.
 reflexivity.
  repeat rewrite Int.signed_repr; auto;  split; try omega.
Qed.

Lemma max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof.
 unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
  simpl. unfold shift_nat. simpl. reflexivity.
Qed.

Lemma decode_val_getN_lem1:
  forall j i b,
          decode_val Mint32 (getN 4 i b) = Vint Int.zero ->
          0 <= j-i < 4 ->
          nth (nat_of_Z (j-i)) (getN 4 i b) Undef = Byte Byte.zero.
Proof.
 intros.
 unfold decode_val in H.
 revert H; case_eq (getN 4 i b); intros. inv H.
 unfold getN in H. destruct l; inv H.
 destruct (proj_bytes
         (ZMap.get i b
          :: ZMap.get (i + 1) b
             :: ZMap.get (i + 1 + 1) b :: ZMap.get (i + 1 + 1 + 1) b :: nil))
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
  clear H. rewrite max_unsigned_eq; omega.
  rewrite H in H4.
 rewrite Int.unsigned_repr in H4 by (rewrite max_unsigned_eq; omega).
  omega.
 assert (Byte.unsigned i0=0/\Byte.unsigned i1=0/\Byte.unsigned i2=0/\Byte.unsigned i3=0).
 unfold rev_if_be in H. destruct Archi.big_endian; simpl in H; apply H1 in H; intuition.
 clear H1 H.
  assert (forall i, Byte.unsigned i = 0 -> i = Byte.zero).
  clear. intros. pose proof (Byte.repr_unsigned i). rewrite H in H0. symmetry; auto.
 destruct H2 as [? [? [? ?]]]. apply H in H1; apply H in H2; apply H in H3; apply H in H4.
 subst.
 assert (j-i=0 \/ j-i=1 \/ j-i=2 \/ j-i=3) by omega.
 destruct H1 as [? | [?|[?|?]]]; rewrite H1; simpl; auto.
*
 unfold proj_value in H1.
 unfold Val.load_result in H1.
 clear PB.
 destruct (ZMap.get i b); inv H1.
(* Not true if Archi.ptr64=false *)
Abort.

Lemma Zmax_Z_of_nat:
 forall n, Z.max (Z_of_nat n) 0 = Z_of_nat n.
Proof.
intros.
apply Z.max_l.
omega.
Qed.
(*
Lemma Zmax_of_nat:
  forall n, Z_of_nat (nat_of_Z n) = Z.max n 0.
Proof.
 intros.
 apply nat_of_Z_max.
Qed.
*)

Lemma snd_split_fullshare_not_bot: snd (Share.split fullshare) <> Share.bot.
Proof.
intro.
case_eq (Share.split fullshare); intros.
rewrite H0 in H. simpl in H. subst.
apply Share.split_nontrivial in H0; auto.
apply Share.nontrivial in H0. contradiction.
Qed.

Lemma readable_readonly2share: forall ro, readable_share (readonly2share ro).
Proof.
  intros.
  unfold readable_share. intro.
  apply identity_share_bot in H.
  assert (H9: Share.Rsh <> Share.bot). {
    unfold Share.Rsh. intro.
    destruct (Share.split Share.top) eqn:?.
    pose proof (Share.split_nontrivial _ _ _ Heqp). spec H1; auto. contradiction Share.nontrivial.
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

(*
Lemma nonunit_readonly2share: forall v, nonunit (readonly2share (@gvar_readonly type v)).
Proof.
  intros.
  destruct (gvar_readonly v); simpl.
  clear.  unfold Share.Lsh. repeat intro.
  pose proof (fst_split_fullshare_not_bot).
  apply unit_identity in H. apply identity_share_bot in H. contradiction H0; apply H.
  clear. repeat intro. pose proof (Share.nontrivial).
  apply unit_identity in H. apply identity_share_bot in H. contradiction H0; apply H.
Qed.
*)

(*
Lemma readable_splice_extern: forall v, readable_share (Share.lub extern_retainer (readonly2share (@gvar_readonly type v))).
Proof.
  intros.
  apply readable_share_lub. apply readable_readonly2share.
Qed.
*)

Lemma init_data_lem:
forall (ge: genv) (v : globvar type) (b : block) (m1 : mem')
  (m3 m4 : Memory.mem) (phi0 : rmap) (a : init_data) (z : Z) (rho: environ)
  (w1 wf : rmap),
   load_store_init_data1 ge m3 b z a ->
   contents_at m4 = contents_at m3 ->
   join w1 wf (beyond_block b (inflate_initial_mem m4 phi0)) ->
   (forall loc : address,
     if adr_range_dec (b, z) (init_data_size a) loc
     then identity (wf @ loc) /\ access_at m4 loc Cur = Some (Genv.perm_globvar v)
     else identity (w1 @ loc)) ->
   forall (Hg: noghost w1) (VOL:  gvar_volatile v = false)
          (AL: initializer_aligned z a = true)
           (LO:   0 <= z) (HI: z + init_data_size a < Ptrofs.modulus)
         (RHO: ge_of rho = filter_genv ge),
  (init_data2pred a  (readonly2share (gvar_readonly v))
       (Vptr b (Ptrofs.repr z))) rho w1.
Proof.
  intros.
  assert (APOS:= init_data_size_pos a).
  assert (READABLE:= readable_readonly2share (gvar_readonly v)).
  Transparent load.
  unfold init_data2pred, mapsto.
  unfold mapsto_zeros, address_mapsto, res_predicates.address_mapsto,
    fst,snd.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
  simpl.
  unfold mapsto, tc_val, is_int, is_long, is_float.
  destruct (readable_share_dec
            (readonly2share (gvar_readonly v))); [clear r | tauto].
  destruct a; 
  repeat rewrite prop_true_andp by 
    first [apply I
            | apply sign_ext_range'; compute; split; congruence
            | apply zero_ext_range'; compute; split; congruence
            ];
  try left; simpl in H; unfold load in H;
  try (if_tac in H; [ | discriminate H]);
  repeat rewrite prop_true_andp by apply I;
  try match type of H with Some (decode_val ?ch ?B) = Some (?V) =>
            exists B; replace V with (decode_val ch B) by (inversion H; auto);
            clear H; repeat split; auto
       end.
* (* Int8 *)
  apply Zone_divide.
* (* Int8 *)
  intro loc; specialize (H2 loc).
  simpl in H2. hnf. if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf. rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
  unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* Int16 *)
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
* (* Int16 *)
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* Int32 *)
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
* (* Int32 *)
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* Int64 *)
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
* (* Int64 *)
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* Float32 *)
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
* (* Float32 *)
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* Float64 *)
   clear - AL.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  rewrite <- Zeq_is_eq_bool in *.
  apply Zmod_divides; [ omega | ].
  apply Zmod_divides in AL; [ | omega].
  destruct AL as [c ?]. exists (2 * c). rewrite Z.mul_assoc. apply H.
*  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
* (* address_mapsto_zeros *)
 rewrite address_mapsto_zeros_eq.
 split; auto. 
  split; auto. simpl in HI. clear - HI. destruct (Z.max_spec z0 0); destruct H; omega.
 split; auto.
  intro loc. hnf. specialize (H2 loc); simpl in H2.
rewrite Zmax_Z_of_nat.
rewrite nat_of_Z_max.
if_tac; auto.

  exists READABLE.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true by (  destruct loc; destruct H3; subst; simpl; unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct loc; destruct H3; subst b0.
  specialize (H (z1-z)).  spec H; [omega |].
  if_tac in H; [ | discriminate].
  replace (z+(z1-z)) with z1 in * by omega.
  rewrite H0.
  inv H.
  assert (contents_at m3 (b,z1) = Byte Byte.zero).
    unfold contents_at.
    simpl. forget (ZMap.get z1 (PMap.get b (mem_contents m3))) as byt.
    clear - H7.
    unfold decode_val in H7.
    revert H7; case_eq (proj_bytes (byt::nil)); intros; try discriminate.
    simpl in  H. destruct byt; inv H.
    unfold decode_int in H7.
    replace (rev_if_be (i::nil)) with (i::nil) in H7 by (unfold rev_if_be; destruct Archi.big_endian; auto).
    simpl int_of_bytes in H7.
    replace (Byte.unsigned i + 0) with (Byte.unsigned i) in H7 by omega.
    f_equal.
   apply zero_ext_inj. forget (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) as j; inv H7; auto.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.

* (* symbol case *)
 rewrite RHO.
  case_eq (Map.get (filter_genv ge) i); try destruct p0; auto; intros.
+
  unfold filter_genv, Map.get in H4.
  revert H4; case_eq (Genv.find_symbol ge i); intros; try discriminate.
  inv H5.
  left. split; [apply I | ].
  rewrite H4 in H.
 exists  (getN (size_chunk_nat Mptr) z (mem_contents m3) !! b).
 repeat split; auto.
 clear - H. 
 cbv iota. congruence.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc). hnf. simpl init_data_size in H2.
 replace (if Archi.ptr64 then 8 else 4) with (size_chunk Mptr) in H2
   by (unfold Mptr; destruct Archi.ptr64; reflexivity).
 if_tac; [ | apply H2].
  exists READABLE. hnf. 
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true
   by (destruct loc, H,H5; subst; simpl;
        unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H6.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
  rewrite H0.
  destruct loc; destruct H5.  subst b1.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H5; subst b1.
  apply nth_getN; simpl; omega.
+
  erewrite mapsto__exp_address_mapsto by (auto; reflexivity).
  rewrite exp_address_mapsto_VALspec_range_eq.
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with (Ptrofs.modulus-1); omega).
  split.
  simpl in AL|-*.
  apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  hnf. split; auto. intro loc; specialize (H2 loc). hnf.
  simpl init_data_size in H2.
 replace (if Archi.ptr64 then 8 else 4) with (size_chunk Mptr) in H2
   by (unfold Mptr; destruct Archi.ptr64; reflexivity).
 if_tac; [ | apply H2].
 destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1.
  eexists.
  hnf. exists READABLE.
  hnf; rewrite H1.
  unfold beyond_block. rewrite only_blocks_at.
  rewrite if_true
   by (destruct loc, H,H5; subst; simpl;
        unfold block; xomega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H6.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto with extensionality.
Qed.

Lemma init_data_list_size_app:
  forall dl1 dl2, init_data_list_size (dl1++dl2) =
                   init_data_list_size dl1 + init_data_list_size dl2.
Proof. induction dl1; intros; simpl; auto. rewrite IHdl1; omega.
Qed.


Lemma max_unsigned_modulus:
  Ptrofs.max_unsigned + 1 = Ptrofs.modulus.
Proof.
 unfold Ptrofs.max_unsigned. omega.
Qed.

Lemma init_data_list_lem:
  forall (ge: genv) m0 (v: globvar type) m1 b m2 m3 m4  phi0 rho,
     alloc m0 0 (init_data_list_size (gvar_init v)) = (m1,b) ->
     store_zeros m1 b 0 (init_data_list_size (gvar_init v)) = Some m2 ->
     Genv.store_init_data_list ge m2 b 0 (gvar_init v) = Some m3 ->
     drop_perm m3 b 0 (init_data_list_size (gvar_init v))
               (Genv.perm_globvar v) = Some m4 ->
  forall
   (Hg: noghost phi0) (SANITY: init_data_list_size (gvar_init v) < Ptrofs.modulus)
   (VOL:  gvar_volatile v = false)
   (AL: initializers_aligned 0 (gvar_init v) = true)
   (RHO: ge_of rho = filter_genv ge),
     init_data_list2pred (gvar_init v) (readonly2share (gvar_readonly v)) (Vptr b Ptrofs.zero)
            rho (beyond_block b (inflate_initial_mem m4 phi0)).
Proof.
intros.
set (phi := beyond_block b (inflate_initial_mem m4 phi0)).
assert (forall loc, fst loc <> b -> identity (phi @ loc)).
  unfold phi; intros.
  unfold beyond_block. rewrite only_blocks_at.
  if_tac; [ |  apply core_identity].
  unfold inflate_initial_mem.  rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'.
  unfold access_at.
  rewrite nextblock_noaccess. apply NO_identity.
  rewrite (nextblock_drop _ _ _ _ _ _ H2).
  rewrite (Genv.store_init_data_list_nextblock _ _ _ _ _ H1).
  rewrite (Genv.store_zeros_nextblock _ _ _ _ H0).
  assert (nextblock m1 = Pos.succ b /\ b = nextblock m0).
   clear - H. Transparent alloc. inv H.  simpl. auto. Opaque alloc.
 destruct H5; unfold block in *; xomega.
 assert (forall loc, if adr_range_dec (b,0)  (init_data_list_size (gvar_init v)) loc
                             then access_at m4 loc Cur = Some (Genv.perm_globvar v)
                             else identity (phi @ loc)).
  intro. if_tac.
     destruct loc; destruct H4; subst b0.
     unfold access_at. simpl. forget (Genv.perm_globvar v) as p.
      forget (init_data_list_size (gvar_init v)) as n.
     clear - H2 H5. unfold drop_perm in H2.
      destruct (range_perm_dec m3 b 0 n Cur Freeable); inv H2.
      simpl.  rewrite PMap.gss.
       destruct (zle 0 z); try omegaContradiction. destruct (zlt z n); try omegaContradiction.
       simpl; auto.
    destruct loc.
  destruct (eq_dec b b0). subst b0.
  unfold phi. unfold beyond_block. rewrite only_blocks_at.
   simpl. rewrite if_true by (unfold block; xomega).
  unfold inflate_initial_mem.  rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'.
  replace (access_at m4 (b,z) Cur) with (@None permission).
  apply NO_identity.
  symmetry.  transitivity (access_at m3 (b,z) Cur).
  clear - H4 H2. unfold access_at; unfold drop_perm in H2.
   destruct (range_perm_dec m3 b 0 (init_data_list_size (gvar_init v)) Cur
         Freeable); inv H2. simpl. rewrite PMap.gss.
  unfold adr_range in H4. destruct (zle 0 z); auto.
   destruct (zlt z (init_data_list_size (gvar_init v)) ); auto.
  contradiction H4. split; auto.
  transitivity (access_at m2 (b,z) Cur).
  apply store_init_data_list_outside' in H1.
  destruct H1 as [? [? ?]]; congruence.
  transitivity (access_at m1 (b,z) Cur).
  clear - H0. erewrite store_zeros_access; eauto.
  clear - H H4. Transparent alloc. inv H. Opaque alloc. unfold access_at; simpl.
  rewrite PMap.gss. destruct (zle 0 z); auto.
   destruct (zlt z (init_data_list_size (gvar_init v)) ); auto.
  contradiction H4. split; auto.
   apply H3. auto.
  clear H3.
  assert (contents_at m4 = contents_at m3).
  clear - H2; unfold contents_at, drop_perm in *.
   destruct (range_perm_dec m3 b 0 (init_data_list_size (gvar_init v)) Cur
         Freeable); inv H2. simpl. auto.
   clear H2.
   forget (gvar_init v) as dl.
   remember dl as D.
   rewrite HeqD in AL,H4|-*.
   assert (nil++dl=D) by (subst; auto).
   remember (@nil init_data) as dl'.
   remember (core phi) as w'.
   remember phi as w.
   assert (join w' w phi). subst. apply core_unit.
   unfold Ptrofs.zero.
   remember 0 as z. rewrite Heqz in H,H0,H1.
   replace z with (init_data_list_size dl') in AL,H4|-* by (subst; auto).
   clear z Heqz.
   assert (forall loc, if adr_range_dec (b,init_data_list_size dl') (init_data_list_size dl) loc
                               then identity (w' @ loc)  else identity (w @ loc)).
  intro. subst. if_tac. rewrite <- core_resource_at. apply core_identity.
  specialize (H4 loc). rewrite if_false in H4 by auto; auto.
  assert (noghost w) as Hgw.
  { subst w phi.
    unfold beyond_block, only_blocks, inflate_initial_mem; simpl.
    rewrite !ghost_of_make_rmap; auto. }
   clear Heqw' Heqw Heqdl' HeqD.
   revert dl' w' w AL H2 H4 H5 H6 Hgw; induction dl; simpl; intros.
   apply all_resource_at_identity; auto; intro loc.
   specialize (H6 loc); if_tac in H6; auto. destruct loc; destruct H7.
   omegaContradiction.
  assert (SANITY': init_data_list_size dl' + init_data_size a + init_data_list_size dl < Ptrofs.modulus).
  clear - H2 SANITY.
  subst D.
 rewrite init_data_list_size_app in SANITY. simpl in SANITY. omega.
  destruct (split_range w (b,init_data_list_size dl') (init_data_size a)) as [w1 [w2 [? ?]]]; auto.
  intros. apply (resource_at_join _ _ _ loc) in H5.
  specialize (H6 loc). rewrite if_true in H6. apply H6 in H5.
  rewrite H5.
    unfold phi; clear. unfold beyond_block. rewrite only_blocks_at.
   if_tac; [ |   destruct (inflate_initial_mem m4 phi0 @ loc);
                [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto].
  unfold inflate_initial_mem; rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. destruct (access_at m4 loc); try destruct p; simpl; auto.
  destruct (phi0 @ loc); auto.
  destruct loc. destruct H7; split; auto.
  pose proof (init_data_list_size_pos dl).
  omega.
  exists w1; exists w2; split3; auto.
  clear IHdl.
  destruct (join_assoc H7 (join_comm H5)) as [wf [? ?]].
  assert (forall loc, if adr_range_dec (b,init_data_list_size dl') (init_data_size a) loc
                                 then identity (wf @ loc) /\
                                         access_at m4 loc Cur = Some (Genv.perm_globvar v)
                                 else identity (w1 @ loc)).
     intro. specialize (H8 loc); specialize (H6 loc); specialize (H4 loc).
       apply (resource_at_join _ _ _ loc) in H9;
       apply (resource_at_join _ _ _ loc) in H10.
 if_tac.  rewrite if_true in H6,H4. apply H8 in H9. rewrite <- H9; auto.
   destruct loc; destruct H11; subst b0. split; auto.
   pose proof (init_data_list_size_pos dl); omega.
   destruct loc; destruct H11; subst b0. split; auto.
   pose proof (init_data_list_size_pos dl); omega.
 auto.
  pose proof (load_store_init_data_lem1 H0 H1 _ _ _ H2).
  unfold phi in *; clear phi.
  eapply init_data_lem; try eassumption.
  apply ghost_of_join in H7.
  simpl; eapply split_identity; eauto.
  clear - AL. apply andb_true_iff in AL. destruct AL; auto.
  pose proof (init_data_list_size_pos dl'); omega.
  pose proof (init_data_list_size_pos dl); omega.
  destruct (join_assoc (join_comm H7) (join_comm H5)) as [wg [? ?]].
  specialize (IHdl  (dl' ++ (a::nil))  wg w2).
  replace (init_data_list_size (dl' ++ a :: nil)) with
             (init_data_list_size dl' + init_data_size a) in IHdl.
  rewrite Ptrofs.add_unsigned.
  repeat rewrite Ptrofs.unsigned_repr
       by (pose proof (init_data_list_size_pos dl'); pose proof (init_data_list_size_pos dl);
      pose proof (init_data_size_pos a); pose proof max_unsigned_modulus; omega).
  apply IHdl; auto.
  apply andb_true_iff in AL; destruct AL; auto.
  rewrite app_ass; auto.
  intro loc; specialize (H6 loc); specialize (H8 loc); specialize (H4 loc).
  if_tac. rewrite if_true in H4; auto.
  destruct loc; destruct H11; auto.
  split; auto.
  pose proof (init_data_size_pos a); omega.
  if_tac in H8; auto.
  rewrite if_false in H6.
  apply join_comm in H5.
  apply (resource_at_join _ _ _ loc) in H7.
  apply H8 in H7. rewrite H7; auto.
  destruct loc.
  intros [? ?]. subst b0.
  forget (init_data_list_size dl') as u.
 destruct (zlt z (u + init_data_size a)).
 apply H12.  split; auto. omega.
 apply H11.  split; auto. omega.
  intro loc. specialize (H4 loc); specialize (H6 loc); specialize (H8 loc).
  apply (resource_at_join _ _ _ loc) in H7.
  apply (resource_at_join _ _ _ loc) in H9.
  apply (resource_at_join _ _ _ loc) in H10.
  apply (resource_at_join _ _ _ loc) in H5.
 destruct loc.
  if_tac in H8.
  rewrite if_false; auto.
 clear - H11; destruct H11; intros [? ?]. omega.
  if_tac in H4.
  rewrite if_true.
  apply H8 in H9. rewrite <- H9 in *. auto.
  destruct H12; subst b0. split; auto.
  forget (init_data_list_size dl') as u.
  assert (~ (u <= z < u + init_data_size a)) by (contradict H11; destruct H11; split; auto; omega).
  omega.
 rewrite if_false. apply H8 in H7. rewrite H7; auto.
 contradict H12. destruct H12; split; auto.
  pose proof (init_data_size_pos a); omega.
  apply ghost_of_join, join_comm in H7.
  simpl; eapply split_identity; eauto.
 clear.
  induction dl'; simpl; intros; try omega.
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
   try solve [unfold access_at; extensionality loc; rewrite (store_access _ _ _ _ _ _ H); auto].
  inv H; auto. invSome.
  unfold access_at; extensionality loc; rewrite (store_access _ _ _ _ _ _ H2); auto.
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


Lemma alloc_global_beyond2:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, (fst loc > nextblock m)%positive ->
        access_at m' loc Cur = None.
Proof.
 intros.
 destruct loc as [b ofs]; simpl in *.
 unfold access_at, Genv.alloc_global in *.
Transparent alloc.
 destruct iv; destruct g; simpl @fst; simpl @ snd;
 [forget 1 as N |  forget  (init_data_list_size (gvar_init v)) as N];
 revert H; case_eq (alloc m 0 N); intros; repeat invSome;
 match goal with H: drop_perm ?m _ _ _ _ = _ |- _ =>
   unfold drop_perm in H;
  destruct (range_perm_dec m b0 0 N Cur Freeable); inv H
 end;
  inv H; simpl in *;
 repeat rewrite PMap.gss;
 repeat rewrite PMap.gso by (intro Hx; inv Hx; xomega);
 try (apply nextblock_noaccess; xomega).
 apply store_zeros_access in H1.
 apply store_init_data_list_outside' in H4.
 destruct H4 as [? [? ?]]. rewrite H2 in H1.
 change (access_at m2 (b,ofs) Cur = None).
 rewrite H1. unfold access_at; simpl.
 repeat rewrite PMap.gso by (intro Hx; inv Hx; xomega).
 apply nextblock_noaccess; xomega.
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
simpl in H3. rewrite PMap.gss in *.
destruct (zle 0 z). simpl. destruct (zlt z N).
simpl in *.
rewrite if_true; auto. rewrite if_false; auto.
 intros [? ?]. xomega.
simpl. rewrite if_false by omega.
simpl in H3; auto.
Qed.

Lemma alloc_global_inflate_same:
  forall n i v gev m G m0,
  Genv.alloc_global gev m0 (i, Gvar v) = Some m ->
   (forall z : Z, initial_core gev G n @ (nextblock m0, z) = NO Share.bot bot_unreadable) ->
   inflate_initial_mem m0 (initial_core gev G n) =
   upto_block (nextblock m0) (inflate_initial_mem m (initial_core gev G n)).
Proof.
 intros.
 apply rmap_ext.
  unfold upto_block, inflate_initial_mem;
  rewrite level_only_blocks; repeat rewrite level_make_rmap. auto.
 intro loc.
 unfold upto_block. rewrite only_blocks_at.
 unfold inflate_initial_mem.
 repeat rewrite resource_at_make_rmap.
 if_tac.
 destruct (alloc_global_old _ _ _ _ H _ H1) as [? ?];
 unfold inflate_initial_mem'; rewrite H2; rewrite H3; auto.
 destruct (eq_dec (fst loc) (nextblock m0)).
 2:{
 assert (access_at m loc Cur = None).
  eapply alloc_global_beyond2; try eassumption. unfold block in *; xomega.
 assert (access_at m0 loc Cur = None).
  unfold access_at. apply nextblock_noaccess. auto.
 unfold inflate_initial_mem'; rewrite H2; rewrite H3; auto.
 rewrite core_NO; auto.
 }
 clear H1.
 specialize (H0 (snd loc)).
 assert (access_at m0 loc Cur = None).
  unfold access_at. apply nextblock_noaccess. rewrite <- e; xomega.
 unfold inflate_initial_mem' at 1. rewrite H1.
  unfold inflate_initial_mem'.
 destruct loc; simpl in e; subst.
 rewrite (alloc_global_access _ _ _ _ _ H).
 if_tac. unfold Genv.perm_globvar. simple_if_tac. simpl in H0. rewrite H0. rewrite core_NO; auto.
  simple_if_tac; rewrite core_YES; auto.
 rewrite core_NO; auto.
 unfold upto_block, only_blocks, inflate_initial_mem; rewrite !ghost_of_make_rmap; auto.
Qed.

Lemma find_id_rev: forall i G,
 list_norepet (map fst G) -> find_id i (rev G) = find_id i G.
Proof.
intros.
induction G; simpl; intros; auto.
inv H. destruct a. simpl in *. specialize (IHG H3).
if_tac. subst.
clear - H2.
rewrite In_rev in H2. rewrite <- map_rev in H2.
 induction (rev G); simpl; auto. rewrite if_true; auto.
 destruct a;  simpl in *.
 if_tac. subst. intuition. apply IHl; intuition.
 rewrite <- IHG. clear IHG.
 clear - H.
 induction (rev G); simpl; auto. rewrite if_false; auto.
 destruct a; simpl in *. if_tac; auto.
Qed.


Definition prog_var_block (rho: environ) (il: list ident) (b: block) : Prop :=
  Exists (fun id => match ge_of rho id with Some b' => b'=b | _ => False end) il.

Lemma match_fdecs_in:
  forall i vl G,
     In i (map (@fst _ _) G) ->
     match_fdecs vl G ->
     In i (map (@fst _ _) vl).
Proof.
 induction vl; simpl; intros; auto.
 inv H0. inv H.
 inv H0.
 destruct H. inv H. simpl; auto.
 right. apply (IHvl G0); auto.
(* EXPERIMENT right; apply (IHvl G); auto. *)
Qed.

Lemma match_fdecs_norepet:
  forall vl G,
     list_norepet (map (@fst _ _) vl) ->
     match_fdecs vl G ->
     list_norepet (map (@fst _ _) G).
Proof.
 induction vl; simpl; intros.
 inv H0. constructor.
 inv H0. inv H.
 simpl.
 constructor; auto.
 contradict H2. eapply match_fdecs_in; eauto.
(* EXPERIMENT  inv H; eauto. *)
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

(* EXPERIMENT
Lemma match_fdecs_nil:
  forall vl, match_fdecs vl nil.
Proof. induction vl; try constructor 3; auto; constructor.
Qed.
*)

Lemma match_fdecs_rev':
  forall vl G vl' G',
   list_norepet (map (@fst _ _) (rev vl ++ vl')) ->
   match_fdecs vl G ->
   match_fdecs vl' G' ->
   match_fdecs (rev vl ++ vl') (rev G ++ G').
Proof.
induction vl; intros.
simpl in *.
destruct G; inv H0. apply H1.
destruct a.
inv H0.
simpl. do 2 rewrite app_ass.
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
left; rewrite map_rev, <- in_rev; auto.
rewrite map_rev, <- in_rev in H; auto.
destruct H0; auto.
subst j. specialize (H4 i i). contradiction H4; auto.
left; auto.
auto.
auto.
constructor 2; auto.
(* EXPERIMENT simpl. rewrite app_ass.
apply IHvl; auto.
clear - H.
rewrite map_app in H.
rewrite map_app.
simpl in *.
rewrite map_app in H.
rewrite app_ass in H.
simpl in *.
auto.
simpl.
constructor 3.
auto.
*)
Qed.

Lemma match_fdecs_rev:
  forall vl G,
   list_norepet (map (@fst _ _) vl) ->
   match_fdecs (rev vl) (rev G) = match_fdecs vl G.
Proof.
  intros; apply prop_ext; split; intros.
*
  rewrite (app_nil_end vl).
  rewrite (app_nil_end G).
  rewrite <- (rev_involutive vl), <- (rev_involutive G).
  apply match_fdecs_rev'; auto.
  rewrite rev_involutive, <- app_nil_end; auto.
  constructor.
*
  rewrite (app_nil_end (rev vl)).
  rewrite (app_nil_end (rev G)).
  apply match_fdecs_rev'; auto.
  rewrite <- app_nil_end.
  rewrite map_rev. rewrite list_norepet_rev; auto.
  constructor.
Qed.

Lemma initial_core_rev:
  forall (gev: Genv.t fundef type) G n (vl: list (ident * globdef fundef type))
    (H: list_norepet (map fst (rev vl)))
    (SAME_IDS : match_fdecs (prog_funct' vl) (rev G)),
    initial_core gev G n = initial_core gev (rev G) n.
Proof.
  intros.
     unfold initial_core;  apply rmap_ext.
+   repeat rewrite level_make_rmap; auto.
+   intro loc; repeat rewrite resource_at_make_rmap; unfold initial_core'.
    if_tac; auto. case_eq (@Genv.invert_symbol (Ctypes.fundef function) type gev (@fst block Z loc)); intros; auto.
    replace (find_id i G) with (find_id i (rev G)); auto.
    clear - H SAME_IDS.
    assert (list_norepet (map (@fst _ _) (rev G))).
     eapply match_fdecs_norepet; eauto.
   clear - H; induction vl; simpl in *; auto.
   destruct a; destruct g; simpl in *; auto.
   rewrite map_app in H. rewrite list_norepet_app in H.
   destruct H as [? [? ?]]. constructor; auto.
   simpl in H1.
   apply list_disjoint_sym in H1.
   pose proof (list_disjoint_notin i H1).
   inv H0. spec H2. left; auto. contradict H2.
   rewrite map_rev. rewrite <- in_rev.
   clear - H2.
   induction vl; simpl in *; auto. destruct a. destruct g.
   destruct H2. simpl in *; left; auto. right; auto. right; auto. 
   rewrite map_app, list_norepet_app in H.   destruct H as [? [? ?]]; auto. 
    apply find_id_rev; auto.
    rewrite <- list_norepet_rev, <- map_rev. auto.
+ rewrite !ghost_of_make_rmap; auto.
Qed.

Definition hackfun phi0 phi :=
  level phi0 = level phi /\ ghost_of phi0 = ghost_of phi /\
  forall loc, (identity (phi0 @ loc) <-> identity (phi @ loc)) /\
                  (~identity (phi0 @ loc) -> (phi0 @ loc = phi @ loc)).

Lemma alloc_Gfun_inflate:
  forall n rho i f fs gv vl gev m0 m G0 G,
   Genv.alloc_global gev m0 (i, Gfun f) = Some m ->
   (forall phi : rmap,
    hackfun (inflate_initial_mem m0 (initial_core gev (G0 ++ (i, fs) :: G) n))
      phi ->
  (globvars2pred gv vl rho) phi) ->
  Genv.find_symbol gev i = Some (nextblock m0) ->
  ~ In i (map fst vl) ->
  forall phi : rmap,
  hackfun (inflate_initial_mem m (initial_core gev (G0 ++ (i, fs) :: G) n)) phi ->
      (globvars2pred gv vl rho) phi.
Proof.
 intros.
 apply H0.
 destruct H3 as [H3' [Hg H3]]; split. rewrite inflate_initial_mem_level in H3'|-*; auto.
 split.
 { unfold inflate_initial_mem in *; rewrite ghost_of_make_rmap in *; auto. }
 intro loc; specialize (H3 loc).
 clear - H3 H2 H1 H.
 assert (exists fs', find_id i (G0 ++ (i,fs)::G) = Some fs').
 clear. induction G0; simpl. exists fs; rewrite if_true; eauto.
 destruct IHG0 as [fs' ?]. destruct a. if_tac. subst i0; exists f; auto.
 eauto.
 forget (G0++(i,fs)::G) as GG.  clear G0 fs G.
 destruct H0 as [fs H0].
 destruct H3.
 destruct (eq_dec loc (nextblock m0, 0)).
 subst loc.
 unfold inflate_initial_mem in *.
 rewrite resource_at_make_rmap in *.
 unfold inflate_initial_mem' in *.
 replace (access_at m0 (nextblock m0, 0) Cur) with (@None permission) in *.
 replace (access_at m (nextblock m0, 0) Cur) with (Some Nonempty) in *.
 unfold initial_core in *. rewrite resource_at_make_rmap in *.
 unfold initial_core' in *.
 simpl in *.
 rewrite (Genv.find_invert_symbol gev i H1) in H3,H4. rewrite H0 in *. destruct fs.
 rewrite <- H3.
 split.
 split; intro. apply PURE_identity. apply NO_identity. intro. contradiction H5.
 apply NO_identity.
 symmetry. clear - H.
  unfold Genv.alloc_global in H.
  revert H; case_eq (alloc m0 0 1); intros. unfold drop_perm in H0.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable); inv H0.
  unfold access_at; simpl. apply alloc_result in H; subst b. rewrite PMap.gss.
 destruct (zle 0 0); try omegaContradiction. destruct (zlt 0 1); try omegaContradiction; simpl. auto.
 symmetry. apply nextblock_noaccess. simpl; unfold block; clear; xomega.
 replace (inflate_initial_mem m0 (initial_core gev GG n) @ loc)
   with (inflate_initial_mem m (initial_core gev GG n) @ loc); auto.
 clear - n0 H.
 unfold inflate_initial_mem; repeat rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
 assert (H8: access_at m0 loc = access_at m loc); [ | rewrite H8; auto].
  unfold Genv.alloc_global in H.
  revert H; case_eq (alloc m0 0 1); intros. unfold drop_perm in H0.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable); inv H0.
  unfold alloc; inv H. unfold access_at; simpl.
  destruct loc as [b z]; simpl in *.
  destruct (eq_dec b (nextblock m0)).
  subst. repeat rewrite PMap.gss. assert (z<>0) by congruence.
  destruct (zle 0 z). simpl. destruct (zlt z 1); try omegaContradiction. simpl.
  extensionality k.
  apply nextblock_noaccess. xomega.
   destruct (zlt z 1); try omegaContradiction. simpl.
  extensionality k.
  apply nextblock_noaccess. xomega.
 rewrite PMap.gss. rewrite PMap.gso by auto. rewrite PMap.gso by auto. auto.
 case_eq (access_at m loc Cur); auto.
  unfold Genv.alloc_global in H.
  revert H; case_eq (alloc m0 0 1); intros. unfold drop_perm in H0.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable); inv H0.
  unfold contents_at; simpl. unfold access_at in H1; simpl in H1.
  destruct (eq_dec b (fst loc)). subst. rewrite PMap.gss in H1.
  destruct (zle 0 (snd loc)); simpl in H1; auto.
  destruct (zlt (snd loc) 1); simpl in H1; auto. assert (snd loc = 0) by omega.
  destruct loc; apply alloc_result in H; simpl in *; congruence.
 clear r H8. inv H. simpl in *. rewrite H3 in *; rewrite PMap.gss in *.
  destruct (zle 0 (snd loc)); try omegaContradiction.
  destruct (zlt (snd loc) 1); try omegaContradiction. inv H1; auto.
  clear H8 r. inv H. simpl in H1; rewrite <- H3 in H1; rewrite PMap.gss in H1.
  destruct (zle 0 (snd loc)); try omegaContradiction.
  destruct (zlt (snd loc) 1); try omegaContradiction. inv H1; auto.
  rewrite PMap.gso in H1 by auto.
  replace (PMap.get (fst loc) (mem_contents m1)) with (PMap.get (fst loc) (mem_contents m0)); auto.
  inv H; simpl. rewrite PMap.gso; auto.
Qed.

Lemma resource_identity_dec:
 forall (r: resource), {identity r}+{~identity r}.
Proof.
intros. destruct r.
destruct (eq_dec sh Share.bot).
subst; left; apply NO_identity.
right. intro. apply identity_NO in H.
destruct H. inv H. contradiction n0; auto.
destruct H as [? [? ?]]. inv H.
 right; apply YES_not_identity.
left; apply PURE_identity.
Qed.

Lemma hackfun_sep:
 forall w1 w2 w w', hackfun w w' -> join w1 w2 w ->
   exists w1', exists w2', join w1' w2' w' /\ hackfun w1 w1' /\ hackfun w2 w2'.
Proof.
intros.
 pose proof I.
 destruct (make_rmap (fun loc => if resource_identity_dec (w1 @ loc) then core (w' @ loc) else w1 @ loc) (ghost_of w1) (level w))  as [w1' [? ?]]; clear H1.
 extensionality loc.
 unfold compose. if_tac. rewrite core_resource_at.
 replace (level w) with (level w') by (destruct H; auto).
 rewrite <- level_core. apply resource_at_approx.
 replace (level w) with (level w1) by (apply join_level in H0; destruct H0; auto).
 apply resource_at_approx.
 destruct (join_level _ _ _ H0) as [<- _].
 apply ghost_of_approx.
 pose proof I.
 destruct (make_rmap (fun loc => if resource_identity_dec (w2 @ loc) then core (w' @ loc) else w2 @ loc) (ghost_of w2) (level w))  as [w2' [? ?]]; clear H1.
 extensionality loc.
 unfold compose. if_tac. rewrite core_resource_at.
 replace (level w) with (level w') by (destruct H; auto).
 rewrite <- level_core. apply resource_at_approx.
 replace (level w) with (level w2) by (apply join_level in H0; destruct H0; auto).
 apply resource_at_approx.
 destruct (join_level _ _ _ H0) as [_ <-]; apply ghost_of_approx.
 exists w1'; exists w2'; split3.
 apply resource_at_join2. destruct H; congruence. destruct H; congruence.
 intro loc; apply (resource_at_join _ _ _ loc) in H0. destruct H3 as [-> _], H5 as [-> _].
 destruct H. destruct H1 as [Hg H1], (H1 loc).
 if_tac. apply H6 in H0. rewrite H0.
 if_tac.  apply H3 in H7. apply identity_core in H7.
 rewrite <- H7 at 2. apply core_unit.
 rewrite H5 by auto. apply core_unit.
 spec H5. contradict H6; apply split_identity in H0; auto. rewrite <- H5.
 if_tac. apply join_comm in H0. apply H7 in H0. rewrite H0. apply join_comm; apply core_unit.
 auto.
 destruct H3 as [_ ->], H5 as [_ ->].
 destruct H as (? & <- & _).
 apply ghost_of_join; auto.
 destruct H; split. apply join_level in H0; destruct H0; congruence.
 destruct H3 as [H3 ->]; split; auto.
 intro loc. rewrite H3. clear - H1. if_tac. pose (core_identity (w' @ loc)). intuition.
 intuition.
 destruct H; split. apply join_level in H0; destruct H0; congruence.
 destruct H5 as [H5 ->]; split; auto.
 intro loc. rewrite H5. clear - H1. if_tac. pose (core_identity (w' @ loc)). intuition.
 intuition.
Qed.

Lemma init_datalist_hack:
  forall b sh rho dl phi0 z,
   (init_data_list2pred dl sh (Vptr b z) rho) phi0 ->
  forall phi,
     hackfun phi0 phi ->
   readable_share sh ->
   (init_data_list2pred dl sh (Vptr b z) rho) phi.
Proof.
  induction dl; intros. destruct H0 as [H0' [Hg H0]]. simpl in *.
  apply all_resource_at_identity. intro loc; destruct (H0 loc).
  apply (resource_at_identity _ loc) in H. apply H2; auto.
  rewrite <- Hg; apply ghost_of_identity; auto.

  rename H1 into H_READABLE.
 simpl init_data_list2pred in H|-*.
 destruct H as [w1 [w2 [? [? ?]]]].
 destruct (hackfun_sep _ _ _ _ H0 H) as [w1' [w2' [? [? ?]]]].
 exists w1'; exists w2'; split3; auto.
 2: eapply IHdl; eauto.
 clear - H_READABLE H1 H4. destruct H4 as [H4' [Hg H4]].

  unfold init_data2pred in *;
  unfold mapsto, address_mapsto in *;
  destruct a; simpl in *;
  (destruct (readable_share_dec sh); [| tauto]);
  try
  (destruct H1 as [[H1' H1]|[H1x _]]; [|solve[inv H1x]];
        left; split;
    [ first [ apply I
           | apply sign_ext_range'; compute; split; congruence
           | apply zero_ext_range'; compute; split; congruence ]
    | simpl in H1 |- *;
      destruct H1 as [bl [[? H8] Hg']]; exists bl; split; [|rewrite <- Hg; auto]; split; [assumption | ]; intro loc; specialize (H8 loc);
      if_tac; [ destruct H8 as [p H8]; exists p; destruct (H4 loc) as [_ H5];
                rewrite <- H5; [rewrite H8; auto| rewrite H8; apply YES_not_identity]
              | destruct (H4 loc) as [HH _]; clear - H8 HH; intuition]]).
 rewrite address_mapsto_zeros_eq in H1|-*.
 rewrite nat_of_Z_max in *.
 split.  destruct H1; omega.
 destruct H1 as [H1' [H1 Hg1]]; split; [|simpl; rewrite <- Hg; auto].
 intro loc; specialize (H1 loc).
 assert (H99:  Z.max (Z.max z0 0) 0 = Z.max z0 0).
   apply Z.max_l. apply Zmax_bound_r. omega.
 rewrite H99 in *.
 hnf in H1|-*.
 if_tac; [destruct H1 as [p H1]; exists p; hnf in H1|-*; rewrite <- H4'; destruct (H4 loc) as [_ H5]
          | destruct (H4 loc) as [HH _]; intuition].
 rewrite <- H5; auto. rewrite H1; apply YES_not_identity.

 destruct (Map.get (ge_of rho) i); try destruct p; auto.
 destruct H1 as [[H1' H1]|[H1' H1]];  [left|right]; split; auto.
 destruct H1 as [bl [[? H8] Hg1]].
 exists bl; split; [|simpl; rewrite <- Hg; auto]; split; [assumption | ]; intro loc; specialize (H8 loc).
 destruct (H4 loc).
 hnf in H8|-*; if_tac. destruct H8 as [p H8]; exists p; hnf in H8|-*.
  rewrite <- H4'; rewrite <- H1; auto. rewrite H8; apply YES_not_identity.
 intuition.
 destruct H1 as [bl [? H8]].
 exists bl,x. destruct H8 as [[H8' H8] Hg1].
 split; [|simpl; rewrite <- Hg; auto].
 split; [assumption | ]; intro loc; specialize (H8 loc).
 destruct (H4 loc).
 hnf in H8|-*; if_tac. destruct H8 as [p H8]; exists p; hnf in H8|-*.
  rewrite <- H4'. rewrite <- H0. rewrite H8. reflexivity.
 rewrite H8.
 apply YES_not_identity.
 intuition.
 unfold mapsto_ in *.
 unfold mapsto in *.
  simpl in *.
 rewrite if_true in H1|-* by auto.
 destruct H1. destruct H. contradiction. destruct H as [ _ ?].
 right. split. hnf; auto.
 destruct H as [v2' ?]; exists v2'.
 destruct H as [x ?]; exists x.
 destruct H; split; auto.
 destruct H; split; auto.
 intros loc; specialize (H1 loc).
 destruct (H4 loc).
 rename H1 into H8.
 hnf in H8|-*; if_tac. destruct H8 as [p H8]; exists p; hnf in H8|-*.
  rewrite <- H4'; rewrite <- H3; auto. rewrite H8; apply YES_not_identity.
 intuition.
 hnf in H0|-*. rewrite <- Hg; auto.
Qed.

Lemma another_hackfun_lemma:
 forall n i v gev m G phi m0,
    hackfun (inflate_initial_mem m (initial_core gev G n)) phi ->
    Genv.alloc_global gev m0 (i, Gvar v) = Some m ->
    hackfun (inflate_initial_mem m0 (initial_core gev G n))
      (upto_block (nextblock m0) phi).
Proof.
 intros. destruct H; split.
 rewrite inflate_initial_mem_level in H|-*.
 unfold upto_block. rewrite level_only_blocks. auto.
 clear H; rename H1 into H.
 destruct H as [Hg H]; split.
 { unfold upto_block, only_blocks, inflate_initial_mem in *; rewrite !ghost_of_make_rmap in *; auto. }
 intro loc; specialize (H loc).
 destruct (plt (fst loc) (nextblock m0)).
 unfold upto_block. rewrite only_blocks_at. rewrite if_true by auto.
 replace (inflate_initial_mem m0 (initial_core gev G n) @ loc)
   with (inflate_initial_mem m (initial_core gev G n) @ loc); auto.
 try rename p into z.   (* Coq 8.3/8.4 compatibility *)
 clear - z H0.
 unfold inflate_initial_mem; repeat rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
 destruct (alloc_global_old _ _ _ _ H0 _ z) as [? ?]. rewrite H; rewrite H1; auto.
 unfold upto_block. rewrite only_blocks_at. rewrite if_false by auto.
 unfold inflate_initial_mem; repeat rewrite resource_at_make_rmap;
   unfold inflate_initial_mem'.
 replace (access_at m0 loc Cur) with (@None permission).
 clear.
 pose proof (core_identity (phi @ loc)).
 assert (identity (NO Share.bot bot_unreadable)) by apply NO_identity.
 intuition.
 symmetry; apply nextblock_noaccess. auto.
Qed.

Lemma hackfun_beyond_block:
  forall b w w', hackfun w w' -> hackfun (beyond_block b w) (beyond_block b w').
Proof.
 intros. destruct H.
 split. unfold beyond_block. repeat rewrite level_only_blocks. auto.
 clear H. destruct H0 as [Hg H0]; split.
 { unfold beyond_block, only_blocks; rewrite !ghost_of_make_rmap; auto. }
 intro loc; specialize (H0 loc).
 unfold beyond_block. repeat  rewrite only_blocks_at. if_tac. auto.
 clear. pose proof (core_identity (w @ loc)); pose proof (core_identity (w' @ loc)); intuition.
Qed.

Lemma Pos_to_nat_eq_S:
  forall b, Pos.to_nat b = S (nat_of_Z (Z.pos b) - 1).
Proof. intros. simpl; pose proof (Pos2Nat.is_pos b); omega.
Qed.


Lemma alloc_global_inflate_initial_eq:
  forall gev m0 i f m G n loc,
      Genv.alloc_global gev m0 (i, Gfun f) = Some m ->
   ~ identity (inflate_initial_mem m0 (initial_core gev G n) @ loc) ->
     inflate_initial_mem m0 (initial_core gev G n) @ loc =
      inflate_initial_mem m (initial_core gev G n) @ loc.
Proof.
intros. rename H0 into H9.
unfold inflate_initial_mem. simpl. rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
destruct loc.
destruct (plt b (nextblock m0)).
*
destruct (alloc_global_old gev _ _ _ H (b,z) p) as [? ?].
rewrite H0,H1. auto.
*
contradiction H9; clear H9.
unfold inflate_initial_mem. simpl. rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
unfold access_at; rewrite nextblock_noaccess.
apply NO_identity.
apply n0.
Qed.

(*
 Lemma alloc_global_inflate_identity_iff:
  forall gev m0 i f m G n loc,
      Genv.alloc_global gev m0 (i, Gfun f) = Some m ->
     (identity (inflate_initial_mem m0 (initial_core gev G n) @ loc) <->
      identity (inflate_initial_mem m (initial_core gev G n) @ loc)).
Proof.
intros.
unfold inflate_initial_mem. simpl. rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
destruct loc.
destruct (plt b (nextblock m0)).
*
destruct (alloc_global_old gev _ _ _ H (b,z) p) as [? [? ?]].
rewrite H0,H2. intuition.
*
unfold access_at at 1. rewrite nextblock_noaccess by auto.
split; [ intros _ | intro; apply NO_identity].
unfold Genv.alloc_global in H.
destruct (alloc m0 0 1) eqn:?.
destruct (peq b (nextblock m0)).
+
subst b. clear n0.
unfold drop_perm in H.
destruct (range_perm_dec m1 b0 0 1 Cur Freeable); inv H.
unfold access_at; simpl.
pose proof (alloc_result _ _ _ _ _ Heqp). subst b0.
rewrite PMap.gss.
destruct (zeq z 0). subst z.
destruct (zle 0 0); try omega. destruct (zlt 0 1); try omega.
simpl.
destruct (initial_core gev G n @ (nextblock m0, 0)); try apply NO_identity.
apply PURE_identity.
replace (if zle 0 z && zlt z 1
     then Some Nonempty
     else (mem_access m1) !! (nextblock m0) z Cur)
with ((mem_access m1) !! (nextblock m0) z Cur)
  by (destruct (zle 0 z); destruct (zlt z 1); try omega; auto).
destruct ((mem_access m1) !! (nextblock m0) z Cur) eqn:?; try apply NO_identity.
elimtype False.
pose proof (perm_alloc_3 _ _ _ _ _ Heqp z Cur) p.
spec H; [ | omega].
unfold perm.
rewrite Heqo. constructor.
+
unfold access_at.
simpl.
rewrite nextblock_noaccess.  apply NO_identity.
apply nextblock_drop in H. rewrite H in *. clear H.
apply nextblock_alloc in Heqp. rewrite Heqp in *; clear Heqp.
contradict n0.
apply Plt_succ_inv in n0; destruct n0; auto.
subst. contradiction n1; auto.
Qed.
*)

 Lemma alloc_global_identity_lemma3:
   forall gev m0 i f m G n loc,
    Genv.alloc_global gev m0 (i, Gfun f) = Some m ->
    identity (inflate_initial_mem m (initial_core gev G n) @ loc) ->
    identity (inflate_initial_mem m0 (initial_core gev G n) @ loc).
Proof.
intros until 1.
unfold inflate_initial_mem. simpl. rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
 intros.
  destruct (adr_range_dec (nextblock m0, 0) 1 loc).
  destruct loc; destruct a. subst b. assert (z=0) by omega. subst z.
  unfold access_at; rewrite nextblock_noaccess. apply NO_identity.
  simpl. apply Plt_strict.
  destruct (plt (fst loc) (nextblock m0)).
  destruct (alloc_global_old _ _ _ _ H _ p) as [? ?].
  rewrite H1,H2. auto.
  unfold access_at. rewrite nextblock_noaccess by auto.
  apply NO_identity.
Qed.

Lemma identity_inflate_at_Gfun:
  forall n i f gev m G0 G loc m0,
 list_norepet (map fst (G0 ++ G)) ->
 Genv.find_symbol gev i = Some (nextblock m0) ->
 Genv.alloc_global gev m0 (i, Gfun f) = Some m ->
 In i (map fst G) ->
 (identity (inflate_initial_mem m0 (initial_core gev (G0 ++ G) n) @ loc) <->
 identity (inflate_initial_mem m (initial_core gev (G0 ++ G) n) @ loc)).
Proof.
intros until m0. intros NR H8 ? ?.
destruct (eq_dec loc (nextblock m0, 0)).
*
subst loc.
unfold initial_core.
unfold inflate_initial_mem.
rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
rewrite !resource_at_make_rmap.
rewrite nextblock_access_empty
  by (apply Pos2Nat.inj_ge; omega).
split; intros _; [ |apply NO_identity].
unfold Genv.alloc_global in H.
destruct (alloc m0 0 1) eqn:?.
assert (H9: 0 <= 0 < 1) by (clear; omega).
assert (H6 := alloc_result _ _ _ _ _ Heqp); subst b.
assert (H1 := perm_drop_1 _ _ _ _ _ _ H 0 Cur H9).
destruct (perm_mem_access _ _ _ _ H1) as [p [H4 H5]].
assert (H2 := perm_drop_2 _ _ _ _ _ _ H 0 Cur p H9).
rewrite H5.
unfold perm in *.
unfold access_at in H5. simpl in H5. destruct ((mem_access m) !! (nextblock m0) 0 Cur); inv H5.
spec H2; [constructor | ].
destruct p; try solve [inv H2].
unfold initial_core'. simpl.
rewrite Genv.find_invert_symbol with (id:=i) by auto.
destruct (list_in_map_inv _ _ _ H0) as [[i' fd] [H10 H11]]; simpl in H10, H11.
subst i'.
rewrite find_id_i with (fs:=fd); auto.
destruct fd.
apply PURE_identity.
apply in_app. right; auto.
*
clear NR.
unfold initial_core.
unfold inflate_initial_mem.
rewrite !resource_at_make_rmap.
unfold inflate_initial_mem'.
rewrite !resource_at_make_rmap.
pose proof (Pos.ltb_spec (fst loc) (nextblock m0)).
destruct ((fst loc <? nextblock m0)%positive); inv H1.
destruct (alloc_global_old _ _ _ _ H loc H2) as [? ?].
rewrite H3.
rewrite H1; split; intro; auto.
destruct loc as [b ofs]. simpl fst in *; simpl snd in *.
rewrite (nextblock_access_empty m0) by (apply Pos.le_ge; auto).
split; intros _; [ |apply NO_identity].
replace (access_at m (b,ofs) Cur) with (@None permission).
apply NO_identity.
symmetry.
unfold Genv.alloc_global in H.
destruct (alloc m0 0 1) eqn:?.
assert (H6 := alloc_result _ _ _ _ _ Heqp); subst b0.
clear - n0 H2 Heqp H.
assert (b <> nextblock m0 \/ ofs <> 0). {
  destruct (eq_block b (nextblock m0)). subst. right. congruence. left; auto.
}
rewrite <- (access_drop_3 _ _ _ _ _ _ H) by (destruct H0; auto; right; omega).
rewrite <- (alloc_access_other _ _ _ _ _ Heqp)by (destruct H0; auto; right; omega).
apply nextblock_access_empty. zify; omega.
Qed.

Lemma global_initializers:
  forall (prog: program) G m n rho,
     list_norepet (prog_defs_names prog) ->
     all_initializers_aligned prog ->
    match_fdecs (prog_funct prog) G ->
    ge_of rho = filter_genv (globalenv prog) ->
    Genv.init_mem prog = Some m ->
     app_pred (globvars2pred (globals_of_env rho) (prog_vars prog) rho)
  (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)).
Proof.
  intros until rho. intros ? AL SAME_IDS RHO ?.
  unfold all_initializers_aligned in AL.
  unfold Genv.init_mem in H0.
  unfold globalenv, Genv.globalenv in *.
  unfold prog_vars, prog_funct in *.
  change (prog_defs prog) with (AST.prog_defs prog) in AL, SAME_IDS |- *.
  destruct (program_of_program prog) as [fl prog_pub main].
  forget (prog_comp_env prog) as cenv.
  clear prog.
  simpl in *|-. simpl prog_vars'. simpl initial_core.
  match goal with |- context [initial_core ?A] =>
     remember A as gev end.
  rewrite <- (rev_involutive fl) in *.
  rewrite alloc_globals_rev_eq in H0.
  forget (rev fl) as vl'. clear fl; rename vl' into vl.
  unfold prog_defs_names in H. simpl in  H.

  rewrite <- rev_prog_vars' in AL|-*.
  rewrite <- rev_prog_funct' in SAME_IDS.
  rewrite globvars2pred_rev.
  rewrite forallb_rev in AL.
  rewrite <- (rev_involutive G) in  SAME_IDS.
  rewrite match_fdecs_rev in SAME_IDS.
  2:{
    apply list_norepet_prog_funct'.
    rewrite <- list_norepet_rev, <- map_rev; auto.
  }
  rewrite initial_core_rev with (vl:=vl) by auto.
  rewrite map_rev in H. rewrite list_norepet_rev in H.
  forget (rev G) as G'; clear G; rename G' into G.
  rename H into H2.
  assert (H :=add_globals_hack _ _ prog_pub H2 Heqgev).
  assert (H1: forall j, In j (map (@fst _ _) G) -> ~ In j (map (@fst _ _) (prog_vars' vl))). {
    intros.
    pose proof (match_fdecs_in j _ _ H1 SAME_IDS).
    clear - H3 H2.
    intro.
    induction vl. inv H.
    inv H2. specialize (IHvl H5).
    destruct a as [i [a|a]]; simpl in *.
    destruct H3. subst j.
    clear - H H4.
    apply H4; clear H4. induction vl; simpl in *; auto.
    destruct a as [i' [a|a]]; auto .
    destruct H. simpl in *; subst; auto.
    right; auto.
    apply IHvl; auto.
    destruct H; subst.
    apply H4; clear - H3. induction vl; simpl in *; auto.
    destruct a as [i' [a|a]]; auto .
    destruct H3. simpl in *; subst; auto.
    right; auto.
    apply IHvl; auto.
  }
  assert (H1': forall j, In j (map fst (prog_funct' vl)) -> In j (map fst G)). {
   clear - SAME_IDS.
   forget (prog_funct' vl) as fs. intro.
   induction SAME_IDS. auto. simpl. intuition.
  }
  assert (NRG: list_norepet (map fst G)). {
     clear - SAME_IDS H2.
     eapply match_fdecs_norepet; eauto.
     apply list_norepet_prog_funct'; auto.
  }
  clear SAME_IDS Heqgev.
  change (map fst vl) with (map fst (@nil (ident*funspec)) ++ map fst vl) in H2.
  change G with (nil++G).
  set (G0 := @nil (ident*funspec)) in *.
  change G with (G0++G) in NRG.
  clearbody G0.
  move H2 after H. move H1 after H.

  assert (H3: forall phi, hackfun (inflate_initial_mem m (initial_core gev (G0++G) n)) phi ->
           (globvars2pred (globals_of_env rho) (prog_vars' vl) rho) phi).
  2:{
    apply H3. clear.
    split. auto.
    split; auto.
    intro loc. intuition.
  }
  intros. rename H3 into HACK; revert phi HACK.
                     (* The purpose of going through hackfun is doing this induction. *)
  revert H m G0 G NRG H2 H0 H1 H1'; induction vl; intros.
  + split. hnf; auto. apply resource_at_empty2.
    intro l. do 2 apply proj2 in HACK; specialize (HACK l).
    unfold inflate_initial_mem in HACK|-*.
    rewrite resource_at_make_rmap in *.
    unfold inflate_initial_mem' in HACK|-*.
    inversion H0; clear H0; subst m.
    unfold access_at, empty in HACK; simpl in HACK; rewrite PMap.gi in HACK.
      destruct HACK as [HACK _]. rewrite <- HACK. apply NO_identity.
    destruct HACK as (? & <- & _).
    unfold inflate_initial_mem, initial_core; rewrite !ghost_of_make_rmap.
    rewrite <- (ghost_core nil); apply core_identity.
  + simpl in H0.
    revert H0; case_eq (alloc_globals_rev gev empty vl); intros; try congruence.
    spec IHvl. clear - AL. simpl in AL. destruct a. destruct g; auto. simpl in AL.
      apply andb_true_iff in AL; destruct AL; auto.
     spec IHvl; [ intros | ].
    assert (H4': (Pos.to_nat b <= length vl)%nat). {
    clear - H4. rewrite Zlength_correct in H4.
      rewrite <- Z2Nat.inj_pos.
       rewrite <- Nat2Z.id .
       apply Z2Nat.inj_le. specialize (Pos2Z.is_pos b). omega.
       omega.
       omega.
     }
 fold fundef in *.
 assert (POS := Pos2Z.is_pos b). {
 rewrite H.
 rewrite Pos_to_nat_eq_S.
 replace (length vl - (nat_of_Z (Z.pos b) - 1))%nat with (S (length vl - S (nat_of_Z (Z.pos b) - 1)))%nat
  by (simpl;  pose proof (Pos2Nat.is_pos b); omega).
 simpl.
  replace (Datatypes.length vl - (Pos.to_nat b - 1))%nat with
             (S (Datatypes.length vl - S (Pos.to_nat b - 1)))%nat.
 apply iff_refl.
 clear - H4'; pose proof (Pos2Nat.is_pos b); omega.
 rewrite Zlength_cons. omega.
 }
 destruct a.
 assert (FS: Genv.find_symbol gev i = Some (nextblock m0)).
  assert (Genv.find_symbol gev i = Some (nextblock m0)).
    apply H. apply alloc_globals_rev_nextblock in H0. rewrite H0 .
      rewrite Zlength_cons.
 rewrite Z2Pos.id.
 rewrite Zlength_correct. omega.
 rewrite Zlength_correct. omega.
 simpl.
   apply alloc_globals_rev_nextblock in H0. rewrite H0 .
  replace (Pos.to_nat (Z.to_pos (Z.succ (Zlength vl))))
    with (S (length vl)).
2:{
rewrite Pos_to_nat_eq_S.
 rewrite Zlength_correct.
  rewrite Z2Pos.id by omega.
 unfold nat_of_Z.
 rewrite Z2Nat.inj_succ by omega.
 rewrite Nat2Z.id. omega.
}
 rewrite Nat.sub_diag. reflexivity.
  auto.
  destruct g.
* (* Gfun case *)
  simpl.
  specialize (IHvl m0 (G0(*++(p::nil)*)) G).
  apply IHvl; auto.
 - clear - H2. apply list_norepet_app in H2. destruct H2 as [? [? ?]].
    inv H0.
    apply list_norepet_app; split3; auto.
    apply list_disjoint_cons_right in H1; auto.
 - clear - H1'; intros; apply H1'. right; auto.
 -
  clear - NRG H2 FS HACK H3 H1'.
  specialize (H1' i). simpl in H1'. spec H1'; [auto | ].
  destruct HACK as [? ? ].
  split. rewrite <- H.
  unfold inflate_initial_mem. repeat rewrite level_make_rmap. auto.
  destruct H0 as [Hg H0]; split.
  unfold inflate_initial_mem in *; rewrite ghost_of_make_rmap in *; auto.
  intro; specialize (H0 loc).
  destruct H0.
  clear - NRG H2 FS H0 H1 H3 H1'.
  split.
  rewrite <- H0.
  clear - NRG H2 FS H3 H1'.
  apply (identity_inflate_at_Gfun n i f); auto.
  intro.
  rewrite <- H1.
  eapply alloc_global_inflate_initial_eq; eauto.
  clear - H3 H.
  contradict H.
  eapply alloc_global_identity_lemma3; eauto.
* (* Gvar case *)
  specialize (IHvl m0 G0 G NRG).
  spec IHvl. { clear - H2. apply list_norepet_app.  apply list_norepet_app in H2.
      destruct H2 as [? [? ?]].  inv H0.  split3; auto. simpl in H1.
    apply list_disjoint_cons_right in H1; auto.
  }
  specialize (IHvl H0).
 spec IHvl. intros. clear - H1 H4. specialize (H1 _ H4). contradict H1.
  right; auto.
  assert (FI: find_id i (G0++G) = None). {
  change (list_norepet (map fst G0 ++ (i::nil) ++ (map fst vl))) in H2.
  apply list_norepet_append_commut in H2. rewrite app_ass in H2.
 inv H2. specialize (H1 i).
 case_eq (find_id i (G0++G)); intros; auto. apply find_id_e in H2.
 contradiction H6. apply in_app. apply in_app_or in H2.
 destruct H2; [right|left].  change i with (fst (i,f)); apply in_map; auto.
 contradiction H1. apply in_map_fst in H2. auto.
 left; auto.
 }
  split. hnf; auto.
  simpl map.  simpl fold_right.
  assert (identity (ghost_of phi)) as Hg.
  { destruct HACK as (? & <- & _).
    unfold inflate_initial_mem, initial_core; rewrite !ghost_of_make_rmap.
    rewrite <- (ghost_core nil); apply core_identity. }
  pose proof (join_comm (join_upto_beyond_block (nextblock m0) phi Hg)).
  do 2 econstructor; split3; [ eassumption | |].
  unfold globvar2pred.
  unfold globals_of_env.
  rewrite RHO. unfold filter_genv, Map.get. simpl @fst; simpl @snd.
  assert (JJ:= alloc_global_inflate_same n i v _ _ (G0++G) _ H3).
 spec JJ.
 intro. unfold initial_core. rewrite resource_at_make_rmap. unfold initial_core'.
  simpl. if_tac; auto.
 rewrite Genv.find_invert_symbol with (id:=i); auto. rewrite FI; auto.
 simpl genv_genv.
 fold fundef in *. simpl.
 rewrite FS.
 assert (H99: exists t, match type_of_global {| genv_genv := gev; genv_cenv := cenv |} (nextblock m0) with
  | Some t => Some (Vptr (nextblock m0) Ptrofs.zero, t)
  | None => Some (Vptr (nextblock m0) Ptrofs.zero, Tvoid)
  end = Some (Vptr (nextblock m0) Ptrofs.zero, t)) by (destruct (type_of_global {| genv_genv := gev; genv_cenv := cenv |} (nextblock m0)); eauto).
(* destruct H99 as [t H99]; rewrite H99; clear t H99.*)
 case_eq (gvar_volatile v); intros; auto. rename H5 into H10.
  hnf; auto.

  unfold Genv.alloc_global in H3.
  revert H3; case_eq (alloc m0 0 (init_data_list_size (gvar_init v))); intros.
  invSome. invSome.
  assert (H90: Z.pos (nextblock m0) -1 = Zlength vl).
    clear - H0 H3.

  apply alloc_globals_rev_nextblock in H0. apply alloc_result in H3.
  subst.  rewrite H0.
  rewrite Zlength_correct.
  rewrite Z2Pos.id by omega. omega.
 destruct (H i (nextblock m0)) as [_ ?].
  rewrite Zlength_cons. rewrite H90.
  split; try omega.
  rewrite Zlength_correct. omega.
  spec H7. 
  simpl length.
  replace (Pos.to_nat (nextblock m0)) with (S (length vl)).
  rewrite minus_diag. reflexivity.
  clear - H90. rewrite Zlength_correct in H90. apply inj_eq_rev.
  rewrite inj_S. rewrite <- H90. clear.
  rewrite Pos_to_nat_eq_S.
  replace (Z.succ (Z.pos (nextblock m0) - 1)) with (Z.pos (nextblock m0)) by omega.
  unfold nat_of_Z.
  replace (S (Z.to_nat (Z.pos (nextblock m0)) - 1))
    with (Z.to_nat (Z.pos (nextblock m0)))
  by (rewrite Z2Nat.inj_pos; pose proof (Pos2Nat.is_pos (nextblock m0)); omega).
 rewrite Z2Nat.id by (pose proof (Pos2Z.is_pos (nextblock m0)); omega).
 auto.

pose proof (init_data_list_lem {| genv_genv := gev; genv_cenv := cenv |} m0 v m1 b m2 m3 m (initial_core gev (G0 ++ G) n) rho
     H3 H6 H9 H10) .
 spec H8.
 { unfold initial_core; simpl; rewrite ghost_of_make_rmap, <- (ghost_core nil); apply core_identity. }
 spec H8.
 clear - AL. simpl in AL. apply andb_true_iff in AL; destruct AL; auto.
 apply andb_true_iff in H. destruct H. apply Zlt_is_lt_bool; auto.
 specialize (H8 H5).
 spec H8.
 clear - AL. simpl in AL. apply andb_true_iff in AL; destruct AL; auto.
 apply andb_true_iff in H. destruct H; auto.
 specialize (H8 RHO). (* replace (nextblock m0) with b by congruence. *)
 eapply init_datalist_hack; eauto.
  apply alloc_result in H3; subst b.
  eassumption.
 apply hackfun_beyond_block; auto.
 apply readable_readonly2share.
 apply IHvl; auto.
 eapply another_hackfun_lemma; eauto.
Qed.
