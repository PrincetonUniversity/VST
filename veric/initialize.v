Load loadpath.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.Clight_lemmas.
Require Import veric.initial_world.


Lemma alloc_globals_app:
   forall F V (ge: Genv.t F V) m m2 vs vs',
  Genv.alloc_globals ge m (vs++vs') = Some m2 <->
    exists m', Genv.alloc_globals ge m vs = Some m' /\
                    Genv.alloc_globals ge m' vs' = Some m2.
Proof.
intros.
revert vs' m m2; induction vs; intros.
simpl.
intuition. exists m; intuition. destruct H as [? [H ?]]; inv H; auto.
simpl.
case_eq (Genv.alloc_global ge m a); intros.
specialize (IHvs vs' m0 m2).
auto.
intuition; try discriminate.
destruct H0 as [? [? ?]]; discriminate.
Qed.

Fixpoint alloc_globals_rev {F V} (ge: Genv.t F V) (m: mem) (vl: list (ident * globdef F V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
     match alloc_globals_rev ge m vl' with
     | Some m' => Genv.alloc_global ge m' v
     | None => None
     end
  end.

Lemma alloc_globals_rev_eq: 
     forall F V (ge: Genv.t F V) m vl,
     Genv.alloc_globals ge m (rev vl) = alloc_globals_rev ge m vl.
Proof.
intros.
revert m; induction vl; intros; auto.
simpl.
rewrite <- IHvl.
case_eq (Genv.alloc_globals ge m (rev vl)); intros.
case_eq (Genv.alloc_global ge m0 a); intros.
rewrite alloc_globals_app.
exists m0; split; auto.
simpl. rewrite H0; auto.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
elimtype False.
apply alloc_globals_app in H1.
destruct H1 as [m' [? ?]].
inversion2 H H1.
simpl in H2.
rewrite H0 in H2; inv H2.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
elimtype False.
apply alloc_globals_app in H0.
destruct H0 as [m' [? ?]].
inversion2 H H0.
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


 
Definition init_data2pred (ge: Genv.t fundef type) (d: init_data)  (sh: share) (a: val) (rho: environ) : mpred :=
 match d with
  | Init_int8 i => mapsto sh (Tint I8 Unsigned noattr) a (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh (Tint I16 Unsigned noattr) a (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh (Tint I32 Unsigned noattr) a (Vint i)
  | Init_float32 r =>  mapsto sh (Tfloat F32 noattr) a (Vfloat ((Float.singleoffloat r)))
  | Init_float64 r =>  mapsto sh (Tfloat F64 noattr) a (Vfloat r)
  | Init_space n => mapsto_zeros n sh a
  | Init_addrof symb ofs =>
       match ge_of rho symb with
       | Some (v, Tarray t _ att) => mapsto sh (Tpointer t att) a (offset_val v ofs)
       | _ => TT
       end
 end.

Fixpoint init_data_list2pred  (ge: Genv.t fundef type)  (dl: list init_data) 
                           (sh: share) (v: val)  (rho: environ) : pred rmap :=
  match dl with
  | d::dl' => 
      sepcon (init_data2pred ge d (Share.splice extern_retainer sh) v rho) 
                  (init_data_list2pred ge dl' sh (offset_val v (Int.repr (Genv.init_data_size d))) rho)
  | nil => emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Share.Lsh else Share.top.

Definition globvar2pred (ge: Genv.t fundef type) (idv: ident * globvar type) : assert :=
 fun rho =>
  match ge_of rho (fst idv) with
  | None => emp
  | Some (v, t) => if (gvar_volatile (snd idv))
                       then  TT
                       else    init_data_list2pred ge (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) v rho
 end.

Definition globvars2pred (ge: Genv.t fundef type) (vl: list (ident * globvar type)) : assert :=
  fold_right (lift2 sepcon) (lift0 emp) (map (globvar2pred ge) vl).

Lemma globvars2pred_rev:
  forall ge l, globvars2pred ge (rev l) = globvars2pred ge l.
Proof.
 intros. unfold globvars2pred. 
 rewrite map_rev.
  rewrite fold_left_rev_right.
 rewrite fold_symmetric.
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
          Some (Genv.genv_next ge + Z_of_nat (length vl)).
Proof.
 induction vl; intros.
 inv H. clear H3. simpl.
 replace (Some (Genv.genv_next ge + 0)) with (Genv.find_symbol (Genv.add_global ge (i,g)) i).
 Focus 2. 
  unfold Genv.add_global, Genv.find_symbol; simpl. rewrite PTree.gss. f_equal; unfold block; omega.
  forget (Genv.add_global ge (i, g)) as ge1.
  revert H2 ge1; induction ul; simpl; intros; auto.
  spec IHul; [intuition |].
  rewrite IHul.
  unfold Genv.find_symbol, Genv.add_global. simpl.
  rewrite PTree.gso; auto.
  simpl length.
  rewrite inj_S.
  unfold Zsucc.
  simpl.
  rewrite (IHvl  (Genv.add_global ge a) i g ul).
  f_equal.
  destruct ge;   unfold Genv.add_global, Genv.genv_next; simpl. omega.
  simpl in H. inv H; auto.
Qed.

Definition upto_block' (b: block) (w: rmap) :=
  fun loc => if zlt (fst loc) b then w @ loc else core (w @ loc).

Definition upto_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (upto_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, upto_block'.
 simpl. destruct (zlt b' b).
 apply rmap_valid.
 pose proof (rmap_valid w b' z'). unfold compose in H.
 revert H;  case_eq (w @ (b',z')); intros;
  repeat rewrite core_NO in *; 
  repeat rewrite core_YES in *;
  repeat rewrite core_PURE in *;
   simpl; intros; auto.
 extensionality loc;  unfold compose.
  unfold upto_block'.
 if_tac; try apply resource_at_approx.
 repeat  rewrite core_resource_at. rewrite <- level_core. 
apply resource_at_approx.
Defined.

Definition beyond_block' (b: block) (w: rmap) :=
  fun loc => if zlt (fst loc) b then core (w @ loc) else w @ loc.

Definition beyond_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (beyond_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, beyond_block'.
 simpl. destruct (zlt b' b).
 pose proof (rmap_valid w b' z'). unfold compose in H.
 revert H;  case_eq (w @ (b',z')); intros;
  repeat rewrite core_NO in *; 
  repeat rewrite core_YES in *;
  repeat rewrite core_PURE in *;
   simpl; intros; auto.
 pose proof (rmap_valid w b' z'). unfold compose in H.
 revert H;  case_eq (w @ (b',z')); intros;
  repeat rewrite core_NO in *; 
  repeat rewrite core_YES in *;
  repeat rewrite core_PURE in *;
   simpl; intros; auto.
 extensionality loc;  unfold compose.
  unfold beyond_block'.
 if_tac. repeat rewrite core_resource_at. rewrite <- level_core; apply resource_at_approx.
apply resource_at_approx.
Defined.


Lemma split_range: 
  forall phi base n, 
    (forall loc, adr_range base n loc -> 
       match phi @ loc with YES _ _ k _ => isVAL k | _ => True end) ->
   exists phi1, exists phi2, 
      join phi1 phi2 phi /\
      forall loc, if adr_range_dec base n loc then identity (phi2 @ loc) 
                                                      else identity (phi1 @ loc).
Proof.
  intros.
  assert (AV.valid (res_option oo (fun loc => if adr_range_dec base n loc then phi @ loc else core (phi @ loc)))).
  intro; intros. destruct base as [b0 z].
  pose proof (H (b,ofs)).
  unfold compose. if_tac; simpl in *. specialize (H0 H1).
   destruct H1; subst b0.
  revert H0; case_eq (phi @ (b,ofs)); simpl; intros; auto.
  destruct H1. subst; auto. clear H0.
  destruct (phi @ (b,ofs)); simpl; auto.
    rewrite core_NO; simpl; auto. rewrite core_YES; simpl; auto. rewrite core_PURE; simpl; auto.
  destruct (make_rmap _ H0 (level phi)) as [phi1 [J1 J2]].
  extensionality loc;   unfold compose.
  if_tac.  apply resource_at_approx.
  repeat rewrite core_resource_at. rewrite <- level_core. apply resource_at_approx.
  clear H0.
  assert (AV.valid (res_option oo (fun loc => if adr_range_dec base n loc then core (phi @ loc) else phi @ loc))).
  clear phi1 J1 J2.
  intro; intros. destruct base as [b0 z].
  unfold compose. if_tac; simpl in *.
  revert H0; case_eq (phi @ (b,ofs)); simpl; intros; auto.
    rewrite core_NO; simpl; auto. rewrite core_YES; simpl; auto. rewrite core_PURE; simpl; auto.
  case_eq (phi @ (b,ofs)); simpl; intros; auto. destruct k; auto.
  intros.
  pose proof (rmap_valid phi b ofs). unfold compose in H3. rewrite H1 in H3.
  simpl in H3. specialize (H3 _ H2). 
  if_tac. destruct H4. subst b0. specialize (H (b,ofs+i)).
  simpl in H. spec H; [auto |].
  destruct (phi @ (b,ofs+i)); inv H3. destruct H; inv H. apply H3.
  pose proof (rmap_valid phi b ofs). unfold compose in H2. rewrite H1 in H2.
  simpl in H2. destruct H2 as [n' [H2 ?]]; exists n'; split; auto.
  if_tac. specialize (H (b,ofs-z0)). spec H. destruct H4; subst; split; auto; omega.
  destruct (phi @ (b,ofs-z0)); inv H3. destruct H; inv H.
  destruct (phi @ (b,ofs-z0)); inv H3. reflexivity.
  destruct (make_rmap _ H0 (level phi)) as [phi2 [J3 J4]].
  extensionality loc;   unfold compose.
  if_tac.
  repeat rewrite core_resource_at. rewrite <- level_core. apply resource_at_approx.
  apply resource_at_approx.
 clear H0.
  exists phi1; exists phi2; split; auto.
  apply resource_at_join2; [congruence | congruence | ].
  intros; rewrite J2; rewrite J4. 
  if_tac.
    apply join_unit2. apply core_unit. auto.
    apply join_unit1. apply core_unit. auto.
  intros. rewrite J2; rewrite J4. if_tac; apply core_identity.
Qed.

Definition load_store_init_data1 (ge: Genv.t fundef type) (m: mem) (b: block) (p: Z) (d: init_data) : Prop :=
  match d with
  | Init_int8 n =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
  | Init_int16 n =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
  | Init_int32 n =>
      Mem.load Mint32 m b p = Some(Vint n)
  | Init_float32 n =>
      Mem.load Mfloat32 m b p = Some(Vfloat(Float.singleoffloat n))
  | Init_float64 n =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
  | Init_addrof symb ofs =>
      Mem.load Mint32 m b p = Some 
             match Genv.find_symbol ge symb with  
                | Some b' => Vptr b' ofs 
                | None => Vint Int.zero
              end        
  | Init_space n =>
      forall z, 0 <= z < Zmax n 0 -> 
           Mem.load Mint8unsigned m b (p+z) = Some (Vint Int.zero)
  end.

Definition initializer_aligned (z: Z) (d: init_data) : bool :=
  match d with
  | Init_int16 n => Zeq_bool (z mod 2) 0
  | Init_int32 n => Zeq_bool (z mod 4) 0
  | Init_float32 n =>  Zeq_bool (z mod 4) 0
  | Init_float64 n =>  Zeq_bool (z mod 8) 0
  | Init_addrof symb ofs =>  Zeq_bool (z mod 4) 0
  | _ => true
  end.
  
Fixpoint initializers_aligned (z: Z) (dl: list init_data) : bool :=
  match dl with 
  | nil => true 
  | d::dl' => andb (initializer_aligned z d) (initializers_aligned (z + Genv.init_data_size d) dl')
  end.

Lemma init_data_list_size_pos: forall dl, Genv.init_data_list_size dl >= 0.
Proof. induction dl; simpl; intros. omega.
 pose proof (Genv.init_data_size_pos a); omega.
Qed.


Lemma load_store_zeros:
  forall m b z N m', Genv.store_zeros m b z N = Some m' ->
         forall z', z <= z' < z + N -> load Mint8unsigned m' b z' = Some (Vint Int.zero).
Proof.
 intros.
 symmetry in H; apply Genv.R_store_zeros_correct in H.
  remember (Some m') as m1.
  revert z'  m' Heqm1 H0; induction H; intros. omegaContradiction.
  subst res.
 unfold n' in *; clear n'.
 destruct (eq_dec z' p). 
 Focus 2. apply IHR_store_zeros; auto. 
   clear - H0 n0.  destruct H0. omega.
  subst z'.
  destruct (load_store_similar _ _ _ _ _ _ e0) with Mint8unsigned; simpl; auto.
  omega.
  destruct H1. 
 simpl in H2. subst x.
  replace (Int.zero_ext 8 Int.zero) with (Int.zero) in H1 by reflexivity.
  rewrite <- H1.
  clear - H. apply Genv.R_store_zeros_complete in H.
 symmetry.
 symmetry in H; symmetry; eapply Genv.store_zeros_outside; eauto.
  right. simpl; omega.
  inv Heqm1.
Qed.

Lemma load_store_init_data_lem1:
  forall {ge m1 b D m2 m3},
   Genv.store_zeros m1 b 0 (Genv.init_data_list_size D) = Some m2 ->
   Genv.store_init_data_list ge m2 b 0 D = Some m3 ->
   forall dl' a dl, dl' ++ a :: dl = D ->
   load_store_init_data1 ge m3 b (Genv.init_data_list_size dl') a.
Proof.
  intros.
  pose proof (Genv.store_init_data_list_charact _ _ _ _ _ H0).
  subst D.
  change (Genv.init_data_list_size dl') with (0 + Genv.init_data_list_size dl'). 
  forget 0 as z.
  assert (forall z', z <= z' < z + Genv.init_data_list_size (dl' ++ a :: dl) ->
               Mem.load Mint8unsigned m2 b z' = Some (Vint Int.zero)).
  eapply load_store_zeros; eauto.
  clear H m1.
  revert z m2 H0 H1 H2; induction dl'; intros.
  simpl app in *. simpl Genv.init_data_list_size in *.
  replace (z+0) with z by omega.
  destruct a; simpl in H2|-*; try solve [destruct H2; auto]; intros.
  simpl in H0.
  rewrite (Genv.store_init_data_list_outside ge dl m2  H0) by (right; simpl; omega).
  apply H1.
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
  apply (equal_f ) with (b,ofs) in H5. simpl in H5. rewrite H5; auto.
  contradiction n. clear - v H5.
  unfold range_perm, perm in *.
  destruct v; split; auto; intros.
  apply (equal_f ) with (b,ofs) in H5. simpl in H5. rewrite <- H5; auto.
  simpl.
  pose proof (Genv.init_data_size_pos a0). 
  omega.
  clear - H2.
  simpl app in H2.
  forget (dl'++a::dl) as D.
  simpl in H2. destruct a0; simpl in *; try solve [destruct H2; auto]; intros.
  auto.
Qed.

Lemma read_sh_readonly:
  forall NU, read_sh = mk_lifted (readonly2share true) NU.
Proof.
  simpl. unfold read_sh. simpl. f_equal; auto.
Qed.  

Lemma rev_if_be_1: forall i, rev_if_be (i::nil) = (i::nil).
Proof. unfold rev_if_be; intros. destruct big_endian; reflexivity. 
Qed.

Lemma zero_ext_inj: forall i,
   Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.zero -> 
   i = Byte.zero.
Proof.
intros.
assert (MU: 256 < Int.max_unsigned).
 unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
  unfold two_power_nat, shift_nat in *; simpl in *. 
 replace (Zpos (4294967296 - 1)) with (4294967295). omega. reflexivity.
rewrite Int.zero_ext_and in H
 by (unfold Int.wordsize, Wordsize_32.wordsize; split; simpl in *; omega).
pose proof (Int.modu_and (Int.repr (Byte.unsigned i)) (Int.repr (two_p 8)) (Int.repr 8)).
 spec H0.
 apply Int.is_power2_two_p; simpl; omega.
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
 simpl proj_bytes in H1.
 destruct (ZMap.get i b); [inv H1 | | ].
2: simpl in H1;
(destruct (eq_block b0 b0); [ | congruence]);
(destruct (Int.eq_dec i0 i0); [ | congruence]);
simpl in H1;
(destruct n; simpl in H1; try congruence);
(destruct n; simpl in H1; try congruence);
(destruct n; simpl in H1; try congruence);
(destruct n; simpl in H1; try congruence);
if_tac in H1; inv H1.
 destruct (ZMap.get (i+1) b); [inv H1 | |  inv H1].
 destruct (ZMap.get (i+1+1) b); [inv H1 | |  inv H1].
 destruct (ZMap.get (i+1+1+1) b); [inv H1 | |  inv H1].
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
 unfold rev_if_be in H. destruct big_endian; simpl in H; apply H1 in H; intuition.
 clear H1 H.
  assert (forall i, Byte.unsigned i = 0 -> i = Byte.zero).
  clear. intros. pose proof (Byte.repr_unsigned i). rewrite H in H0. symmetry; auto.
 destruct H2 as [? [? [? ?]]]. apply H in H1; apply H in H2; apply H in H3; apply H in H4.
 subst.
 assert (j-i=0 \/ j-i=1 \/ j-i=2 \/ j-i=3) by omega.
 destruct H1 as [? | [?|[?|?]]]; rewrite H1; simpl; auto.
Qed.

Lemma init_data_lem:
forall (ge : Genv.t fundef type) (v : globvar type) (b : block) (m1 : mem')
  (m3 m4 : Memory.mem) (phi0 : rmap) (a : init_data) (z : Z) (rho: environ)
  (w1 wf : rmap),
   load_store_init_data1 ge m3 b z a ->
   contents_at m4 = contents_at m3 ->
   join w1 wf (beyond_block b (inflate_initial_mem m4 phi0)) ->
   (forall loc : address,
     if adr_range_dec (b, z) (Genv.init_data_size a) loc
     then identity (wf @ loc) /\ access_at m4 loc = Some (Genv.perm_globvar v)
     else identity (w1 @ loc)) ->
   forall (VOL:  gvar_volatile v = false)
          (AL: initializer_aligned z a = true)
           (LO:   0 <= z) (HI: z + Genv.init_data_size a < Int.modulus)
         (RHO: ge_of rho = filter_genv ge),
  (init_data2pred ge a  (Share.splice extern_retainer (readonly2share (gvar_readonly v)))
       (Vptr b (Int.repr z))) rho w1.
Proof.
  intros.
  assert (NU: nonunit (readonly2share (gvar_readonly v))).
  destruct (gvar_readonly v); simpl.
    clear.  unfold Share.Lsh. repeat intro.
    pose proof (fst_split_fullshare_not_bot).
    apply unit_identity in H. apply identity_share_bot in H. contradiction H0; apply H.
    clear. repeat intro. pose proof (Share.nontrivial). 
    apply unit_identity in H. apply identity_share_bot in H. contradiction H0; apply H.
  assert (APOS:= Genv.init_data_size_pos a).
  Transparent load.
  unfold init_data2pred, mapsto; simpl.
  rewrite Zmod_small by omega.
  repeat rewrite Share.unrel_splice_R.
  repeat rewrite Share.unrel_splice_L.
  destruct a; simpl in H; unfold load in H;
  try (if_tac in H; [ | discriminate H]);
  try match type of H with Some (decode_val ?ch ?B) = Some (?V) =>
            exists B; replace V with (decode_val ch B) by (inversion H; auto)
       end. 
(* Int8 *)
  repeat split; auto; clear H.
  apply Zone_divide.
  intro loc; specialize (H2 loc).
  simpl in H2. hnf. simpl size_chunk. if_tac; auto.
  exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf. rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'. 
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
(* Int16 *)
  repeat split; auto; clear H.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.  
(* Int32 *)
  repeat split; auto; clear H.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
(* Float32 *)
  repeat split; auto; clear H.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
(* Float64 *)
 repeat split; auto; clear H.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc).
  simpl in H2. simpl size_chunk. hnf; if_tac; auto.
  exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b0.
  apply nth_getN; simpl; omega.

  intro loc. hnf. specialize (H2 loc); simpl in H2.
 if_tac; auto.
    exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H3; subst; simpl; unfold block; omega).
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
    simpl. forget (ZMap.get z1 (ZMap.get b (mem_contents m3))) as byt.
    clear - H7.
    unfold decode_val in H7. 
    revert H7; case_eq (proj_bytes (byt::nil)); intros; try discriminate.
    simpl in  H. destruct byt; inv H.
    unfold decode_int in H7.
    replace (rev_if_be (i::nil)) with (i::nil) in H7 by (unfold rev_if_be; destruct big_endian; auto).
    simpl int_of_bytes in H7.
    replace (Byte.unsigned i + 0) with (Byte.unsigned i) in H7 by omega.
    f_equal.
   apply zero_ext_inj. forget (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) as j; inv H7; auto.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.

(* symbol case *)
 rewrite RHO.
  case_eq (filter_genv ge i); try destruct p; try destruct t; intros; auto.
  unfold filter_genv in H4.
  revert H4; case_eq (Genv.find_symbol ge i); intros; try discriminate.
  revert H5; case_eq (type_of_global ge b0); intros; try discriminate.
  inv H6. 
  rewrite H4 in H.
  match type of H with Some (decode_val ?ch ?A) = Some ?B => 
       assert (decode_val ch A=B) by (inv H; auto); clear H
  end.
 replace (offset_val (Vptr b0 Int.zero) i0) with (Vptr b0 i0)   
    by (unfold offset_val; rewrite Int.add_zero_l; auto).
 exists ( (getN (size_chunk_nat Mint32) z (ZMap.get b (mem_contents m3)))).
 repeat split; auto.
  simpl in AL. apply Zmod_divide.  intro Hx; inv Hx. apply Zeq_bool_eq; auto.
  intro loc; specialize (H2 loc). hnf. simpl Genv.init_data_size in H2.
   simpl size_chunk.
 if_tac.
  exists NU. hnf. 
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H7.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  rewrite H0.
  destruct loc; destruct H.  subst b1.
  apply nth_getN; simpl; omega.
  rewrite H0.
  destruct loc; destruct H; subst b1.
  apply nth_getN; simpl; omega.
  apply H2.
Qed.

Lemma store_zeros_access:  forall m b z N m',
      Genv.store_zeros m b z N = Some m' -> access_at m' = access_at m.
Proof.
 intros. symmetry in H; apply Genv.R_store_zeros_correct in H.
 remember (Some m') as m1. revert m' Heqm1; induction H; intros; inv Heqm1.
 auto.
 rewrite (IHR_store_zeros m'0 (eq_refl _)).
 clear - e0.
 Transparent store. unfold store in e0.
 if_tac in e0; inv e0. unfold access_at; simpl. auto.
Qed.

Lemma init_data_list_lem:
  forall ge m0 (v: globvar type) m1 b m2 m3 m4  phi0 rho,
     alloc m0 0 (Genv.init_data_list_size (gvar_init v)) = (m1,b) ->
     Genv.store_zeros m1 b 0 (Genv.init_data_list_size (gvar_init v)) = Some m2 ->
     Genv.store_init_data_list ge m2 b 0 (gvar_init v) = Some m3 ->
     drop_perm m3 b 0 (Genv.init_data_list_size (gvar_init v)) 
               (Genv.perm_globvar v) = Some m4 ->
  forall
   (SANITY: Genv.init_data_list_size (gvar_init v) < Int.modulus)
   (VOL:  gvar_volatile v = false)
   (AL: initializers_aligned 0 (gvar_init v) = true)
   (RHO: ge_of rho = filter_genv ge),
     init_data_list2pred ge (gvar_init v) (readonly2share (gvar_readonly v)) (Vptr b Int.zero) 
            rho (beyond_block b (inflate_initial_mem m4 phi0)).
Proof.
intros.
set (phi := beyond_block b (inflate_initial_mem m4 phi0)).
assert (forall loc, fst loc <> b -> identity (phi @ loc)).
  unfold phi; intros.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  if_tac. apply core_identity.
  unfold inflate_initial_mem.  rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'.
  unfold access_at.
  rewrite nextblock_noaccess. apply NO_identity. 
  rewrite (nextblock_drop _ _ _ _ _ _ H2).
  rewrite (Genv.store_init_data_list_nextblock _ _ _ _ _ H1).
  rewrite (Genv.store_zeros_nextblock _ _ _ _ H0).
  assert (nextblock m1 = Zsucc b /\ b = nextblock m0).
   clear - H. Transparent alloc. inv H.  simpl. auto. Opaque alloc.
 destruct H5; unfold block in *; omega.
 assert (forall loc, if adr_range_dec (b,0)  (Genv.init_data_list_size (gvar_init v)) loc
                             then access_at m4 loc = Some (Genv.perm_globvar v)
                             else identity (phi @ loc)).
  intro. if_tac.
     destruct loc; destruct H4; subst b0.
     unfold access_at. simpl. forget (Genv.perm_globvar v) as p.
      forget (Genv.init_data_list_size (gvar_init v)) as n.
     clear - H2 H5. unfold drop_perm in H2.
      destruct (range_perm_dec m3 b 0 n Cur Freeable); inv H2.
      simpl.  rewrite ZMap.gss.
       destruct (zle 0 z); try omegaContradiction. destruct (zlt z n); try omegaContradiction.
       simpl; auto.
    destruct loc.
  destruct (eq_dec b b0). subst b0.
  unfold phi. unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'. simpl. rewrite if_false by (unfold block; omega).
  unfold inflate_initial_mem.  rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'.
  replace (access_at m4 (b,z)) with (@None permission).
  apply NO_identity.
  symmetry.  transitivity (access_at m3 (b,z)).
  clear - H4 H2. unfold access_at; unfold drop_perm in H2.
   destruct (range_perm_dec m3 b 0 (Genv.init_data_list_size (gvar_init v)) Cur
         Freeable); inv H2. simpl. rewrite ZMap.gss.
  unfold adr_range in H4. destruct (zle 0 z); auto.
   destruct (zlt z (Genv.init_data_list_size (gvar_init v)) ); auto.
  contradiction H4. split; auto.
  transitivity (access_at m2 (b,z)).
  apply store_init_data_list_outside' in H1.
  destruct H1 as [? [? ?]]; congruence.
  transitivity (access_at m1 (b,z)).
  clear - H0. erewrite store_zeros_access; eauto.
  clear - H H4. Transparent alloc. inv H. Opaque alloc. unfold access_at; simpl.
  rewrite ZMap.gss. destruct (zle 0 z); auto.
   destruct (zlt z (Genv.init_data_list_size (gvar_init v)) ); auto.
  contradiction H4. split; auto.
   apply H3. auto.
  clear H3.
  assert (contents_at m4 = contents_at m3).
  clear - H2; unfold contents_at, drop_perm in *.
   destruct (range_perm_dec m3 b 0 (Genv.init_data_list_size (gvar_init v)) Cur
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
   unfold Int.zero.
   remember 0 as z. rewrite Heqz in H,H0,H1.
   replace z with (Genv.init_data_list_size dl') in AL,H4|-* by (subst; auto).
   clear z Heqz.
   assert (forall loc, if adr_range_dec (b,Genv.init_data_list_size dl') (Genv.init_data_list_size dl) loc 
                               then identity (w' @ loc)  else identity (w @ loc)).
  intro. subst. if_tac. rewrite <- core_resource_at. apply core_identity.
  specialize (H4 loc). rewrite if_false in H4 by auto; auto.
   clear Heqw' Heqw Heqdl' HeqD.
   revert dl' w' w AL H2 H4 H5 H6; induction dl; simpl; intros.
   apply all_resource_at_identity; intro loc.
   specialize (H6 loc); if_tac in H6; auto. destruct loc; destruct H7.
  omegaContradiction.
  assert (SANITY': Genv.init_data_list_size dl' + Genv.init_data_size a + Genv.init_data_list_size dl < Int.modulus).
  clear - H2 SANITY.
  admit.  (* easy *)
  destruct (split_range w (b,Genv.init_data_list_size dl') (Genv.init_data_size a)) as [w1 [w2 [? ?]]].
  intros. apply (resource_at_join _ _ _ loc) in H5.
  specialize (H6 loc). rewrite if_true in H6. apply H6 in H5.
  rewrite H5.
    unfold phi; clear. unfold beyond_block. rewrite resource_at_make_rmap.
      unfold beyond_block'. if_tac. 
   destruct (inflate_initial_mem m4 phi0 @ loc);
    [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto.
  unfold inflate_initial_mem; rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. destruct (access_at m4 loc); try destruct p; simpl; auto.
  destruct (phi0 @ loc); auto.
  destruct loc. destruct H7; split; auto.
  pose proof (init_data_list_size_pos dl).
  omega.
  exists w1; exists w2; split3; auto. 
  clear IHdl. 
  destruct (join_assoc H7 (join_comm H5)) as [wf [? ?]].
  assert (forall loc, if adr_range_dec (b,Genv.init_data_list_size dl') (Genv.init_data_size a) loc
                                 then identity (wf @ loc) /\ 
                                         access_at m4 loc = Some (Genv.perm_globvar v)
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
  clear - AL. apply andb_true_iff in AL. destruct AL; auto.
  pose proof (init_data_list_size_pos dl'); omega.
  pose proof (init_data_list_size_pos dl); omega.
  destruct (join_assoc (join_comm H7) (join_comm H5)) as [wg [? ?]].
  specialize (IHdl  (dl' ++ (a::nil))  wg w2).
  replace (Genv.init_data_list_size (dl' ++ a :: nil)) with
             (Genv.init_data_list_size dl' + Genv.init_data_size a) in IHdl.
  rewrite Int.add_unsigned.
Lemma max_unsigned_modulus:
  Int.max_unsigned + 1 = Int.modulus.
Admitted.
  repeat rewrite Int.unsigned_repr
       by (pose proof (init_data_list_size_pos dl'); pose proof (init_data_list_size_pos dl); 
      pose proof (Genv.init_data_size_pos a); pose proof max_unsigned_modulus; omega).
  apply IHdl; auto.
  apply andb_true_iff in AL; destruct AL; auto.
  rewrite app_ass; auto.
  intro loc; specialize (H6 loc); specialize (H8 loc); specialize (H4 loc).
  if_tac. rewrite if_true in H4; auto.
  destruct loc; destruct H11; auto.
  split; auto. 
  pose proof (Genv.init_data_size_pos a); omega.
  if_tac in H8; auto.
  rewrite if_false in H6.
  apply join_comm in H5.
  apply (resource_at_join _ _ _ loc) in H7.
  apply H8 in H7. rewrite H7; auto.
  destruct loc.
  intros [? ?]. subst b0.
  forget (Genv.init_data_list_size dl') as u.
 destruct (zlt z (u + Genv.init_data_size a)).
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
  forget (Genv.init_data_list_size dl') as u.
  assert (~ (u <= z < u + Genv.init_data_size a)) by (contradict H11; destruct H11; split; auto; omega).
  omega.
 rewrite if_false. apply H8 in H7. rewrite H7; auto.
 contradict H12. destruct H12; split; auto.
  pose proof (Genv.init_data_size_pos a); omega.
 clear.
  induction dl'; simpl; intros; try omega.
Qed.

Definition all_initializers_aligned (prog: AST.program fundef type) := 
  forallb (fun idv => andb (initializers_aligned 0 (gvar_init (snd idv)))
                                 (Zlt_bool (Genv.init_data_list_size (gvar_init (snd idv))) Int.modulus))
                      (prog_vars prog) = true.

Lemma forallb_rev: forall {A} f (vl: list A), forallb f (rev vl) = forallb f vl.
Proof. induction vl; simpl; auto.
  rewrite forallb_app. rewrite IHvl. simpl. rewrite andb_comm.
  rewrite <- andb_assoc. f_equal; auto.
Qed.
  
Lemma join_upto_beyond_block:
  forall b phi, join (beyond_block b phi) (upto_block b phi) phi.
Proof. intros. 
  unfold beyond_block, upto_block;
  apply resource_at_join2.
  repeat rewrite level_make_rmap. auto.
  repeat rewrite level_make_rmap. auto.
 intro;   repeat rewrite resource_at_make_rmap.
  unfold beyond_block', upto_block'. 
   if_tac. apply core_unit. apply join_comm; apply core_unit.
Qed.

Lemma store_zeros_contents1: forall m b z N m' loc,
      fst loc <> b ->
      Genv.store_zeros m b z N = Some m' -> 
      contents_at m loc = contents_at m' loc.
Proof.
 intros. symmetry in H0; apply Genv.R_store_zeros_correct in H0.
 remember (Some m') as m1. revert m' Heqm1; induction H0; intros; inv Heqm1.
 auto.
 transitivity (contents_at m' loc). 
 Transparent store. unfold store in e0.
 if_tac in e0; inv e0. unfold contents_at; simpl. rewrite ZMap.gso by auto. auto.
 eapply IHR_store_zeros; eauto.
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


Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.
Lemma nth_error_app1: forall {T} (al bl : list T) (j: nat),
     (j < length al)%nat ->
     nth_error (al++bl) j = nth_error al j.
Proof.
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try omegaContradiction.
   apply IHj. omega.
Qed.

Lemma alloc_global_old:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, fst loc < nextblock m ->
        access_at m loc = access_at m' loc /\ contents_at m loc = contents_at m' loc.
Admitted.

Lemma alloc_global_beyond2:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, fst loc > nextblock m ->
        access_at m' loc = None.
Admitted.

Lemma alloc_global_access:
 forall {F V} (ge: Genv.t F V) m i v m', Genv.alloc_global ge m (i, Gvar v) = Some m' ->
  forall z, access_at m' (nextblock m, z) = 
                    if range_dec 0 z (Genv.init_data_list_size (gvar_init v)) 
                    then Some (Genv.perm_globvar v) else None.
Admitted.

Lemma alloc_global_inflate_same:
  forall n i v gev m G m0,
  Genv.alloc_global gev m0 (i, Gvar v) = Some m ->
   (forall z : Z, initial_core gev G n @ (nextblock m0, z) = NO Share.bot) ->
   inflate_initial_mem m0 (initial_core gev G n) =
   upto_block (nextblock m0) (inflate_initial_mem m (initial_core gev G n)).
Proof.
 intros.
 apply rmap_ext.
  unfold upto_block, inflate_initial_mem; repeat rewrite level_make_rmap. auto.
 intro loc.
 unfold upto_block. rewrite resource_at_make_rmap.
 unfold upto_block'.
 unfold inflate_initial_mem.
 repeat rewrite resource_at_make_rmap.
 if_tac.
  destruct (alloc_global_old _ _ _ _ H _ H1);
 unfold inflate_initial_mem'; rewrite H2; rewrite H3; auto.
 destruct (eq_dec (fst loc) (nextblock m0)).
Focus 2.
 assert (access_at m loc = None).
  eapply alloc_global_beyond2; try eassumption. unfold block in *; omega.
 assert (access_at m0 loc = None).
  unfold access_at. apply nextblock_noaccess. auto.
 unfold inflate_initial_mem'; rewrite H2; rewrite H3; auto.
 rewrite core_NO; auto.
 (* End Focus 2*)
 clear H1.
 specialize (H0 (snd loc)).
 assert (access_at m0 loc = None).
  unfold access_at. apply nextblock_noaccess. rewrite <- e; omega.
 unfold inflate_initial_mem' at 1. rewrite H1.
  unfold inflate_initial_mem'.
 destruct loc; simpl in e; subst.
 rewrite (alloc_global_access _ _ _ _ _ H).
 if_tac. unfold Genv.perm_globvar. if_tac. simpl in H0. rewrite H0. rewrite core_NO; auto.
  if_tac; rewrite core_YES; auto.
 rewrite core_NO; auto.
Qed.

Lemma global_initializers:
  forall prog G m n rho,
     list_norepet (prog_defs_names prog) ->
     all_initializers_aligned prog ->
    match_fdecs (prog_funct prog) G ->
    ge_of rho = filter_genv (Genv.globalenv prog) ->
    Genv.init_mem prog = Some m ->
     app_pred (globvars2pred (Genv.globalenv prog) (prog_vars prog) rho)
  (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)).
Proof.
 intros until rho. intros ? AL SAME_IDS RHO ?.
 unfold all_initializers_aligned in AL.
  unfold Genv.init_mem in H0.
  unfold Genv.globalenv in *.
  destruct prog as [fl main vl].
  simpl in *.
  remember (Genv.add_globals (Genv.empty_genv fundef type) fl) as gev.
  rewrite <- (rev_involutive fl) in *.
  rewrite alloc_globals_rev_eq in H0.
  forget (rev fl) as vl'. clear fl; rename vl' into vl.
  unfold prog_defs_names in H. simpl in  H.  
  unfold prog_vars, prog_funct in *.  simpl in *.
  rewrite <- rev_prog_vars' in AL|-*.
  rewrite <- rev_prog_funct' in SAME_IDS.
  rewrite globvars2pred_rev.
  rewrite forallb_rev in AL.
  unfold match_fdecs in SAME_IDS.
  match type of SAME_IDS with ?A = ?B => assert (rev A = rev B) by (f_equal; auto) end.
  clear SAME_IDS; repeat rewrite <- map_rev in H1. rewrite rev_involutive in H1.
  rename H1 into SAME_IDS.
  replace (initial_core gev G n) with (initial_core gev (rev G) n).
   rewrite map_rev in H. rewrite list_norepet_rev in H.
  Focus 2.  clear - SAME_IDS H.
     unfold initial_core;  apply rmap_ext.
    repeat rewrite level_make_rmap; auto.
    intro loc; repeat rewrite resource_at_make_rmap; unfold initial_core'.
    if_tac; auto. case_eq (Genv.invert_symbol gev (fst loc)); intros; auto.
    replace (find_id i G) with (find_id i (rev G)); auto.
    admit.  (* easy *)
   forget (rev G) as G'; clear G; rename G' into G.
  assert (forall id b, 0 <= b-1 < Zlength vl ->
                           (Genv.find_symbol gev id = Some b <->
                            nth_error (map (@fst _ _) (rev vl)) (nat_of_Z (b-1))  = Some id)).
     intros. subst.
     clear - H H1. rename H1 into Hb; revert H; induction vl; simpl; intros;
       try rewrite Zlength_nil in *.
      unfold Genv.find_symbol; simpl. rewrite PTree.gempty.
     intuition. 
       destruct a. inv H. rewrite Zlength_cons in Hb.
       destruct (eq_dec (b-1) (Zlength vl)).
       admit.  (* seems true *)
        spec IHvl ; [ omega |].
      specialize (IHvl H3).
      rewrite Genv.add_globals_app.
      unfold Genv.add_globals at 1. simpl.
        unfold Genv.find_symbol.
       unfold Genv.add_global; simpl. 
      destruct (eq_dec id i). subst i. rewrite PTree.gss.
      rewrite Genv.genv_next_add_globals. rewrite <- Zlength_correct. simpl Genv.genv_next.
     rewrite map_app.
     rewrite In_rev in H2. rewrite <- map_rev in H2.
     clear - H2 Hb.  revert H2; induction (rev vl); intro. simpl. split; intro. inv H; simpl. auto.
      f_equal. 
     destruct (eq_dec b 1); subst; auto.
     admit.  (* easy *)
     clear IHl.
     rewrite Zlength_cons.
    split; intro. assert (b = 1 + Zsucc (Zlength l)) by congruence.
    subst b.
    replace (nat_of_Z (1 + Zsucc (Zlength l) - 1)) with (length (map (@fst _ _) (a::l)) + 0)%nat.
    rewrite nth_error_app.
    simpl nth_error. auto.
    rewrite Zlength_correct. simpl map. simpl length. rewrite map_length.
    clear. unfold Zsucc.
    replace (1 + (Z_of_nat (length l) + 1) - 1) with (1 + Z_of_nat (length l)) by omega.
    rewrite nat_of_Z_plus by omega. rewrite nat_of_Z_eq.
    change (nat_of_Z 1) with (1%nat). omega.
    admit.  (* easy *)
    rewrite PTree.gso by auto. 
  rewrite map_app.
  destruct IHvl.
  split; intro. apply H in H1. rewrite nth_error_app1; auto.
    admit.  (* easy *)
  assert (nat_of_Z (b-1) < length (map (@fst _ _) (rev vl)))%nat.
    clear - n H1. admit.
  rewrite nth_error_app1 in H1 by auto.
  apply H0 in H1. auto.
  assert (exists ul, 
                 (forall (id : ident) (b : Z),   0 <= b-1 < Zlength vl ->
                  (Genv.find_symbol gev id = Some b <-> 
                        nth_error (map fst (rev vl)) (nat_of_Z (b - 1)) = Some id)) /\
                map fst (prog_funct' (vl ++ ul )) = map fst G /\
                list_norepet (map (@fst _ _) (vl ++ ul))).
  exists nil; rewrite <- app_nil_end; auto.
  split; auto. split; auto.
     clear - SAME_IDS. forget (prog_funct' vl) as fl.
     revert fl SAME_IDS; induction G; destruct fl; simpl; intros; inv SAME_IDS; auto.
     f_equal; auto.
  clear SAME_IDS H Heqgev H1.
  destruct H2 as [ul [? [? ?]]].
  revert H m G H0 H1; induction vl; simpl; intros.
 apply resource_at_empty2.
 intro l.
 unfold inflate_initial_mem.
 rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
 inversion H0; clear H0; subst m.
 unfold access_at, empty. simpl. rewrite ZMap.gi. apply NO_identity.
 revert H0; case_eq (alloc_globals_rev gev empty vl); intros; try congruence.
 spec IHvl. clear - AL. simpl in AL. destruct a. destruct g; auto. simpl in AL.
   apply andb_true_iff in AL; destruct AL; auto.
 spec IHvl. simpl in H2. inv H2; auto.
  spec IHvl; [ intros | ].
 rewrite H. rewrite map_app. rewrite nth_error_app1; [intuition |].
 clear - H4. admit.
  rewrite Zlength_cons; omega.
  destruct a; destruct g.
  destruct G; inv H1.
  specialize (IHvl m0 G H0 H6).
  destruct p. simpl @fst in *; simpl @snd in *.
    admit. (* quite possibly true, because the only difference
    between (inflate_initial_mem m0 ...) and (inflate_initial_mem m ...)
    is a PURE at a location where globvars2pred will yield emp *)
(* Gvar case *)
  specialize (IHvl m0 G H0 H1).
  unfold globvars2pred.
  simpl map.  simpl fold_right.
  pose proof (join_upto_beyond_block (nextblock m0)
     (inflate_initial_mem m (initial_core gev G n))).
  do 2 econstructor; split3; [ eassumption | |].
  unfold globvar2pred. rewrite RHO. unfold filter_genv. simpl @fst; simpl @snd.
  unfold Genv.alloc_global in H3.
  revert H3; case_eq (alloc m0 0 (Genv.init_data_list_size (gvar_init v))); intros.
  invSome. invSome.
  assert (b-1 = Zlength vl).
    clear - H0 H3. admit.
 destruct (H i b) as [_ ?].
  rewrite Zlength_cons; rewrite H6.
  split; try omega.
  admit. (* trivial *)
  spec H7. rewrite H6. clear. rewrite map_app.  rewrite Zlength_correct.
   rewrite nat_of_Z_of_nat. replace (length vl) with (length (map (@fst _ _ )(rev vl)) + 0)%nat.
    rewrite nth_error_app. simpl. auto. rewrite plus_comm. simpl.
    rewrite map_rev. rewrite rev_length. rewrite map_length. auto.
 rewrite H7.
 assert (H99: exists t, match type_of_global gev b with
  | Some t => Some (Vptr b Int.zero, t)
  | None => Some (Vptr b Int.zero, Tvoid)
  end = Some (Vptr b Int.zero, t)) by (destruct (type_of_global gev b); eauto).
 destruct H99 as [t H99]; rewrite H99; clear t H99.
 case_eq (gvar_volatile v); intros; auto.
  replace (nextblock m0) with b.
 eapply init_data_list_lem; try eassumption.
 clear - AL. simpl in AL. apply andb_true_iff in AL; destruct AL; auto.
 apply andb_true_iff in H. destruct H. apply Zlt_is_lt_bool; auto.
 clear - AL. simpl in AL. apply andb_true_iff in AL; destruct AL; auto.
 apply andb_true_iff in H. destruct H; auto.
  apply alloc_result in H3; auto.
  change (fold_right (lift2 sepcon) (lift0 emp) (map (globvar2pred gev) (prog_vars' vl)))
      with  (globvars2pred gev (prog_vars' vl)).
 replace (upto_block (nextblock m0) (inflate_initial_mem m (initial_core gev G n)))
        with (inflate_initial_mem m0 (initial_core gev G n)); auto.
 assert (forall z, initial_core gev G n @ (nextblock m0,z) = NO Share.bot).
 intros; unfold initial_core; rewrite resource_at_make_rmap.
   unfold initial_core'. simpl. if_tac; auto. subst z.
 rewrite (Genv.find_invert_symbol gev i).
  replace (find_id i G) with (@None funspec); auto.
  clear - H2 H1. admit.
  destruct (H i (nextblock m0)) as [_ ?]. 
  clear - H0. admit.
  apply H5. 
  clear - H0. admit.
 clear - H3 H5.
 eapply alloc_global_inflate_same; eauto.
Qed.

