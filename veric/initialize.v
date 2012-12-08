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


(* Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_float32: float -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> int -> init_data.  (**r address of symbol + offset *)
Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vfloat n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | None => None
      | Some b' => Mem.store Mint32 m b p (Vptr b' ofs)
      end
  | Init_space n => Some m
  end.
*)

Definition mapsto_zeros (n: Z) : spec :=
     fun (rsh sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l (Zmax n 0))
                                  (fun l' => yesat NoneP (VAL (Byte Byte.zero)) rsh sh l')
                                  noat).

Definition init_data2pred (ge: Genv.t fundef type) (d: init_data) : spec :=
 match d with
  | Init_int8 i => address_mapsto Mint8unsigned (Vint (Int.zero_ext 8 i))
  | Init_int16 i => address_mapsto Mint16unsigned (Vint (Int.zero_ext 16 i))
  | Init_int32 i => address_mapsto Mint32 (Vint i) 
  | Init_float32 r =>  address_mapsto Mfloat32 (Vfloat ((Float.singleoffloat r)))
  | Init_float64 r =>  address_mapsto Mfloat64 (Vfloat r)
  | Init_space n => mapsto_zeros n 
  | Init_addrof symb ofs =>
       match Genv.find_symbol ge symb with
       | None => mapsto_zeros (Genv.init_data_size d)
       | Some b' => address_mapsto Mint32 (Vptr b' ofs)
       end
 end.

Fixpoint init_data_list2pred  (ge: Genv.t fundef type)  (dl: list init_data) (sh: share) (b: block) (ofs: Z) : pred rmap :=
  match dl with
  | d::dl' => 
      sepcon (init_data2pred ge d extern_retainer sh (b, ofs)) 
                  (init_data_list2pred ge dl' sh b (ofs + Genv.init_data_size d))
  | nil => emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Share.Lsh else Share.top.

Definition globvar2pred (ge: Genv.t fundef type) (idv: ident * globvar type) : pred rmap :=
  match Genv.find_symbol ge (fst idv) with
  | None => emp
  | Some b => if (gvar_volatile (snd idv))
                       then  TT
                       else    init_data_list2pred ge (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) b 0
 end.

Definition globvars2pred (ge: Genv.t fundef type) (vl: list (ident * globvar type)) : pred rmap :=
  fold_right sepcon emp (map (globvar2pred ge) vl).

Lemma globvars2pred_rev:
  forall ge l, globvars2pred ge (rev l) = globvars2pred ge l.
Proof.
 intros. unfold globvars2pred. 
 rewrite map_rev.
  rewrite fold_left_rev_right.
 rewrite fold_symmetric.
 f_equal. extensionality x y; apply sepcon_comm.
 intros; apply sepcon_assoc.
 intros; apply sepcon_comm.
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
Admitted.


Definition upto_block' (b: block) (w: rmap) :=
  fun loc => if zlt (fst loc) b then w @ loc else NO Share.bot.

Definition upto_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (upto_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, upto_block'.
 simpl. destruct (zlt b' b).
 apply rmap_valid.
  simpl. auto.
 extensionality loc;  unfold compose.
  unfold upto_block'.
 if_tac; [ | reflexivity ].
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
Admitted.


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
  clear - H. admit.
  clear H m1.
  revert z m2 H0 H1 H2; induction dl'; intros.
  simpl app in *. simpl Genv.init_data_list_size in *.
  replace (z+0) with z by omega.
  destruct a; simpl in H2|-*; try solve [destruct H2; auto]; intros.
  simpl in H0.
  rewrite (Genv.store_init_data_list_outside ge dl m2  H0) by (right; simpl; omega).
  apply H1.
  simpl.
  assert (Genv.init_data_list_size dl >= 0) by admit.
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
    assert (Genv.init_data_size  a0 >= 0) by admit.
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

Lemma init_data_lem:
forall (ge : Genv.t fundef type) (v : globvar type) (b : block) (m1 : mem')
  (m3 m4 : Memory.mem) (phi0 : rmap) (a : init_data) (z : Z)
  (w1 wf : rmap),
   load_store_init_data1 ge m3 b z a ->
   contents_at m4 = contents_at m3 ->
   join w1 wf (beyond_block b (inflate_initial_mem m4 phi0)) ->
   (forall loc : address,
     if adr_range_dec (b, z) (Genv.init_data_size a) loc
     then identity (wf @ loc) /\ access_at m4 loc = Some (Genv.perm_globvar v)
     else identity (w1 @ loc)) ->
     gvar_volatile v = false ->
   initializer_aligned z a = true ->
  (init_data2pred ge a extern_retainer (readonly2share (gvar_readonly v)) (b, z)) w1.
Proof.
  intros. rename H4 into AL; rename H3 into VOL.
  assert (NU: nonunit (readonly2share (gvar_readonly v))).
  destruct (gvar_readonly v); simpl.
  admit. (* easy *)
    admit. (* easy *)
  Transparent load. 
  destruct a; unfold init_data2pred; simpl in H; unfold load in H;
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
    admit. (* looks true *)
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  match type of H with Some (decode_val ?ch ?A) = Some ?B => 
       assert (decode_val ch A=B) by (inv H; auto); clear H; 
        destruct (Genv.find_symbol ge i); try exists A
  end.
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
  unfold inflate_initial_mem'. rewrite H5.
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
  intro loc.
  specialize (H2 loc). simpl in H2.
  hnf. simpl Genv.init_data_size. rewrite Zmax_left by omega.
  if_tac. exists NU.
  destruct H2.
  apply join_comm in H1.
  apply (resource_at_join _ _ _ loc) in H1.
  apply H2 in H1. hnf; rewrite H1.
  unfold beyond_block. rewrite resource_at_make_rmap.
  unfold beyond_block'.
  rewrite if_false by (  destruct loc; destruct H; subst; simpl; unfold block; omega).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H5.
 unfold Genv.perm_globvar. rewrite VOL. rewrite preds_fmap_NoneP.
  assert (contents_at m4 loc = Byte Byte.zero).
    rewrite H0.
    destruct loc; destruct H; subst b0.
    rewrite (nth_getN m3 b z z0 4); auto.
    unfold size_chunk_nat in H4.
    forget (ZMap.get b (mem_contents m3)) as byt.
    clear - H4 H6.
    simpl size_chunk in *. simpl nat_of_Z in *.
    unfold nat_of_P in *. simpl Pmult_nat in *.
    assert (0 <= z0-z < 4) by omega.
    clear - H H4.
    admit.
    omega.
  destruct (gvar_readonly v);  repeat f_equal; auto.
  apply read_sh_readonly.
  apply H2.
Qed.


Lemma init_data_list_lem:
  forall ge m0 (v: globvar type) m1 b m2 m3 m4  phi0,
     alloc m0 0 (Genv.init_data_list_size (gvar_init v)) = (m1,b) ->
     Genv.store_zeros m1 b 0 (Genv.init_data_list_size (gvar_init v)) = Some m2 ->
     Genv.store_init_data_list ge m2 b 0 (gvar_init v) = Some m3 ->
     drop_perm m3 b 0 (Genv.init_data_list_size (gvar_init v)) 
               (Genv.perm_globvar v) = Some m4 ->
     gvar_volatile v = false ->
   initializers_aligned 0 (gvar_init v) = true ->
     init_data_list2pred ge (gvar_init v) (readonly2share (gvar_readonly v)) b 0 
            (beyond_block b (inflate_initial_mem m4 phi0)).
Proof.
intros. rename H3 into VOL. rename H4 into AL.
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
  clear - H0. admit.
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
  destruct (split_range w (b,Genv.init_data_list_size dl') (Genv.init_data_size a)) as [w1 [w2 [? ?]]].
  intros. apply (resource_at_join _ _ _ loc) in H5.
  specialize (H6 loc). rewrite if_true in H6. apply H6 in H5.
  rewrite H5.
   admit.  (* straightforward *)
  destruct loc. destruct H7; split; auto.
  assert (Genv.init_data_list_size dl >= 0) by admit.
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
  admit. (* easy *)
  admit. (* easy *)
 auto.       
  pose proof (load_store_init_data_lem1 H0 H1 _ _ _ H2).
  unfold phi in *; clear phi.
  eapply init_data_lem; try eassumption.
  clear - AL. apply andb_true_iff in AL. destruct AL; auto.

  destruct (join_assoc (join_comm H7) (join_comm H5)) as [wg [? ?]].
  specialize (IHdl  (dl' ++ (a::nil))  wg w2).
  replace (Genv.init_data_list_size (dl' ++ a :: nil)) with
             (Genv.init_data_list_size dl' + Genv.init_data_size a) in IHdl.
  apply IHdl; auto.
  apply andb_true_iff in AL; destruct AL; auto.
  rewrite app_ass; auto.
  intro loc; specialize (H6 loc); specialize (H8 loc); specialize (H4 loc).
  if_tac. rewrite if_true in H4; auto.
  destruct loc; destruct H11; auto.
  split; auto. 
  assert (Genv.init_data_size a >= 0) by admit.
  omega.
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
   assert (Genv.init_data_size a >= 0) by admit.
 omega.
 clear.
  induction dl'; simpl; intros; try omega.
Qed.

Definition all_initializers_aligned (prog: AST.program fundef type) := 
  forallb (fun idv => initializers_aligned 0 (gvar_init (snd idv))) (prog_vars prog) = true.

Lemma forallb_rev: forall {A} f (vl: list A), forallb f (rev vl) = forallb f vl.
Proof. induction vl; simpl; auto.
  rewrite forallb_app. rewrite IHvl. simpl. rewrite andb_comm.
  rewrite <- andb_assoc. f_equal; auto.
Qed.

Lemma global_initializers:
  forall prog G m n,
     list_norepet (prog_defs_names prog) ->
     all_initializers_aligned prog ->
    match_fdecs (prog_funct prog) G ->
    Genv.init_mem prog = Some m ->
     app_pred (globvars2pred (Genv.globalenv prog) (prog_vars prog))
  (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)).
Proof.
 intros until n. intros ? AL SAME_IDS ?.
 unfold all_initializers_aligned in AL.
 assert (IOK: initial_rmap_ok m (initial_core (Genv.globalenv prog) G n))
      by (apply initial_core_ok; auto).
  unfold Genv.init_mem in H0.
  unfold Genv.globalenv in *.
  destruct prog as [fl main vl].
  simpl in *.
  remember (Genv.add_globals (Genv.empty_genv fundef type) fl) as gev.
  rewrite <- (rev_involutive fl) in *.
  rewrite alloc_globals_rev_eq in H0.
  forget (rev fl) as vl'. clear fl; rename vl' into vl.
  unfold prog_vars in AL|-*. simpl in AL|-*.
  rewrite <- rev_prog_vars' in AL|-*.
  rewrite globvars2pred_rev.
  rewrite forallb_rev in AL.
  assert (exists ul, gev = Genv.add_globals (Genv.empty_genv fundef type) (rev vl ++ ul) /\
                              map fst (prog_funct' (rev vl ++ ul )) = map fst G /\
                              list_norepet (map (@fst _ _) (rev vl ++ ul))).
  exists nil; rewrite <- app_nil_end; auto.
  split; auto. split; auto.
     clear - SAME_IDS.
     unfold match_fdecs,prog_funct in SAME_IDS.
     simpl in SAME_IDS.
     forget (prog_funct' (rev vl)) as vl'.
     revert vl' SAME_IDS; induction G; destruct vl'; simpl; intros; auto.
     inv SAME_IDS. inv SAME_IDS. inv SAME_IDS; f_equal; auto.
  clear SAME_IDS. 
  clear IOK; assert (IOK: True) by auto.
  clear H Heqgev.
  revert m H0 H1 IOK; induction vl; simpl; intros.
 apply resource_at_empty2.
 intro l.
 unfold inflate_initial_mem.
 rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
  inv H0.
 unfold access_at, empty. simpl. rewrite ZMap.gi. apply NO_identity.
 invSome.
 destruct a; destruct g.
(* Gfun case *) 
 specialize (IHvl AL _ H0).
 spec IHvl.
 destruct H1 as [ul [? [? ?]]].
 exists ((i,Gfun f)::ul).
 subst gev.
 split3.
 f_equal. rewrite app_ass. simpl; auto.
 clear - H1. rewrite app_ass in H1. apply H1.
 rewrite app_ass in H2. apply H2.
 spec IHvl. auto.
 admit. (* quite possibly true, because the only difference
    between (inflate_initial_mem m0 ...) and (inflate_initial_mem m ...)
    is a PURE at a location where globvars2pred will yield emp *)
(* Gvar case *)
  spec IHvl.
 clear - AL. simpl in AL. apply andb_true_iff in AL. destruct AL; auto.
 specialize (IHvl _ H0).
 unfold globvars2pred. simpl map.
 unfold Genv.alloc_global in H3.
 revert H3; case_eq (alloc m0 0 (Genv.init_data_list_size (gvar_init v))); intros.
 invSome. invSome.
 destruct H1 as [ul [? [? ?]]].
 spec IHvl.
  exists ((i, Gvar v)::ul).
 rewrite app_ass in H1,H2,H4; split3; auto.
 unfold globvar2pred at 1. simpl @fst; simpl @snd.
 spec IHvl. auto.
 assert (Genv.find_symbol gev i = Some b).
   apply alloc_result in H. subst.
 rewrite <- alloc_globals_rev_eq in H0. 
 apply Genv.alloc_globals_nextblock in H0.
 rewrite H0.
 rewrite app_ass in *. simpl app in *.
 simpl nextblock.
 apply add_variables_nextblock; auto. 
 rewrite H7.
 case_eq (gvar_volatile v); intros.
 admit.  (* very likely true *)
 simpl fold_right.
 set (phi:= inflate_initial_mem m (initial_core gev G n)) in *.
 exists (beyond_block b phi), (upto_block b phi).
 split3.
 clear.  admit.  (* easy; make a lemma *)
 eapply init_data_list_lem; try eassumption.
 clear - AL. simpl in AL. apply andb_true_iff in AL; destruct AL; auto.
 change (globvars2pred gev (prog_vars' vl) (upto_block b phi)).
 replace (upto_block b phi) with (inflate_initial_mem m0 (initial_core gev G n)); auto.
 unfold phi in *; clear phi.
 clear - H H3 H5 H6.
 apply rmap_ext.
 clear.  admit.  (* easy; make a lemma for upto_block *)
 intro loc.
 unfold upto_block. rewrite resource_at_make_rmap. unfold upto_block'.
 unfold inflate_initial_mem.
 repeat rewrite resource_at_make_rmap.
 if_tac. 
 unfold inflate_initial_mem'.
 replace (access_at m0 loc) with (access_at m loc); auto.
 replace (contents_at m0 loc) with (contents_at m loc); auto.
 admit.  (* easy *)
 admit.  (* easy *)
 unfold inflate_initial_mem'.
 replace (access_at m0 loc) with (@None permission); auto.
 symmetry.
 admit.  (* easy *)
Qed.

Lemma disj_no_fun:  (* do we still need this? *)
  forall (fs: list (AST.ident * globdef fundef type)) ids, 
       list_disjoint (map (@fst _ _) fs) ids ->
       forall i, In i ids ->
      (Genv.genv_symb (Genv.add_globals (Genv.empty_genv _ _) fs)) ! i = None.
Proof.
intros. spec H i i.
assert (~In i (map (@fst _ _) fs)). intro. contradiction H; auto.
clear - H1; rename H1 into H0. unfold Genv.add_globals.
rewrite fold_right_rev_left. rewrite <- (rev_involutive fs). rewrite In_rev in H0.
rewrite <- map_rev in H0. remember (rev fs) as fs'; rewrite rev_involutive. clear - H0.
revert H0; induction fs'; simpl; intros.
rewrite Maps.PTree.gempty; auto. destruct a; simpl in *.
rewrite Maps.PTree.gso; [ | intro; subst; intuition]. 
apply IHfs'. contradict H0; auto.
Qed.
