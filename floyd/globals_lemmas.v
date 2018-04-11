Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
(*Require Import VST.floyd.unfold_data_at.*)
Local Open Scope logic.

Fixpoint fold_right_sepcon' (l: list(environ->mpred)) : environ -> mpred :=
 match l with
 | nil => emp
 | b::nil => b
 | b::r => b * fold_right_sepcon' r
 end.

Lemma fold_right_sepcon'_eq:
  fold_right_sepcon' = @fold_right (environ->mpred) _ sepcon emp.
Proof.
extensionality l rho.
induction l; auto.
simpl.
destruct l. simpl. rewrite sepcon_emp. auto.
f_equal; auto.
Qed.


Lemma orp_dup {A}{ND: NatDed A}: forall P: A, P || P = P.
Proof. intros. apply pred_ext.
apply orp_left; apply derives_refl.
apply orp_right1; apply derives_refl.
Qed.

Lemma unsigned_repr_range: forall i, 0 <= i -> 0 <= Ptrofs.unsigned (Ptrofs.repr i) <= i.
Proof.
  intros.
  rewrite Ptrofs.unsigned_repr_eq.
  pose proof Z.mod_le i Ptrofs.modulus H.
  pose proof Z.mod_bound_pos i Ptrofs.modulus H.
  set (x := Ptrofs.modulus) in *.
 revert x H0 H1.
  rewrite Ptrofs.modulus_power.
 intros.
  unfold Ptrofs.zwordsize,  Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in x.
  destruct (Archi.ptr64);
  (compute in x; subst x; spec H0; [omega| ]; spec H1; omega).
Qed.

Lemma tc_globalvar_sound:
  forall Delta i t gz idata rho,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
   gvar_volatile gz = false ->
   gvar_init gz = idata ->
   tc_environ Delta rho ->
   globvar2pred (globals_of_env rho) (i, gz) rho |-- init_data_list2pred idata (readonly2share (gvar_readonly gz)) (eval_var i t rho) rho.
Proof.
pose (H2:=True).
pose (H4:=True).
pose (H5:=True); intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b ?].
unfold globals_of_env. 
rewrite H11. rewrite H1.
rewrite H3; simpl.
unfold eval_var.
unfold Map.get. rewrite H10. rewrite H11.
auto.
Qed.

Lemma tc_globalvar_sound':
  forall Delta i t gv idata rho,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
   gvar_volatile gv = false ->
   gvar_init gv = idata ->
   tc_environ Delta rho ->
   globvar2pred (globals_of_env rho)  (i, gv) rho |--
   init_data_list2pred idata (readonly2share (gvar_readonly gv)) (globals_of_env rho i) rho.
Proof.
pose (H2:=True).
pose (H4:=True).
pose (H5:=True); intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b ?].
unfold globals_of_env. 
rewrite H11. rewrite H1.
rewrite H3; simpl. auto.
Qed.

Definition zero_of_type (t: type) : val :=
 match t with
  | Tfloat _ _ => Vfloat Float.zero
  | _ => Vint Int.zero
 end.


Definition eval_sgvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ge_of rho) id with
| Some b => Vptr b Ptrofs.zero
| None => Vundef
end.

Lemma eval_sgvar_lemma1:
  forall (F: val -> mpred) ofs id t,
    F Vundef |-- FF ->
   `F (`(offset_val ofs) (eval_sgvar id t)) =
   (EX v:val, local (locald_denote (sgvar id v)) && `(F (offset_val ofs v))).
Proof.
intros.
extensionality rho.
unfold_lift. unfold local, lift1.
unfold eval_sgvar.
unfold Map.get. simpl.
apply pred_ext.
unfold sgvar_denote.
destruct (ge_of rho id).
apply exp_right with (Vptr b Ptrofs.zero).
normalize.
eapply derives_trans; [ apply H | ].
apply FF_left.
unfold sgvar_denote.
apply exp_left; intro; normalize.
destruct (ge_of rho id).
subst. auto.
contradiction.
Qed.

Definition init_data2pred' {cs: compspecs}
     (Delta: tycontext) (gv: globals) (d: init_data)  (sh: share) (ty: type) (v: val) : environ -> mpred :=
 match d with
  | Init_int8 i => `(mapsto sh tuchar v (Vint (Int.zero_ext 8 i)))
  | Init_int16 i => `(mapsto sh tushort v (Vint (Int.zero_ext 16 i)))
  | Init_int32 i => `(mapsto sh tuint v (Vint i))
  | Init_int64 i => `(mapsto sh tulong v (Vlong i))
  | Init_float32 r =>  `(mapsto sh tfloat v (Vsingle r))
  | Init_float64 r =>  `(mapsto sh tdouble v (Vfloat r))
  | Init_space n =>  if zeq n (sizeof ty)
                                   then `(data_at_ sh ty v)
                                   else `(memory_block sh n v)
  | Init_addrof symb ofs =>
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Tarray t n' att) =>
         `(mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) (gv symb)))
      | None, Some Tvoid => TT
(*
      | None, Some t => `(mapsto sh (Tpointer t noattr) v) (`(offset_val ofs) (eval_sgvar symb t))
*)
      | None, Some t => EX s:val, local (locald_denote (gvar symb s)) && `((mapsto sh (Tpointer t noattr) v) (offset_val (Ptrofs.unsigned ofs) s))
      | Some _, Some (Tarray t _ att) => `(memory_block sh 4 v)
      | Some _, Some Tvoid => TT
      | Some _, Some (Tpointer (Tfunction _ _ _) _) => `(memory_block sh 4 v)
      | _, _ => TT
      end
 end.

Lemma unsigned_repr_le: forall i, 0 <= i -> Int.unsigned (Int.repr i) <= i.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  apply Zmod_le; try assumption.
  pose proof Int.Z_mod_modulus_range i.
  omega.
Qed.

Lemma mapsto_aligned:
 forall t ch, access_mode t = By_value ch ->
  forall  sh b z p,
  mapsto sh t (Vptr b z) p
   |-- !! (Memdata.align_chunk ch | Ptrofs.unsigned z).
Proof.
intros.
unfold mapsto. simpl.
rewrite H.
if_tac.
simple_if_tac.
apply FF_left.
apply orp_left. normalize. clear H H0.
rewrite (res_predicates.address_mapsto_align).
match goal with |- ?A |-- ?B => change (predicates_hered.derives A B) end.
intros ? ?. destruct H. apply H0.
normalize.
clear.
rewrite (res_predicates.address_mapsto_align).
match goal with |- ?A |-- ?B => change (predicates_hered.derives A B) end.
intros ? ?. destruct H. apply H0.
simple_if_tac.
apply FF_left.
normalize.
Qed.

Lemma unpack_globvar_aux1 {cs: compspecs}:
  forall sh t b v i_ofs,
  Ptrofs.unsigned i_ofs + sizeof (Tpointer t noattr) <= Ptrofs.max_unsigned ->
               mapsto sh (Tpointer t noattr) (Vptr b i_ofs) v
                   |-- memory_block sh 4 (Vptr b i_ofs).
Proof.
 intros. 
 assert_PROP ((Memdata.align_chunk Mptr | Ptrofs.unsigned i_ofs)).
    apply mapsto_aligned; reflexivity.
 eapply derives_trans; [ apply mapsto_mapsto_ | ].
 rewrite (memory_block_mapsto_ _ (Tpointer t noattr)); auto.
 unfold size_compatible; unfold Ptrofs.max_unsigned in H; omega.
 simpl. apply align_compatible_rec_by_value with Mptr; auto.
Qed.

Lemma sizeof_Tpointer {cs: compspecs} : forall t, 
       sizeof (Tpointer t noattr) = if Archi.ptr64 then 8 else 4.
Proof.
intros.
simpl. reflexivity.
Qed.

Lemma init_data_size_space {cs: compspecs}:
 forall t, init_data_size (Init_space (sizeof t)) = sizeof t.
Proof. intros.
 pose proof (sizeof_pos t).
 unfold init_data_size. rewrite Z.max_l; auto. omega.
Qed.

(*
ofs + sizeof t < Ptrofs.modulus
align_compatible_rec cenv_cs t ofs
ofs + init_data_size a <= Ptrofs.max_unsigned
*)

Lemma init_data2pred_rejigger {cs: compspecs}:
  forall (Delta : tycontext) (t : type) (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs v,
  field_compatible t nil (Vptr b (Ptrofs.repr ofs)) ->
  (*legal_alignas_type t = true -> *)
  0 <= ofs ->
  ofs + init_data_size idata <= Ptrofs.max_unsigned ->
  tc_environ Delta rho ->
  v = Vptr b (Ptrofs.repr 0) ->
(*   (alignof t | Ptrofs.unsigned (Ptrofs.repr ofs)) -> *)
  readable_share sh ->
   init_data2pred idata sh (offset_val ofs v) rho
    |-- init_data2pred' Delta (globals_of_env rho) idata sh t (offset_val ofs v) rho .
Proof.
intros until v.
intros H1 H6' H6 H7 H8 (*H1''*) RS.
(* 
hnf in H1. simpl in H1. destruct H1 as [_ [H9 _]]. clear H6.
assert_PROP (Ptrofs.unsigned (Ptrofs.repr ofs) + sizeof t < Ptrofs.modulus /\
     align_compatible_rec cenv_cs t (Ptrofs.unsigned (Ptrofs.repr ofs)) /\
 ofs + init_data_size idata <= Ptrofs.max_unsigned). {
Search init_data type.
unfold init_data2pred.
destruct idata.
eapply derives_trans; [apply andp_right; [subst v; eapply mapsto_aligned; reflexivity | apply derives_refl ] |].
normalize.
simpl  in H.
Search mapsto.
Search init_data2pred.

  END ***)
 unfold init_data2pred', init_data2pred.
 rename H8 into H8'.
 assert (H8: offset_val ofs v = Vptr b (Ptrofs.repr ofs)).
 rewrite H8'; simpl. rewrite Ptrofs.add_zero_l; auto.
 clear H8'.
 simpl.
 destruct idata; super_unfold_lift; try apply derives_refl.
*  if_tac; try rewrite H8;
    try (rewrite data_at__memory_block by (auto; unfold Ptrofs.max_unsigned in H6; omega);
          rewrite <- H;
         rewrite prop_true_andp by auto);
    (unfold init_data_size in H6;
    assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable;
    pose proof (Z.le_max_l z 0);
     pose proof unsigned_repr_range ofs H6';
    apply mapsto_zeros_memory_block; [omega | omega | auto ]).
*  destruct ((var_types Delta) ! i) eqn:Hv;
   destruct ((glob_types Delta) ! i) eqn:Hg;
    try destruct g; try solve [simpl; apply TT_right].
 +   destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' H15]; rewrite H15.
     simpl.
     rewrite H8.
     eapply derives_trans.
     apply unpack_globvar_aux1.
     pose proof unsigned_repr_le ofs.
     rewrite sizeof_Tpointer; simpl in H6.
     rewrite Ptrofs.unsigned_repr by (destruct Archi.ptr64; omega).
     omega.
    destruct t1; try (apply prop_right; auto).
    destruct t1; try (apply prop_right; auto).
    auto.
    auto.
 +
   destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' H15]; rewrite H15.
   assert (Hv' :=proj1 (expr_lemmas2.typecheck_var_environ_None _ _ (proj1 (proj2 H7)) i) Hv).
   assert (locald_denote (gvar i (Vptr b' Ptrofs.zero)) rho)
     by (hnf; rewrite Hv'; rewrite H15; auto).
    destruct t0; simpl; try apply TT_right; try rewrite H8; try rewrite H;
   try  (apply exp_right with (Vptr b' Ptrofs.zero); apply andp_right;
      [unfold local, lift1; apply prop_right; auto
      |      unfold offset_val; simpl; try rewrite Ptrofs.repr_unsigned, Ptrofs.add_zero_l; auto; try apply derives_refl]).
  unfold globals_of_env. rewrite H15. 
  unfold mapsto. simpl. rewrite !if_true by auto.
  rewrite andb_false_r. simpl.
  apply orp_right1.
  apply orp_left. normalize. rewrite Ptrofs.repr_unsigned.
   apply derives_refl.
  normalize. inv H0.
Qed.

Lemma readable_share_readonly2share:
 forall b, readable_share (readonly2share b).
Proof.
destruct b; simpl.
intro.
rewrite glb_split_x in H.
destruct (Share.split Share.Rsh) eqn:?.
pose proof (split_nontrivial' _ _ _ Heqp).
simpl in H.
spec H0; auto.
apply juicy_mem.nonidentity_Rsh; auto.
unfold readable_share.
rewrite Share.glb_idem.
apply juicy_mem.nonidentity_Rsh.
Qed.

Lemma unpack_globvar  {cs: compspecs}:
  forall Delta gz i t gv idata,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0 = true)%bool ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   init_data_size idata <= sizeof t ->
   sizeof t <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) && globvar2pred gz (i, gv) |--
       init_data2pred' Delta gz idata (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) t (gz i).
Proof.
intros.
go_lowerx. subst gz.
eapply derives_trans; [eapply tc_globalvar_sound'; try eassumption | ].
assert (RS: forall sh', readable_share (Share.lub sh' (readonly2share (gvar_readonly gv)))).
intros.
apply readable_share_lub. apply readable_share_readonly2share.
forget (readonly2share (gvar_readonly gv)) as sh.
autorewrite with subst norm1 norm2; normalize.
unfold init_data_list2pred.
rewrite sepcon_emp.
destruct (globvar_eval_var _ _ _ _ H7 H H0) as [b [? ?]].
assert (globals_of_env rho i = offset_val 0 (globals_of_env rho i)).
unfold globals_of_env.
rewrite H9. reflexivity.
rewrite H10 at 1.
 apply derives_trans with
    (init_data2pred' Delta (globals_of_env rho) idata (Share.lub extern_retainer sh) t
      (offset_val 0 (globals_of_env rho i)) rho).
+ rewrite andb_true_iff in H1; destruct H1.
  eapply init_data2pred_rejigger; eauto.
  4: unfold globals_of_env; rewrite H9; reflexivity.
   - split; simpl; auto.
       change Ptrofs.max_unsigned with (Ptrofs.modulus-1) in H6.
      split3; auto. subst; auto. omega. split; auto. apply la_env_cs_sound in H11; auto.
      subst; auto.
   - omega.
   - omega.
 +
 unfold init_data2pred'.
  rewrite <- H10.
 destruct idata; unfold_lift;
   try (rewrite H8; simpl; rewrite Ptrofs.add_zero_l; auto);
 try apply derives_refl.
Qed.

Fixpoint id2pred_star   {cs: compspecs}
   (Delta: tycontext) (gz: globals) (sh: share) t (v: val) (dl: list init_data) : environ->mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta gz d sh t v
                   * id2pred_star Delta gz sh t (offset_val (init_data_size d) v) dl'
 | nil => emp
 end.

Arguments id2pred_star cs Delta gz sh t v dl rho  / .

Lemma init_data_size_pos : forall a, init_data_size a >= 0.
Proof.
 destruct a; simpl; try omega.
 pose proof (Zmax_spec z 0).
 destruct (zlt 0 z); omega.
destruct Archi.ptr64; omega.
Qed.

Lemma init_data_list_size_pos : forall a, init_data_list_size a >= 0.
Proof.
 induction a; simpl.
 omega.
 pose proof (init_data_size_pos a); omega.
Qed.

Lemma unpack_globvar_star  {cs: compspecs}:
  forall Delta gz i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)% bool = true ->
   gvar_volatile gv = false ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) && globvar2pred gz (i, gv) |-- 
       id2pred_star Delta gz (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) (gvar_info gv) (gz i) (gvar_init gv).
Proof.
assert (H5:=true).
intros until 4.
remember (gvar_info gv) as t eqn:H3; symmetry in H3.
remember (gvar_init gv) as idata eqn:H4; symmetry in H4.
intros.
go_lowerx. subst gz.
eapply derives_trans; [eapply tc_globalvar_sound'; eassumption | ].
normalize.
  autorewrite with subst norm1 norm2; normalize.

normalize.
  autorewrite with subst norm1 norm2; normalize.
assert (RS: forall sh', readable_share (Share.lub sh' (readonly2share (gvar_readonly gv)))).
 {intros. 
  apply readable_share_lub. apply readable_share_readonly2share.
}
forget (readonly2share (gvar_readonly gv)) as sh.
set (ofs:=0%Z).
assert (alignof t | Ptrofs.unsigned (Ptrofs.repr ofs)) by (subst ofs; simpl; apply Z.divide_0_r).
destruct (globvar_eval_var _ _ _ _ H7 H H0) as [b [_ H9']].
unfold globals_of_env. rewrite H9'.
remember (Vptr b Ptrofs.zero) as x.
assert (H10: x = offset_val ofs x) by (subst ofs x; reflexivity).
rewrite H10 at 1.
clear H10.
assert (H11: init_data_list_size idata + ofs <= sizeof t)  by (unfold ofs; omega).
assert (H12:  sizeof t <= Ptrofs.max_unsigned)  by omega.
assert (0 <= ofs) by (unfold ofs; omega).
fold (globals_of_env rho).
match goal with |- _ |-- ?F _ _ _ _ _ _ _ _  => change F with @id2pred_star end.
replace x with (offset_val ofs x) at 2. 2: subst x; normalize.
clearbody ofs.
revert ofs H8 H9 H9' H11 H12.
clear dependent gv. clear H H0 H6.
induction idata; simpl; auto; intros. 
match goal with |- _ |-- _ * ?F _ _ _ _ _ _ _ _  => change F with @id2pred_star end.
apply sepcon_derives.
*
  clear IHidata. 
  rewrite andb_true_iff in H1 by (pose proof (init_data_list_size_pos idata); omega).
  pose proof (init_data_size_pos a).
  pose proof (init_data_list_size_pos idata).
  assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable.
  destruct H1.
  eapply init_data2pred_rejigger; eauto; try tauto; [ hnf; simpl | ];
  clear x Heqx; clear RS H7 H9' b.
  split3; simpl; auto. 
  rewrite Ptrofs.unsigned_repr by omega.
  split3; auto.
  admit. admit. admit.
* specialize (IHidata (ofs + init_data_size a)).
rewrite offset_offset_val.
 pose proof (init_data_list_size_pos idata).
pose proof (init_data_size_pos a).
 apply IHidata; clear IHidata; try omega; auto.
 rewrite Ptrofs.unsigned_repr by omega.
 rewrite Ptrofs.unsigned_repr in H8 by omega.
 apply Z.divide_add_r; auto.
 admit. (* alignment issue *)
Fail idtac.
Admitted.

Lemma tc_globalvar_sound_space {cs: compspecs} :
  forall Delta i t gv rho,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   sizeof t <= Ptrofs.max_unsigned ->
   tc_environ Delta rho ->
   (!! ((align_compatible t) (eval_var i t rho))) && globvar2pred (globals_of_env rho) (i, gv) rho |-- 
   data_at_ (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) t (eval_var i t rho).
Proof.
assert (H4 := true).
intros until 1. intros ? Hno; intros.
normalize.
eapply derives_trans; [eapply tc_globalvar_sound; eassumption | ].
simpl.
rewrite data_at__memory_block; try tauto;
  try (unfold Int.max_unsigned in H5; omega).
destruct (tc_eval_gvar_zero _ _ _ _ H6 H H0) as [b ?].
rewrite H8 in H7 |- *.
rewrite sepcon_emp.
pose proof (mapsto_zeros_memory_block
  (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) (sizeof t) b Ptrofs.zero).
rewrite Ptrofs.unsigned_zero in H9.
apply andp_right.
+ normalize.
  apply prop_right. subst t.
  rewrite andb_true_iff in Hno.
  destruct Hno as [? ?]. split3; simpl; auto.
  split3; auto.
  change Ptrofs.max_unsigned with (Ptrofs.modulus-1) in H5.
  omega.
+ apply H9.
  pose (sizeof_pos t).
  - unfold Ptrofs.max_unsigned in H5. omega.
  - unfold Ptrofs.max_unsigned in H5. omega.
  - apply readable_share_lub; apply readable_share_readonly2share.
Qed.

Definition inttype2init_data (sz: intsize) : (int -> init_data) :=
 match sz with
 | IBool  =>  Init_int8
 | I8  =>  Init_int8
 | I16 =>  Init_int16
 | I32 =>  Init_int32
 end.

Definition notboolsize (sz: intsize) : Prop :=
  match sz with IBool => False | _ => True end.

Lemma id2pred_star_ZnthV_Tint  {cs: compspecs} :
 forall Delta gz sh n (v: val) (data: list int) sz sign mdata
  (NBS: notboolsize sz),
  n = Zlength mdata ->
  mdata = map (inttype2init_data sz) data ->
  !! isptr v && !! align_compatible (Tint sz sign noattr) v &&
  !! (offset_in_range (sizeof (Tint sz sign noattr) * n)) v &&
  id2pred_star Delta gz sh (tarray (Tint sz sign noattr) n) v mdata |--
  `(data_at sh (tarray (Tint sz sign noattr) n)
           (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data) v).
Proof.
  intros. subst n mdata.
  replace (Zlength (map  (inttype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  go_lowerx.
  match goal with |- ?F _ _ _ _ _ _ _ _ |-- _ => change F with @id2pred_star end.
  change (offset_in_range (sizeof (Tint sz sign noattr) * Zlength data) v) in H1.
  assert (offset_in_range (sizeof (Tint sz sign noattr) * 0) v) by
    (unfold offset_in_range; destruct v; auto; pose proof Ptrofs.unsigned_range i; omega).
unfold tarray.
set (t := Tint sz sign noattr) in *.
set (t1 := Tarray t (Zlength data) noattr)  at 1. clearbody t1.
(* replace v with (field_address0 (Tarray (Tint sz sign noattr) (Z.succ (Zlength data)) noattr) (SUB 1) v) at 1. *)
revert v H H0 H1 H2; induction data; intros.
*
  rewrite Zlength_nil. unfold data_at, field_at; simpl.
  unfold at_offset; simpl.
   unfold nested_field_type; simpl.
   rewrite data_at_rec_eq. unfold  aggregate_pred.aggregate_pred.array_pred.
  unfold aggregate_pred.array_pred. simpl.
  repeat apply andp_right; auto; try apply prop_right; try reflexivity.  
  hnf. simpl.
  split3; auto.
  split3; auto.
  hnf. destruct v; auto. replace (sizeof (Tarray (Tint sz sign noattr) 0 noattr)) with 0 by (destruct sz; simpl; auto).
  pose proof Ptrofs.unsigned_range i; omega.
  hnf; destruct v; auto. apply align_compatible_rec_Tarray. intros. omega.
*
rewrite Zlength_cons.
simpl map.
unfold id2pred_star; fold @id2pred_star.
erewrite (split2_data_at_Tarray sh t (Z.succ (Zlength data)) 1).
4: rewrite sublist_same.
4: apply JMeq_refl.
2: list_solve. 2: list_solve. 2: auto. 2: list_solve. 2: apply JMeq_refl. 2: apply JMeq_refl.
rewrite (sublist_one) by list_solve.
autorewrite with sublist.
rewrite sublist_1_cons.
rewrite Znth_0_cons.
rewrite sublist_same by list_solve.
apply sepcon_derives.
+
clear IHdata.
fold (tarray t 1). erewrite data_at_singleton_array_eq by apply JMeq_refl.
rewrite <- (mapsto_data_at sh t (Vint (Cop.cast_int_int sz sign a)) (Vint (Cop.cast_int_int sz sign a)) v); try reflexivity; auto.
2: subst t; destruct sz, sign; reflexivity.
Focus 2.
destruct v; auto. red.
assert (sizeof t > 0).
subst t; simpl. destruct sz; computable.
clearbody t.
clear - H1 H3.
rewrite Zlength_cons in H1. simpl in H1.
unfold Z.succ in H1. rewrite Z.mul_add_distr_l in H1.
pose proof (Zlength_nonneg data).
rewrite Z.mul_1_r in H1.
assert (0 <= sizeof t * Zlength data). {
 apply Z.mul_nonneg_nonneg; omega.
}
admit.  (* have <= where we need <  *)
subst t.
normalize.
unfold init_data2pred', inttype2init_data.
destruct sz; try contradiction NBS;
unfold_lift; unfold tuchar, tushort, tuint;  rewrite <- (mapsto_unsigned_signed Unsigned sign sh);
apply derives_refl.
+
  replace (init_data_size (inttype2init_data sz a)) with (sizeof t) 
      by (subst t; destruct sz; simpl; auto). 
  eapply derives_trans; [ apply IHdata | ]; clear IHdata; auto.
 -    admit. (* should be ok *)
 -    admit. (* should be ok *)
 -    admit. (* should be ok *)
 - replace (Z.succ (Zlength data) - 1) with (Zlength data) by (clear; omega).
   apply derives_refl'; f_equal.
   admit. (* probably all right *)
Admitted.

Lemma id2pred_star_ZnthV_tint  {cs: compspecs}:
 forall Delta gz sh n (v: val) (data: list int) mdata,
  n = Zlength mdata ->
  mdata = map Init_int32 data ->
  !! isptr v && !! align_compatible tint v &&
  !! offset_in_range (sizeof tint * n) v &&
  id2pred_star Delta gz sh (tarray tint n) v mdata |--
  `(data_at sh (tarray tint n) (map Vint data) v).
Proof. intros; apply id2pred_star_ZnthV_Tint; auto; apply Coq.Init.Logic.I.
Qed.

Lemma gvar_isptr:
  forall i s rho, locald_denote (gvar i s) rho -> isptr s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst; apply Coq.Init.Logic.I.
Qed.

Lemma offset_zero_globals_of_env: forall rho i,
   offset_val 0 (globals_of_env rho i) = globals_of_env rho i.
Proof.
intros.
unfold globals_of_env.
destruct (ge_of rho i); simpl; auto.
Qed.

Lemma unpack_globvar_array  {cs: compspecs}:
  forall t sz sign (data: list int)  n Delta gz i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   t = Tint sz sign noattr ->
  forall    (NBS: notboolsize sz),
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (inttype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) && globvar2pred gz(i, gv) |--
      `(data_at (Share.lub extern_retainer (readonly2share (gvar_readonly gv)))
         (tarray (Tint sz sign noattr) n)
         (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)
         (gz i)).
Proof.
  intros. subst t.
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (tc_environ Delta)))
  end.
 2: solve [apply andp_left1; unfold local, lift1; intro rho; apply prop_derives; intros [? ?]; auto].
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (`isptr (eval_var i (tarray (Tint sz sign noattr) n)))))
  end.
  Focus 2. {
    go_lowerx. apply prop_right. eapply eval_var_isptr; eauto.
    right; split; auto. rewrite <- H1; auto.
   } Unfocus.
  eapply derives_trans.
  apply andp_right.
  apply andp_left1. apply andp_left1. apply andp_left1. apply derives_refl.
   apply andp_derives; [ apply andp_derives; [ eapply unpack_globvar_star; try eassumption; try reflexivity | apply derives_refl]  | apply derives_refl].
* rewrite andb_true_iff.
  split; rewrite H1.
  reflexivity.
  unfold is_aligned, is_aligned_aux. rewrite andb_true_iff; split.
  destruct sz, sign; simpl; auto.
  rewrite Z.mod_0_l. reflexivity.
  destruct sz, sign; simpl; computable.
*
 (* rewrite H1.*)  (* rewrite H3.*) rewrite H5.
  rewrite <- andp_assoc.
  apply andp_left1.
Print Ltac go_lowerx'.
  go_lowerx. 
Transparent sizeof.
  eapply derives_trans; [| apply (id2pred_star_ZnthV_Tint Delta (globals_of_env rho)); auto].
  instantiate (1 := rho).
 2: rewrite <- H5; auto.
 match goal with |- ?F _ _ _ _ _ _ _ _ |-- _ => change F with @id2pred_star end.
  subst gz.
  normalize. clear H8.
  rewrite H1 in H6.
  assert (isptr (globals_of_env rho i)). {
    unfold globals_of_env. destruct  (globvar_eval_var _ _ _ _ H3 H H0) as [b [_ H10]]. rewrite H10. apply I.
  }
  assert (align_compatible (Tint sz sign noattr) (globals_of_env rho i)). {
    hnf. 
    admit.
  }
 simpl andp. fold (sizeof (Tint sz sign noattr)).
  assert (offset_in_range (sizeof (Tint sz sign noattr) * n) (globals_of_env rho i)). {
    unfold offset_in_range.
    destruct (globals_of_env rho i) eqn:?H; auto.
    rewrite H5 in H6; simpl in H6.
    pose proof initial_world.zlength_nonneg _ (gvar_init gv).
    rewrite Z.max_r in H6 by omega.
    unfold Ptrofs.max_unsigned in H6.
    pose proof init_data_list_size_pos (gvar_init gv).    
    admit.
  }
  normalize.
 match goal with |- _ |-- ?F _ _ _ _ _ _ _ _ => change F with @id2pred_star end.
  rewrite H1.
  apply derives_refl.
Fail idtac.
Admitted.

Lemma process_globvar':
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gz gv gvs SF c Post (idata : init_data) t,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_info gv = t ->
       gvar_init gv = (idata::nil) ->
       init_data_size idata <= sizeof t ->
       sizeof t <= Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz::Q) (SEPx R))
                       * id2pred_star Delta gz
                         (Share.lub  extern_retainer (readonly2share (gvar_readonly gv)))
                         t (gz i) (idata ::nil) * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz::Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre; [ | apply H7]; clear H7.
pose proof  (unpack_globvar Delta gz i t gv idata H H0 H1 H2 H3 H4 H5 H6).
clear H H0 H1 H2 H3 H4 H5 H6.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold globvars2pred.
change (lift_S (LiftEnviron Prop)) with environ in *.
unfold lift2.
change  (fun rho : environ => gz = globals_of_env rho)
  with (locald_denote (gvars gz)) in H7|-*.
go_lowerx.
normalize.
apply sepcon_derives; auto.
rewrite sepcon_assoc.
apply sepcon_derives; auto.
apply sepcon_derives; auto.
unfold local, lift1 in H7. specialize (H7 rho). simpl in H7. rewrite prop_true_andp in H7 by (split; auto).
apply H7.
Qed.

Lemma process_globvar_array:
  forall {cs: compspecs} {Espec: OracleKind} Delta gz P Q R (i: ident)
          gv gvs SF c Post (n: Z) (t: type)  (sz : intsize) (sign : signedness) (data : list int),
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some (gvar_info gv) ->
       gvar_info gv = tarray t n ->
       gvar_volatile gv = false ->
       t = Tint sz sign noattr ->
       notboolsize sz ->
       n = Zlength (gvar_init gv) ->
       gvar_init gv = map (inttype2init_data sz) data ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz :: Q)
                      (SEPx ((data_at
                   (Share.lub extern_retainer (readonly2share (gvar_readonly gv)))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo Cop.cast_int_int sz sign) data) (gz i))
                    :: R)))
                       * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz :: Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre; [ | apply H8]. clear H8.
pose proof (unpack_globvar_array _ _ _ _ _ _ gz _ _ H H0 H1 H2 H3 H4 H5 H6 H7).
clear H H0 H1 H2 H3 H4 H5 H6 H7.
rewrite <- !insert_local.
rewrite <- insert_SEP.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold globvars2pred.
change (lift_S (LiftEnviron Prop)) with environ in *.
unfold lift2.
change  (fun rho : environ => gz = globals_of_env rho)
  with (locald_denote (gvars gz)) in H8|-*.
go_lowerx.
normalize.
apply sepcon_derives; auto.
pull_right (PQR rho).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
unfold local, lift1 in H8. specialize (H8 rho). simpl in H8. rewrite prop_true_andp in H8 by (split; auto).
apply H8.
Qed.

Lemma process_globvar_star':
  forall {cs: compspecs} {Espec: OracleKind} Delta gz P Q R (i: ident)
          gv gvs SF c Post,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz :: Q)
                      (SEPx R))
                  * (id2pred_star Delta gz
                          (Share.lub extern_retainer
                               (readonly2share (gvar_readonly gv)))
                      (gvar_info gv) (gz i) (gvar_init gv))
             * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz :: Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre; [ | apply H4]. clear H4.
pose proof (unpack_globvar_star _ gz _ _ H H0 H1 H2 H3).
clear H H0 H1 H2 H3.
rewrite <- !insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold globvars2pred.
change (lift_S (LiftEnviron Prop)) with environ in *.
unfold lift2.
change  (fun rho : environ => gz = globals_of_env rho)
  with (locald_denote (gvars gz)) in H4|-*.
go_lowerx.
normalize.
apply sepcon_derives; auto.
pull_right (PQR rho).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
unfold local, lift1 in H4. specialize (H4 rho). simpl in H4. rewrite prop_true_andp in H4 by (split; auto).
apply H4.
Qed.

Lemma map_instantiate:
  forall {A B} (f: A -> B) (x: A) (y: list B) z,
    y = map f z ->  f x :: y = map f (x :: z).
Proof. intros. subst. reflexivity. Qed.

Ltac expand_one_globvar :=
 (* given a proof goal of the form   local (tc_environ Delta) && globvar2pred (_,_) |-- ?33 *)
first [
    eapply unpack_globvar;
      [reflexivity | reflexivity | split; [| split]; reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence ]
 | eapply unpack_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence ]
 | eapply derives_trans;
    [ apply unpack_globvar_star;
        [reflexivity | reflexivity | split; [| split]; reflexivity
        | reflexivity | compute; split; clear; congruence ]
    |  cbv beta; simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
      change (Share.lub extern_retainer Tsh) with Ews
    ]; apply derives_refl
 | apply andp_left2; apply derives_refl
 ].

Lemma main_pre_start:
 forall prog u gv,
   main_pre prog u gv = (PROP() LOCAL(gvars gv) SEP())%assert * globvars2pred gv (prog_vars prog).
Proof.
intros.
unfold main_pre.
unfold globvars2pred,  PROPx, LOCALx, SEPx.
unfold lift2.
extensionality rho.
simpl.
normalize.
unfold gvars_denote. unfold_lift. unfold local, lift1.
fold (globals_of_env rho).
apply pred_ext; intros; normalize.
rewrite prop_true_andp by auto.
auto.
Qed.

Ltac process_one_globvar :=
 first
  [ simple eapply process_globvar';
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence | ]
  | simple eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence |  ]
  | simple eapply process_globvar_star';
        [reflexivity | reflexivity | reflexivity
        | reflexivity | compute; split; clear; congruence
       | simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
         change (Share.lub extern_retainer Tsh) with Ews
         ]
  ];
  change (Share.lub extern_retainer _) with Ews;
  change (Share.lub extern_retainer _) with Ers;
  change (Vint oo _) with (Vint oo id);
  fold_types;
  rewrite ?Combinators.compose_id_right.

Lemma move_globfield_into_SEP:
 forall {cs: compspecs}{Espec: OracleKind} Delta P Q R
   (S1: mpred) (S2 S3 S4: environ -> mpred) c Post,
 semax Delta (PROPx P (LOCALx Q (SEPx (S1::R))) * S2 * S3 * S4) c Post ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) * (`S1 * S2) * S3 * S4) c Post.
Proof.
intros.
eapply semax_pre0; [ | eassumption].
rewrite <- insert_SEP.
rewrite <- !sepcon_assoc.
pull_left (`S1).
auto.
Qed.

Lemma move_globfield_into_SEP':
 forall {cs: compspecs}{Espec: OracleKind} Delta P Q R
   (f: val -> localdef)
   (g: val -> mpred)
   (h: val -> val) (S2 S3 S4: environ -> mpred) c Post,
  (forall x: val,
   semax Delta (PROPx P (LOCALx (f x :: Q) (SEPx ((g (h x))::R))) * S2 * S3 * S4) c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) * ((EX x:val, local (locald_denote (f x)) && `(g (h x))) * S2) * S3 * S4) c Post.
Proof.
intros.
normalize.
apply extract_exists_pre; intro x.
eapply semax_pre0; [ | apply (H x)].
clear.
rewrite <- insert_SEP.
rewrite <- insert_local.
rewrite local_sepcon_assoc1.
rewrite !local_sepcon_assoc2.
rewrite !local_sepcon_assoc1.
apply andp_derives; auto.
rewrite <- !sepcon_assoc.
pull_left (`(g (h x))).
apply derives_refl.
Qed.

Lemma move_globfield_into_SEP'':
 forall {cs: compspecs}{Espec: OracleKind} Delta P Q R
   (i: ident) (v: val)
   (g: val -> mpred)
   (h: val -> val) (S2 S3 S4: environ -> mpred) c Post,
   In (gvar i v) Q ->
  semax Delta (PROPx P (LOCALx Q (SEPx ((g (h v))::R))) * S2 * S3 * S4) c Post ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) * ((EX x:val, local (locald_denote (gvar i x)) && `(g (h x))) * S2) * S3 * S4) c Post.
Proof.
intros.
normalize.
apply extract_exists_pre; intro x.
eapply semax_pre0; [ | apply H0].
clear - H.
rewrite <- insert_SEP.
go_lowerx.
normalize.
cancel.
clear - H2 H H1.
revert H H1; induction Q; intros.
inv H. simpl in H. destruct H. subst a.
simpl in H1.
destruct H1.
clear - H2 H.
hnf in H,H2.
destruct (Map.get (ve_of rho) i) as [[? ?]|]. contradiction.
destruct (ge_of rho i); try contradiction.
subst. auto.
destruct H1.
auto.
Qed.

Lemma move_globfield_into_SEP0:
 forall {cs: compspecs}{Espec: OracleKind} Delta
   (S0 S3 S4: environ -> mpred) c Post,
 semax Delta (S0 * S3 * S4) c Post ->
 semax Delta (S0 * emp * S3 * S4) c Post.
Proof.
intros.
rewrite sepcon_emp; auto.
Qed.

Lemma offset_val_unsigned_repr: forall i p,
  offset_val (Ptrofs.unsigned (Ptrofs.repr i)) p = offset_val i p.
Proof.
  intros.
  unfold offset_val.
  unfold Ptrofs.add.
  rewrite Ptrofs.repr_unsigned.
  auto.
Qed.

Ltac process_idstar :=
  match goal with
  | |- semax _ (_ * globvars2pred _ (_::_) * _) _ _ =>
     process_one_globvar;
     match goal with |- semax _ (_ * ?A * _ * _) _ _ =>
         let p := fresh "p" in set (p:=A);
         simpl in p;
         unfold id2pred_star, init_data2pred' in p;
         simpl PTree.get in p; simpl zeq in p;
         cbv beta iota zeta in p;
         simpl init_data_size in p;
         revert p; rewrite ?offset_offset_val; intro p; simpl Z.add in p;
         subst p;
      repeat first
        [simple apply move_globfield_into_SEP
        | simple eapply move_globfield_into_SEP''; [ now repeat econstructor | ]
        | simple apply move_globfield_into_SEP'; intros ?gvar0;
          lazymatch goal with
          | |- semax _ ((PROPx _ (LOCALx (gvar ?A ?B :: _) _)) * _ * _ * _)  _ _ =>
                 let n := fresh "v" A in rename B into n
          | |- _ => idtac
          end
        ];
      simple apply move_globfield_into_SEP0
      | |- _ => idtac
    end
 end.

Lemma eliminate_globvars2pred_nil: 
 forall {cs: compspecs}{Espec: OracleKind} Delta PQR gv SF c Post,
  semax Delta (PQR * SF) c Post ->
  semax Delta (PQR * globvars2pred gv nil * SF) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H].
go_lowerx; normalize.
Qed.

Ltac expand_main_pre :=
 rewrite main_pre_start;
 unfold prog_vars, prog_vars'; simpl globvars2pred;
 repeat  process_idstar;
 apply eliminate_globvars2pred_nil;
 rewrite ?offset_val_unsigned_repr.

