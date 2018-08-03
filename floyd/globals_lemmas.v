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
intros.
unfold globvar2pred.
simpl.
destruct_var_types i.
destruct_glob_types i.
unfold globals_of_env.
unfold eval_var.
rewrite Heqo0, Heqo1, H1, H2.
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
intros.
unfold globvar2pred.
simpl.
destruct_glob_types i.
unfold globals_of_env.
rewrite Heqo0, H1, H2.
auto.
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
(*
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
simpl.
apply pred_ext.
unfold sgvar_denote.
destruct (Map.get (ge_of rho) id).
apply exp_right with (Vptr b Ptrofs.zero).
normalize.
eapply derives_trans; [ apply H | ].
apply FF_left.
unfold sgvar_denote.
apply exp_left; intro; normalize.
destruct (Map.get (ge_of rho) id).
subst. auto.
contradiction.
Qed.
*)
Definition init_data2pred' {cs: compspecs}
     (Delta: tycontext) (gv: globals) (d: init_data)  (sh: share) (v: val) : mpred :=
 match d with
  | Init_int8 i => mapsto sh tuchar v (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh tushort v (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh tuint v (Vint i)
  | Init_int64 i => mapsto sh tulong v (Vlong i)
  | Init_float32 r =>  mapsto sh tfloat v (Vsingle r)
  | Init_float64 r =>  mapsto sh tdouble v (Vfloat r)
  | Init_space n =>  memory_block sh n v
  | Init_addrof symb ofs =>
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Tarray t n' att) =>
           mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) (gv symb))
      | None, Some t => mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) (gv symb))
      | Some _, Some _ => mapsto_ sh (Tpointer Tvoid noattr) v
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

Lemma init_data2pred_rejigger {cs: compspecs}:
  forall (Delta : tycontext)  (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs v,
  tc_environ Delta rho ->
  v = Vptr b (Ptrofs.repr 0) ->
  readable_share sh ->
   init_data2pred idata sh (offset_val ofs v) rho
    |-- init_data2pred' Delta (globals_of_env rho) idata sh (offset_val ofs v).
Proof.
intros until v.
intros H7 H8 RS.
assert (H6:=I).
 unfold init_data2pred', init_data2pred.
 rename H8 into H8'.
 assert (H8: offset_val ofs v = Vptr b (Ptrofs.repr ofs)).
 rewrite H8'; simpl. rewrite Ptrofs.add_zero_l; auto.
 clear H8'.
 simpl.
 destruct idata; super_unfold_lift; try apply derives_refl.
*  unfold init_data_size in H6.
    assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable.
    pose proof (Z.le_max_l z 0).
    rewrite H8.
    apply mapsto_zeros_memory_block; auto.
* destruct_var_types i eqn:Hv&Hv'; rewrite ?Hv, ?Hv';
  destruct_glob_types i eqn:Hg&Hg'; rewrite ?Hg, ?Hg';
try solve [simpl; apply TT_right].
 + rewrite H8. cancel.
 + replace (offset_val (Ptrofs.unsigned i0) (globals_of_env rho i)) with (Vptr b0 i0).
   replace (mapsto sh (Tpointer Tvoid noattr) (offset_val ofs v) (Vptr b0 i0))
   with (mapsto sh (Tpointer t noattr) (offset_val ofs v) (Vptr b0 i0)).
   destruct t; auto.
   unfold mapsto; simpl.
   destruct (offset_val ofs v); auto. rewrite !if_true by auto. rewrite andb_false_r.
   apply derives_refl.
   unfold mapsto; simpl.
   destruct (offset_val ofs v); auto. rewrite !if_true by auto. rewrite andb_false_r.
   reflexivity.
   unfold globals_of_env. rewrite Hg'. simpl. rewrite Ptrofs.add_zero_l.
   f_equal. rewrite Ptrofs.repr_unsigned; auto.
Qed.

Lemma readable_readonly2share: forall ro, readable_share (readonly2share ro).
Proof.
intros. apply initialize.readable_readonly2share.
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
       `(init_data2pred' Delta gz idata (readonly2share (gvar_readonly gv)) (gz i)).
Proof.
intros.
go_lowerx. subst gz.
eapply derives_trans; [eapply tc_globalvar_sound'; try eassumption | ].
assert (RS:= readable_readonly2share (gvar_readonly gv)).
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
     (init_data2pred' Delta (globals_of_env rho) idata sh
      (offset_val 0 (globals_of_env rho i))).
+ rewrite andb_true_iff in H1; destruct H1.
  eapply init_data2pred_rejigger; eauto; try omega.
  unfold globals_of_env; rewrite H9; reflexivity.
 +
 unfold init_data2pred'.
  rewrite <- H10.
 destruct idata; unfold_lift;
   try (rewrite H8; simpl; rewrite Ptrofs.add_zero_l; auto);
 try apply derives_refl.
Qed.

Fixpoint id2pred_star   {cs: compspecs}
   (Delta: tycontext) (gz: globals) (sh: share) (v: val) (dl: list init_data) : environ->mpred :=
 match dl with
 | d::dl' => `(init_data2pred' Delta gz d sh v)
                   * id2pred_star Delta gz sh (offset_val (init_data_size d) v) dl'
 | nil => emp
 end.

Arguments id2pred_star cs Delta gz sh v dl rho  / .

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

Definition globvar_all_aligned {cs: compspecs} gv : bool :=
  forallb (fun a =>andb
                (init_data_size a mod hardware_alignof ha_env_cs (gvar_info gv) =? 0)
                (init_data_size a mod alignof (gvar_info gv) =? 0))
           (gvar_init gv).

Lemma unpack_globvar_star  {cs: compspecs}:
  forall Delta gz i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)% bool = true ->
   gvar_volatile gv = false ->
  (globvar_all_aligned gv = true) ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) && globvar2pred gz (i, gv) |-- 
       id2pred_star Delta gz (readonly2share (gvar_readonly gv)) (gz i) (gvar_init gv).
Proof.
intros until 4.
intros H5.
unfold globvar_all_aligned in H5.
remember (gvar_info gv) as t eqn:H3; symmetry in H3.
remember (gvar_init gv) as idata eqn:H4; symmetry in H4.
intros.
go_lowerx. subst gz.
eapply derives_trans; [eapply tc_globalvar_sound'; eassumption | ].
normalize.
  autorewrite with subst norm1 norm2; normalize.
match goal with |- _ |-- ?F _ _ _ _ _ _ _  => change F with @id2pred_star end.
normalize.
  autorewrite with subst norm1 norm2; normalize.
assert (RS:= readable_readonly2share (gvar_readonly gv)).
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
match goal with |- _ |-- ?F _ _ _ _ _ _ _  => change F with @id2pred_star end.
replace x with (offset_val ofs x) at 2. 2: subst x; normalize.
change 0 with ofs in H1.
clearbody ofs.
revert ofs H1 H5 H8 H9 H9' H11 H12.
clear dependent gv. clear H H0 H6.
induction idata; simpl; auto; intros. 
match goal with |- _ |-- _ * ?F _ _ _ _ _ _ _  => change F with @id2pred_star end.
apply sepcon_derives.
*
  clear IHidata. 
  rewrite andb_true_iff in H1 by (pose proof (init_data_list_size_pos idata); omega).
  pose proof (init_data_size_pos a).
  pose proof (init_data_list_size_pos idata).
  assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable.
  destruct H1.
  rewrite Ptrofs.unsigned_repr in H8 by omega.
  eapply init_data2pred_rejigger; eauto; try tauto;
  clear x Heqx; clear RS H7 H9' b.
* specialize (IHidata (ofs + init_data_size a)).
rewrite offset_offset_val.
 pose proof (init_data_list_size_pos idata).
pose proof (init_data_size_pos a).
 rewrite Ptrofs.unsigned_repr in H8 by omega.
 rewrite !andb_true_iff in H5.
 destruct H5 as [[H5a H5b] H5].
 assert (hardware_alignof ha_env_cs t | init_data_size a). {
   clear - H5a.
   assert (hardware_alignof ha_env_cs t > 0). {
     eapply hardware_alignof_pos; eauto.
     apply cenv_consistent.
     apply ha_env_cs_consistent.
     apply ha_env_cs_complete.
   }
   rewrite Z.eqb_eq in H5a.
   rewrite Z.mod_divide in H5a by omega. auto.
 }   
 assert (alignof t | init_data_size a). {
   clear - H5b.
   pose proof (alignof_pos t).
   rewrite Z.eqb_eq in H5b.
   rewrite Z.mod_divide in H5b by omega. auto.
 }   
 assert (Halign: is_aligned cenv_cs ha_env_cs la_env_cs t (ofs + init_data_size a) = true). {
    clear - H1 H2.
    rewrite andb_true_iff in H1; destruct H1; auto.
    unfold is_aligned, is_aligned_aux in *.
    rewrite andb_true_iff in H0|-*; destruct H0; split; auto.
    rewrite Z.eqb_eq in H1|-*.
   destruct (zeq (hardware_alignof ha_env_cs t) 0).
   rewrite e. apply Zmod_0_r.
   rewrite Z.mod_divide in H1|-* by auto.
   apply Z.divide_add_r; auto.
 }
 apply IHidata; clear IHidata; try omega; auto.
 rewrite andb_true_iff in H1|-*; destruct H1; split; auto.
 rewrite Ptrofs.unsigned_repr by omega.
 apply Z.divide_add_r; auto.
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
  !! (offset_strict_in_range (sizeof (Tint sz sign noattr) * n)) v &&
  id2pred_star Delta gz sh v mdata |--
  `(data_at sh (tarray (Tint sz sign noattr) n)
           (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data) v).
Proof.
  intros. subst n mdata.
  replace (Zlength (map  (inttype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  go_lowerx.
  match goal with |- ?F _ _ _ _ _ _ _ |-- _ => change F with @id2pred_star end.
  change (offset_strict_in_range (sizeof (Tint sz sign noattr) * Zlength data) v) in H1.
  assert (offset_strict_in_range (sizeof (Tint sz sign noattr) * 0) v) by
    (unfold offset_strict_in_range; destruct v; auto; pose proof Ptrofs.unsigned_range i; omega).
unfold tarray.
set (t := Tint sz sign noattr) in *.
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
4: apply eq_refl.
2: list_solve. 2: list_solve. 2: auto. 2: list_solve. 2: apply eq_refl. 2: apply eq_refl.
rewrite (sublist_one) by list_solve.
autorewrite with sublist.
rewrite sublist_1_cons.
rewrite Znth_0_cons.
rewrite sublist_same by list_solve.
apply sepcon_derives.
+
clear IHdata.
fold (tarray t 1). erewrite data_at_singleton_array_eq by apply eq_refl.
rewrite <- (mapsto_data_at sh t (Vint (Cop.cast_int_int sz sign a)) (Vint (Cop.cast_int_int sz sign a)) v); try reflexivity; auto.
2: subst t; destruct sz, sign; reflexivity.
2:{
destruct v; auto. red.
assert (sizeof t > 0).
subst t; simpl. destruct sz; computable.
clearbody t.
clear - H1 H3.
rewrite Zlength_cons in H1. simpl in H1.
unfold Z.succ in H1. rewrite Z.mul_add_distr_l in H1.
pose proof (Zlength_nonneg data).
rewrite Z.mul_1_r in H1.
assert (0 <= sizeof t * Zlength data)
  by (apply Z.mul_nonneg_nonneg; omega).
 omega.
}
subst t.
normalize.
unfold init_data2pred', inttype2init_data.
destruct sz; try contradiction NBS;
unfold_lift; unfold tuchar, tushort, tuint;  rewrite <- (mapsto_unsigned_signed Unsigned sign sh);
apply derives_refl.
+
  replace (init_data_size (inttype2init_data sz a)) with (sizeof t) 
      by (subst t; destruct sz; simpl; auto).
  assert (H8: align_compatible t (offset_val (sizeof t) v)
                /\  offset_strict_in_range (sizeof t * Zlength data) (offset_val (sizeof t) v)
               /\ offset_strict_in_range (sizeof t * 0) (offset_val (sizeof t) v)).  {
   clear IHdata.
   rewrite Zlength_cons in H1. unfold Z.succ in H1.
   rewrite Z.mul_add_distr_l in H1. rewrite Z.mul_1_r in H1.
   rewrite Z.mul_0_r in H2.
   pose proof (sizeof_pos t). pose proof (Zlength_nonneg data).
   destruct v; try contradiction.
   pose proof (Ptrofs.unsigned_range i).
   assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable.
   rewrite Z.mul_0_r in *.
   assert (0 <= sizeof t * Zlength data) by (apply Z.mul_nonneg_nonneg; omega).
   unfold offset_strict_in_range, offset_val in *.
   unfold align_compatible in H0|-*.
   unfold Ptrofs.add.
   rewrite (Ptrofs.unsigned_repr (sizeof t)) 
    by (unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize;
          clear; subst t; destruct sz,sign, Archi.ptr64; simpl; omega).
  rewrite Ptrofs.unsigned_repr.
  split3; try omega.
   assert (exists ch, access_mode t = By_value ch)
     by (clear; subst t; destruct sz,sign; eexists; reflexivity).
  destruct H8 as [ch ?].
  apply align_compatible_rec_by_value_inv with (ch:=ch) in H0; auto.
  apply align_compatible_rec_by_value with (ch:=ch); auto.
   apply Z.divide_add_r; auto.
  clear - H8. subst t. destruct sz,sign; inv H8; simpl; apply Z.divide_refl.
  unfold Ptrofs.max_unsigned.
  omega.
 }
 destruct H8 as [H8a [H8b H8c]].
  eapply derives_trans; [ apply IHdata | ]; clear IHdata; auto.
  replace (Z.succ (Zlength data) - 1) with (Zlength data) by (clear; omega).
   apply derives_refl'; f_equal.
 unfold field_address0.
  rewrite if_true.
  unfold offset_val. destruct v; simpl; auto. f_equal.
  subst t; destruct sz,sign; reflexivity.
  eapply field_compatible0_cons_Tarray.
  reflexivity.
  hnf; simpl. split3; auto. 
  destruct v; try contradiction.
  split3; auto; red.
  unfold sizeof; fold sizeof.
  pose proof (Zlength_nonneg data).
  rewrite Z.max_r by omega.
  unfold offset_strict_in_range in H1. rewrite Zlength_cons in H1.
  omega.
  apply align_compatible_rec_Tarray; intros.
  unfold align_compatible, offset_val in H8a.
  assert (exists ch, access_mode t = By_value ch)
     by (clear; subst t; destruct sz,sign; eexists; reflexivity).
   destruct H4 as [ch ?].
  eapply align_compatible_rec_by_value; try eassumption.
  simpl in H0.
  eapply align_compatible_rec_by_value_inv in H0; try eassumption.
  apply Z.divide_add_r; auto.
  apply Z.divide_mul_l; auto.
  clear - t H4.
  subst t.
  destruct sz,sign; inv H4; try apply Z.divide_refl.
  pose proof (Zlength_nonneg data); omega.
Qed.

Lemma id2pred_star_ZnthV_tint  {cs: compspecs}:
 forall Delta gz sh n (v: val) (data: list int) mdata,
  n = Zlength mdata ->
  mdata = map Init_int32 data ->
  !! isptr v && !! align_compatible tint v &&
  !! offset_strict_in_range (sizeof tint * n) v &&
  id2pred_star Delta gz sh v mdata |--
  `(data_at sh (tarray tint n) (map Vint data) v).
Proof. intros; apply id2pred_star_ZnthV_Tint; auto; apply Coq.Init.Logic.I.
Qed.

Lemma offset_zero_globals_of_env: forall rho i,
   offset_val 0 (globals_of_env rho i) = globals_of_env rho i.
Proof.
intros.
unfold globals_of_env.
destruct (Map.get (ge_of rho) i); simpl; auto.
Qed.

Lemma unpack_globvar_array  {cs: compspecs}:
  forall t sz sign (data: list int)  n Delta gz i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   globvar_all_aligned gv = true ->
   t = Tint sz sign noattr ->
  forall    (NBS: notboolsize sz),
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (inttype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) && globvar2pred gz(i, gv) |--
      `(data_at (readonly2share (gvar_readonly gv))
         (tarray (Tint sz sign noattr) n)
         (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)
         (gz i)).
Proof.
  intros until 4. intros Hgal; intros. subst t.
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (tc_environ Delta)))
  end.
 2: solve [apply andp_left1; unfold local, lift1; intro rho; apply prop_derives; intros [? ?]; auto].
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (`isptr (eval_var i (tarray (Tint sz sign noattr) n)))))
  end.
  2:{
    go_lowerx. apply prop_right. eapply eval_var_isptr; eauto.
    right; split; auto. rewrite <- H1; auto.
   }
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
  go_lowerx. 
  eapply derives_trans; [| apply (id2pred_star_ZnthV_Tint Delta (globals_of_env rho)); auto].
  instantiate (1 := rho).
 2: rewrite <- H5; auto.
 match goal with |- ?F _ _ _ _ _ _ _ |-- _ => change F with @id2pred_star end.
  subst gz.
  normalize. clear H8.
  rewrite H1 in H6.
  assert (headptr (globals_of_env rho i)). {
    unfold globals_of_env. destruct  (globvar_eval_var _ _ _ _ H3 H H0) as [b [_ H10]]. rewrite H10.
    exists b; auto. 
  }
  assert (align_compatible (Tint sz sign noattr) (globals_of_env rho i)). {
    destruct H7 as [b ?]. rewrite H7.
   assert (exists ch, access_mode (Tint sz sign noattr) = By_value ch)
     by (clear; destruct sz,sign; eexists; reflexivity).
   destruct H8 as [ch ?].
    eapply align_compatible_rec_by_value; try eassumption.
    rewrite Ptrofs.unsigned_zero.
    apply Z.divide_0_r.
  }
 apply headptr_isptr in H7.
 simpl andp. fold (sizeof (Tint sz sign noattr)).
  assert (offset_strict_in_range (sizeof (Tint sz sign noattr) * n) (globals_of_env rho i)). {
    unfold offset_strict_in_range.
    destruct (globals_of_env rho i) eqn:?H; auto.
    rewrite H5 in H6; simpl in H6.
    pose proof initial_world.zlength_nonneg _ (gvar_init gv).
    rewrite Z.max_r in H6 by omega.
    fold (sizeof (Tint sz sign noattr)) in H6.
    unfold Ptrofs.max_unsigned in H6.
    pose proof init_data_list_size_pos (gvar_init gv).
    simpl in H8.
    unfold globals_of_env in H9. destruct (Map.get (ge_of rho) i) eqn:?H; inv H9.
    rewrite Ptrofs.unsigned_zero.
    split; try omega. 
    rewrite Z.add_0_l.
    apply Z.mul_nonneg_nonneg.
    clear; pose proof (sizeof_pos (Tint sz sign noattr)); omega.
    apply Zlength_nonneg.
  }
  normalize.
 match goal with |- _ |-- ?F _ _ _ _ _ _ _ => change F with @id2pred_star end.
  apply derives_refl.
Qed.

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
                         (readonly2share (gvar_readonly gv))
                         (gz i) (idata ::nil) * globvars2pred gz gvs * SF)
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
       globvar_all_aligned gv = true ->
       t = Tint sz sign noattr ->
       notboolsize sz ->
       n = Zlength (gvar_init gv) ->
       gvar_init gv = map (inttype2init_data sz) data ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz :: Q)
                      (SEPx ((data_at
                   (readonly2share (gvar_readonly gv))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo Cop.cast_int_int sz sign) data) (gz i))
                    :: R)))
                       * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz :: Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros until 4. intro Hgal; intros.
eapply semax_pre; [ | apply H8]. clear H8.
pose proof (unpack_globvar_array _ _ _ _ _ _ gz _ _ H H0 H1 H2 Hgal H3 H4 H5 H6 H7).
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
       globvar_all_aligned gv = true ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz :: Q)
                      (SEPx R))
                  * (id2pred_star Delta gz (readonly2share (gvar_readonly gv))
                      (gz i) (gvar_init gv))
             * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz :: Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre; [ | apply H5]. clear H5.
pose proof (unpack_globvar_star _ gz _ _ H H0 H1 H2 H3 H4).
clear H H0 H1 H2 H3 H4.
rewrite <- !insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
unfold globvars2pred.
change (lift_S (LiftEnviron Prop)) with environ in *.
unfold lift2.
change  (fun rho : environ => gz = globals_of_env rho)
  with (locald_denote (gvars gz)) in H5|-*.
go_lowerx.
normalize.
apply sepcon_derives; auto.
pull_right (PQR rho).
apply sepcon_derives; auto.
apply sepcon_derives; auto.
unfold local, lift1 in H5. specialize (H5 rho). simpl in H5.
rewrite prop_true_andp in H5 by (split; auto).
apply H5.
Qed.

Fixpoint init_datalist2pred' {cs: compspecs}
     (Delta: tycontext) (gv: globals) (dl: list init_data)  (sh: share) (ofs: Z) (v: val) : mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta gv d sh (offset_val ofs v) 
                * init_datalist2pred' Delta gv dl' sh (ofs + init_data_size d) v
 | nil => emp
 end.

Lemma halfprocess_globvar_star:
  forall {cs: compspecs} {Espec: OracleKind} Delta gz P Q R (i: ident)
          gv gvs SF c Post,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz :: Q)
                      (SEPx (init_datalist2pred' Delta gz (gvar_init gv) (readonly2share (gvar_readonly gv)) 0 (gz i)
                                 ::R)))
             * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz :: Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre; [ | apply H4]. clear H4.
unfold globvars2pred; fold globvars2pred.
go_lowerx.
unfold lift2. simpl.
normalize.
rewrite prop_true_andp by (split; auto).
cancel.
unfold globvar2pred.
simpl.
rewrite H2.
pose proof (readable_readonly2share (gvar_readonly gv)).
forget (readonly2share (gvar_readonly gv)) as sh.
rewrite <- offset_zero_globals_of_env at 1.
set (ofs:=0).
clearbody ofs.
revert ofs; induction (gvar_init gv); intros.
apply derives_refl.
apply sepcon_derives.
destruct (globvar_eval_var _ _ _ _ H4 H H0) as [b [? ?]].
eapply init_data2pred_rejigger; eauto.
unfold globals_of_env.
rewrite H10. reflexivity.
fold init_data_list2pred.
fold init_datalist2pred'.
spec IHl.
simpl in H3.
pose proof (init_data_size_pos a).
omega.
eapply derives_trans; [ | apply IHl].
rewrite offset_offset_val.
auto.
Qed.

Lemma map_instantiate:
  forall {A B} (f: A -> B) (x: A) (y: list B) z,
    y = map f z ->  f x :: y = map f (x :: z).
Proof. intros. subst. reflexivity. Qed.

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

Lemma main_pre_ext_start:
 forall {Espec : OracleKind} prog u gv ora,
   main_pre_ext prog ora u gv = (PROP() LOCAL(gvars gv) SEP(has_ext ora))%assert * globvars2pred gv (prog_vars prog).
Proof.
intros.
unfold main_pre_ext.
unfold globvars2pred,  PROPx, LOCALx, SEPx.
unfold lift2.
extensionality rho.
simpl.
normalize.
unfold gvars_denote. unfold_lift. unfold local, lift1.
fold (globals_of_env rho).
rewrite sepcon_comm.
apply pred_ext; intros; normalize.
rewrite prop_true_andp by auto.
auto.
Qed.

Lemma process_globvar_space:
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gz gv gvs SF c Post t,
       gvar_info gv = t ->
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_init gv = (Init_space (sizeof t)::nil) ->
       sizeof t <= Ptrofs.max_unsigned ->
  semax Delta (PROPx P (LOCALx (gvars gz::Q) (SEPx (data_at_  (readonly2share (gvar_readonly gv)) t (gz i) :: R)))
                       * globvars2pred gz gvs * SF)
     c Post ->
 semax Delta (PROPx P (LOCALx (gvars gz::Q) (SEPx R))
                      * globvars2pred gz ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros until t. intros H3; intros.
eapply semax_pre; [ | apply H6]; clear H6.
rewrite <- insert_SEP.
rewrite <- insert_local.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
assert (H7 := unpack_globvar Delta gz i t gv _ H H0 H1 H2 H3 H4).
spec H7.
simpl. pose proof (sizeof_pos t). rewrite Z.max_l by omega. omega.
specialize (H7 H5).
go_lowerx.
unfold globvars2pred; fold globvars2pred.
simpl map.
unfold fold_right; fold (fold_right sepcon emp  (map (globvar2pred gz) gvs)).
unfold lift2.
normalize.
apply sepcon_derives; auto.
pull_left (PQR rho).
rewrite sepcon_assoc. 
apply sepcon_derives; auto.
apply sepcon_derives; auto.
specialize (H7 rho).
unfold_lift in H7. unfold local, lift1 in H7.
simpl in H7.
rewrite prop_true_andp in H7 by auto.
eapply derives_trans; [ apply H7  | ].
unfold_lift.
assert_PROP (isptr (globals_of_env rho i)) by (saturate_local; apply prop_right; auto).
assert (headptr (globals_of_env rho i)).
hnf. unfold globals_of_env in H9|-*. destruct (Map.get (ge_of rho) i); try contradiction. eauto.
rewrite memory_block_data_at_; auto.
subst t.
rewrite andb_true_iff in H1; destruct H1.
pose proof (la_env_cs_sound 0 (gvar_info gv) H1 H3).
apply headptr_field_compatible; auto.
apply I.
assert (Ptrofs.modulus = Ptrofs.max_unsigned + 1) by computable.
omega.
Qed.

Ltac process_one_globvar :=
 first
  [ simple eapply process_globvar_space;
    [simpl; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | simpl; computable | ]
  | simple eapply process_globvar';
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence | ]
  | simple eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence |  ]
  | simple eapply process_globvar_star';
        [reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | compute; split; clear; congruence
       | simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
         change (Share.lub extern_retainer Tsh) with Ews
         ]
  | simple eapply halfprocess_globvar_star;
        [reflexivity | reflexivity | reflexivity | reflexivity|
         simpl; compute; split; clear; congruence | ]
  ];
  change (Share.lub extern_retainer _) with Ews;
  change (Share.lub extern_retainer _) with Ers;
  try change (Vint oo _) with (Vint oo id);
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
(*
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
destruct (Map.get (ge_of rho) i); try contradiction.
subst. auto.
destruct H1.
auto.
Qed.
*)
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
     process_one_globvar;
     lazymatch goal with |- semax _ (_ * ?A * _ * _) _ _ =>
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
(*        | simple eapply move_globfield_into_SEP''; [ now repeat econstructor | ] *)
        | simple apply move_globfield_into_SEP'; intros ?gvar0 (*;
          lazymatch goal with
          | |- semax _ ((PROPx _ (LOCALx (gvar ?A ?B :: _) _)) * _ * _ * _)  _ _ =>
                 let n := fresh "v" A in rename B into n
          | |- _ => idtac
          end*)
        ];
      simple apply move_globfield_into_SEP0
    | |- semax _ (_ * _ * _) _ _ => idtac
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
 (rewrite main_pre_start || rewrite main_pre_ext_start);
 unfold prog_vars, prog_vars'; simpl globvars2pred;
 repeat  process_idstar;
 apply eliminate_globvars2pred_nil;
 rewrite ?offset_val_unsigned_repr;
 simpl readonly2share.

