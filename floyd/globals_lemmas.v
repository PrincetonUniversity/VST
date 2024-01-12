Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.data_at_list_solver.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Import LiftNotation.
Import -(notations) compcert.lib.Maps.

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
  (compute in x; subst x; spec H0; [lia| ]; spec H1; lia).
Qed.

Section mpred.

Context `{!heapGS Σ}.

Lemma tc_globalvar_sound:
  forall Delta i t gz idata rho,
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some t ->
   gvar_volatile gz = false ->
   gvar_init gz = idata ->
   tc_environ Delta rho ->
   globvar2pred (globals_of_env rho) (i, gz) ⊢ init_data_list2pred (globals_of_env rho) idata (readonly2share (gvar_readonly gz)) (eval_var i t rho).
Proof.
intros.
unfold globvar2pred.
simpl.
red in H3.
destruct_var_types i.
destruct_glob_types i.
unfold globals_of_env.
unfold eval_var.
rewrite Heqo0 Heqo1 H1 H2 //.
Qed.

Lemma tc_globalvar_sound':
  forall Delta i t gv idata rho,
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some t ->
   gvar_volatile gv = false ->
   gvar_init gv = idata ->
   tc_environ Delta rho ->
   globvar2pred (globals_of_env rho) (i, gv) ⊢
   init_data_list2pred (globals_of_env rho) idata (readonly2share (gvar_readonly gv)) (globals_of_env rho i).
Proof.
intros.
unfold globvar2pred.
simpl.
red in H3.
destruct_glob_types i.
unfold globals_of_env.
rewrite Heqo0 H1 H2 //.
Qed.

Lemma init_data_tarray_tint {cs:compspecs} gv b: forall xs i (Hi: Z.divide 4 (Ptrofs.unsigned i)) (Hxs: Ptrofs.unsigned i + 4 * Zlength xs < Ptrofs.modulus),
  init_data_list2pred gv (map Init_int32 xs) Ews (Vptr b i) ⊢
  data_at Ews (tarray tint (Zlength xs)) (map Vint xs) (Vptr b i).
Proof. induction xs; intros; simpl.
  - rewrite data_at_zero_array_eq; auto; reflexivity.
  - replace (4 * Zlength (a :: xs))%Z with (4  + (4 * Zlength xs)) in Hxs by list_solve.
    rewrite mapsto_tuint_tint.
    specialize (Zlength_nonneg xs); intros L.
    unfold Ptrofs.add. rewrite ! Ptrofs.unsigned_repr; try rep_lia.

    rewrite (split2_data_at_Tarray Ews tint (Zlength (a :: xs)) 1
            (Vint a :: map Vint xs) (Vint a :: map Vint xs)
            (sublist 0 1 (Vint a :: map Vint xs))
            (sublist 1 (Zlength (a :: xs)) (Vint a :: map Vint xs)) (Vptr b i)); try list_solve.
    rewrite -> (data_at_singleton_array_eq Ews tint (Vint a)) by trivial.
    erewrite mapsto_data_at'; auto; trivial.
    rewrite IHxs.
    rewrite Zlength_cons.
    replace (Z.succ (Zlength xs) - 1) with (Zlength xs) by lia.
    cancel. f_equiv. { list_solve. }
    unfold field_address0. rewrite if_true; simpl; trivial.
    repeat (split; first done).
    split3.
    * red. rewrite sizeof_Tarray Z.max_r. simpl sizeof; rep_lia. list_solve.
    * eapply align_compatible_rec_Tarray; intros.
      econstructor. reflexivity.
      apply Z.divide_add_r; [ trivial | exists i0; rewrite Z.mul_comm; reflexivity].
    * split. reflexivity. simpl; lia.
    * rewrite ! Ptrofs.unsigned_repr; try rep_lia.
      apply Z.divide_add_r; [ trivial | apply Z.divide_refl].
    * rewrite ! Ptrofs.unsigned_repr; rep_lia.
    * red; simpl; intuition auto.
      -- lia.
      -- econstructor; auto.
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

Definition init_data2pred'
     (Delta: tycontext) (gv: globals) (d: init_data)  (sh: share) (v: val) : mpred :=
 match d with
  | Init_int8 i => mapsto sh tuchar v (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh tushort v (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh tuint v (Vint i)
  | Init_int64 i => mapsto sh tulong v (Vlong i)
  | Init_float32 r =>  mapsto sh tfloat v (Vsingle r)
  | Init_float64 r =>  mapsto sh tdouble v (Vfloat r)
  | Init_space n =>  mapsto_zeros n sh v
  | Init_addrof symb ofs =>
      match (var_types Delta) !! symb, (glob_types Delta) !! symb with
      | None, Some (Tarray t n' att) =>
           mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) (gv symb))
      | None, Some t => mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) (gv symb))
      | Some _, Some _ => mapsto_ sh (Tpointer Tvoid noattr) v
      | _, _ => True
      end
 end.

Lemma unsigned_repr_le: forall i, 0 <= i -> Int.unsigned (Int.repr i) <= i.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  apply Zmod_le; try assumption.
  pose proof Int.Z_mod_modulus_range i.
  lia.
Qed.

Lemma mapsto_aligned:
 forall t ch, access_mode t = By_value ch ->
  forall  sh b z p,
  mapsto sh t (Vptr b z) p
   ⊢ ⌜(Memdata.align_chunk ch | Ptrofs.unsigned z)⌝.
Proof.
intros.
unfold mapsto. simpl.
rewrite H.
if_tac.
- simple_if_tac.
  { iIntros "[]". }
  iIntros "[H | H]".
  + rewrite (res_predicates.address_mapsto_align).
    iDestruct "H" as "(_ & _ & $)".
  + iDestruct "H" as (??) "H".
    rewrite (res_predicates.address_mapsto_align).
    iDestruct "H" as "(_ & $)".
- simple_if_tac.
  { iIntros "[]". }
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
 unfold init_data_size. rewrite Z.max_l; auto. lia.
Qed.

Lemma init_data2pred_rejigger {cs: compspecs}:
  forall (Delta : tycontext)  (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs v,
  tc_environ Delta rho ->
  v = Vptr b (Ptrofs.repr 0) ->
  readable_share sh ->
   init_data2pred (globals_of_env rho) idata sh (offset_val ofs v)
    ⊢ init_data2pred' Delta (globals_of_env rho) idata sh (offset_val ofs v).
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
 red in H7.
 unfold globals_of_env.
 destruct_var_types i eqn:Hv&Hv'; rewrite ?Hv ?Hv';
  destruct_glob_types i eqn:Hg&Hg'; rewrite ?Hg ?Hg';
try solve [simpl; apply TT_right].
 + rewrite H8. cancel.
 + replace (offset_val (Ptrofs.unsigned i0) (globals_of_env rho i)) with (Vptr b0 i0).
   trans (mapsto sh (Tpointer t noattr) (offset_val ofs v) (Vptr b0 i0)).
   2: { simpl offset_val. rewrite !Ptrofs.add_zero_l.
        rewrite Ptrofs.repr_unsigned.
        destruct t; auto; try apply derives_refl.
        unfold mapsto; simpl.
        destruct (offset_val ofs v); auto. rewrite -> !if_true by auto. rewrite andb_false_r.
        apply derives_refl. }
   unfold mapsto; simpl.
   destruct (offset_val ofs v); auto. rewrite andb_false_r /=. rewrite -> !if_true by auto.
   rewrite !Ptrofs.add_zero_l //.
   { unfold globals_of_env. rewrite Hg'. simpl. rewrite Ptrofs.add_zero_l.
     f_equal. rewrite Ptrofs.repr_unsigned; auto. }
Qed.

Lemma readable_readonly2share: forall ro, readable_share (readonly2share ro).
Proof.
intros. apply initialize.readable_readonly2share.
Qed.

Lemma unpack_globvar  {cs: compspecs}:
  forall Delta gz i t gv idata,
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0 = true)%bool ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   init_data_size idata <= sizeof t ->
   sizeof t <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) ∧ ⎡globvar2pred gz (i, gv)⎤ ⊢
       ⎡init_data2pred' Delta gz idata (readonly2share (gvar_readonly gv)) (gz i)⎤.
Proof.
intros.
go_lowerx. subst gz.
etrans; [eapply tc_globalvar_sound'; try eassumption | ].
assert (RS:= readable_readonly2share (gvar_readonly gv)).
forget (readonly2share (gvar_readonly gv)) as sh.
autorewrite with subst norm1 norm2; normalize.
unfold init_data_list2pred.
rewrite bi.sep_emp.
destruct (globvar_eval_var _ _ _ _ H7 H H0) as [b [? ?]].
assert (globals_of_env rho i = offset_val 0 (globals_of_env rho i)).
unfold globals_of_env.
rewrite H9. reflexivity.
rewrite -> H10 at 1.
trans (init_data2pred' Delta (globals_of_env rho) idata sh
      (offset_val 0 (globals_of_env rho i))).
+ rewrite andb_true_iff in H1; destruct H1.
  eapply init_data2pred_rejigger; eauto; try lia.
  unfold globals_of_env; rewrite H9; reflexivity.
+ unfold init_data2pred'.
  rewrite <- H10.
  destruct idata; unfold_lift;
    try (rewrite H8; simpl; rewrite Ptrofs.add_zero_l; auto);
  try apply derives_refl.
Qed.

Fixpoint id2pred_star   {cs: compspecs}
   (Delta: tycontext) (gz: globals) (sh: share) (v: val) (dl: list init_data) : mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta gz d sh v
                   ∗ id2pred_star Delta gz sh (offset_val (init_data_size d) v) dl'
 | nil => emp
 end.

Arguments id2pred_star cs Delta gz sh v dl  / .

Lemma init_data_size_pos : forall a, init_data_size a >= 0.
Proof.
 destruct a; simpl; try lia.
destruct Archi.ptr64; lia.
Qed.

Lemma init_data_list_size_pos : forall a, init_data_list_size a >= 0.
Proof.
 induction a; simpl.
 lia.
 pose proof (init_data_size_pos a); lia.
Qed.

Lemma unpack_globvar_star  {cs: compspecs}:
  forall Delta gz i gv,
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some (gvar_info gv) ->
   gvar_volatile gv = false ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) ∧ ⎡globvar2pred gz (i, gv)⎤ ⊢
       ⎡id2pred_star Delta gz (readonly2share (gvar_readonly gv)) (gz i) (gvar_init gv)⎤.
Proof.
intros until 2. pose proof I. intros H2.
remember (gvar_info gv) as t eqn:H3; symmetry in H3.
remember (gvar_init gv) as idata eqn:H4; symmetry in H4.
intros.
go_lowerx. fold id2pred_star. subst gz.
etrans; [eapply tc_globalvar_sound'; eassumption | ].
assert (RS:= readable_readonly2share (gvar_readonly gv)).
forget (readonly2share (gvar_readonly gv)) as sh.
set (ofs:=0%Z).
assert (alignof t | Ptrofs.unsigned (Ptrofs.repr ofs)) by (subst ofs; simpl; apply Z.divide_0_r).
destruct (globvar_eval_var _ _ _ _ H5 H H0) as [b [_ H9']].
unfold globals_of_env. rewrite H9'. clear H9'.
remember (Vptr b Ptrofs.zero) as x.
replace x with (offset_val ofs x) at 1 2 by (subst x; normalize).
fold (globals_of_env rho).
clearbody ofs.
clear - H5 RS Heqx.
revert ofs.
induction idata; simpl; auto; intros.
fold id2pred_star.
apply bi.sep_mono.
* clear IHidata.
  eapply init_data2pred_rejigger; eauto.
* specialize (IHidata (ofs + init_data_size a)).
  rewrite offset_offset_val.
  apply IHidata.
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
  ⌜isptr v⌝ ∧ ⌜align_compatible (Tint sz sign noattr) v⌝ ∧
  ⌜offset_strict_in_range (sizeof (Tint sz sign noattr) * n) v⌝ ∧
  (⎡id2pred_star Delta gz sh v mdata⎤ : assert) ⊢
  ⎡data_at sh (tarray (Tint sz sign noattr) n)
           (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data) v⎤.
Proof.
  intros. subst n mdata.
  replace (Zlength (map  (inttype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  go_lowerx.
  fold id2pred_star.
  change (offset_strict_in_range (sizeof (Tint sz sign noattr) * Zlength data) v) in H1.
  assert (offset_strict_in_range (sizeof (Tint sz sign noattr) * 0) v) by
    (unfold offset_strict_in_range; destruct v; auto; pose proof Ptrofs.unsigned_range i; lia).
  unfold tarray.
  set (t := Tint sz sign noattr) in *.
  revert v H H0 H1 H2; induction data; intros.
*
  rewrite Zlength_nil. unfold data_at, field_at; simpl.
  unfold at_offset; simpl.
   unfold nested_field_type; simpl.
   rewrite data_at_rec_eq. unfold  aggregate_pred.aggregate_pred.array_pred.
  unfold aggregate_pred.array_pred. simpl.
  repeat apply bi.and_intro; auto; try apply bi.pure_intro; try reflexivity.
  hnf. simpl.
  split3; auto.
  split3; auto.
  hnf. destruct v; auto. replace (sizeof (Tarray (Tint sz sign noattr) 0 noattr)) with 0 by (destruct sz; simpl; auto).
  pose proof Ptrofs.unsigned_range i; lia.
  hnf; destruct v; auto. apply align_compatible_rec_Tarray. intros. lia.
*
rewrite Zlength_cons.
simpl map.
unfold id2pred_star; fold @id2pred_star.
erewrite (split2_data_at_Tarray sh t (Z.succ (Zlength data)) 1).
4: rewrite sublist_same.
4: apply eq_refl.
2: list_solve.
2: list_solve. 2: auto. 2: list_solve. 2: apply eq_refl. 2: apply eq_refl.
rewrite -> (sublist_one) by list_solve.
autorewrite with sublist.
rewrite sublist_1_cons.
rewrite -> sublist_same by list_solve.
apply bi.sep_mono.
+
clear IHdata.
fold (tarray t 1). erewrite data_at_singleton_array_eq by apply eq_refl.
rewrite <- (mapsto_data_at sh t (Vint (Cop.cast_int_int sz sign a)) (Vint (Cop.cast_int_int sz sign a)) v); try reflexivity; auto.
2: subst t; destruct sz, sign; reflexivity.
2:{
destruct v; auto. red.
assert (sizeof t > 0).
subst t; unfold sizeof; simpl. destruct sz; computable.
clearbody t.
clear - H1 H3.
rewrite Zlength_cons in H1. simpl in H1.
unfold Z.succ in H1. rewrite Z.mul_add_distr_l in H1.
pose proof (Zlength_nonneg data).
rewrite Z.mul_1_r in H1.
assert (0 <= sizeof t * Zlength data)
  by (apply Z.mul_nonneg_nonneg; lia).
 lia.
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
   rewrite -> Z.mul_0_r in *.
   assert (0 <= sizeof t * Zlength data) by (apply Z.mul_nonneg_nonneg; lia).
   unfold offset_strict_in_range, offset_val in *.
   unfold align_compatible in H0|-*.
   unfold Ptrofs.add.
   rewrite -> (Ptrofs.unsigned_repr (sizeof t)) 
    by (unfold sizeof, Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize;
          clear; subst t; destruct sz,sign, Archi.ptr64; simpl; computable).
  rewrite Ptrofs.unsigned_repr.
  split3; try lia.
   assert (exists ch, access_mode t = By_value ch)
     by (clear; subst t; destruct sz,sign; eexists; reflexivity).
  destruct H8 as [ch ?].
  apply align_compatible_rec_by_value_inv with (ch:=ch) in H0; auto.
  apply align_compatible_rec_by_value with (ch:=ch); auto.
   apply Z.divide_add_r; auto.
  clear - H8. subst t. destruct sz,sign; inv H8; simpl; apply Z.divide_refl.
  unfold Ptrofs.max_unsigned.
  lia.
 }
 destruct H8 as [H8a [H8b H8c]].
  etrans; [ apply IHdata | ]; clear IHdata; auto.
  replace (Z.succ (Zlength data) - 1) with (Zlength data) by (clear; lia).
  apply bi.equiv_entails_1_1; f_equiv; hnf.
  unfold field_address0.
  rewrite if_true.
  unfold offset_val. destruct v; simpl; auto. f_equal.
  subst t; destruct sz,sign; reflexivity.
  eapply field_compatible0_cons_Tarray.
  reflexivity.
  hnf; simpl. split3; auto. 
  destruct v; try contradiction.
  split3; auto; red.
  unfold sizeof, Ctypes.sizeof;  fold Ctypes.sizeof. fold (sizeof t).
  pose proof (Zlength_nonneg data).
  rewrite -> Z.max_r by lia.
  unfold offset_strict_in_range in H1. rewrite Zlength_cons in H1.
  lia.
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
  pose proof (Zlength_nonneg data); lia.
Qed.

Lemma id2pred_star_ZnthV_tint  {cs: compspecs}:
 forall Delta gz sh n (v: val) (data: list int) mdata,
  n = Zlength mdata ->
  mdata = map Init_int32 data ->
  ⌜isptr v⌝ ∧ ⌜align_compatible tint v⌝ ∧
  ⌜offset_strict_in_range (sizeof tint * n) v⌝ ∧
  (⎡id2pred_star Delta gz sh v mdata⎤ : assert) ⊢
  ⎡data_at sh (tarray tint n) (map Vint data) v⎤.
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
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   t = Tint sz sign noattr ->
  forall    (NBS: notboolsize sz),
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (inttype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) ∧ ⎡globvar2pred gz(i, gv)⎤ ⊢
      ⎡data_at (readonly2share (gvar_readonly gv))
         (tarray (Tint sz sign noattr) n)
         (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)
         (gz i)⎤.
Proof.
  intros. subst t.
  iIntros "(#? & H)".
  iPoseProof (unpack_globvar_star with "[$H]") as "H"; first auto.
  rewrite H5.
  rewrite -(id2pred_star_ZnthV_Tint Delta gz); auto.
  iStopProof; go_lowerx.
  rewrite monPred_at_intuitionistically.
  fold id2pred_star.
  iIntros "((% & ->) & $)"; iPureIntro.
  assert (headptr (globals_of_env rho i)). {
    unfold globals_of_env. eapply globvar_eval_var in H0 as [b [_ H10]]; eauto. rewrite H10.
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
 split; first done; split; first done; split; last done.
 unfold offset_strict_in_range.
 destruct (globals_of_env rho i) eqn:?H; auto.
 rewrite H1 H5 /= /sizeof /= in H6.
 pose proof initial_world.zlength_nonneg _ (gvar_init gv).
 rewrite -> Z.max_r in H6 by lia.
 change (match sz with I16 => 2 | I32 => 4 | _ => 1 end)
   with (sizeof (Tint sz sign noattr)) in H6.
 unfold Ptrofs.max_unsigned in H6.
 pose proof init_data_list_size_pos (gvar_init gv).
 simpl in H8.
 unfold globals_of_env in H9. destruct (Map.get (ge_of rho) i) eqn:?H; inv H9.
 rewrite Ptrofs.unsigned_zero.
 change (match sz with
         | I16 => 2
         | I32 => 4
         | _ => 1
         end) with (sizeof (Tint sz sign noattr)).
 split; try lia.
 rewrite Z.add_0_l.
 apply Z.mul_nonneg_nonneg.
 clear; pose proof (sizeof_pos (Tint sz sign noattr)); lia.
   apply Zlength_nonneg.
{ rewrite -H5 //. }
Qed.

Definition float_type (sz: floatsize) : Type :=
   match sz with F32 => float32 | F64 => float end.

Definition float_constructor (sz: floatsize) :  float_type sz -> val
 :=   match sz with F32 => Vsingle | F64 => Vfloat end.

Definition floattype2init_data (sz: floatsize) : (float_type sz -> init_data) :=
 match sz with F32 => Init_float32 | F64 => Init_float64 end.

Lemma id2pred_star_ZnthV_tfloat  {cs: compspecs}:
 forall Delta sz gz sh n (v: val) (data: list (float_type sz)) mdata,
  n = Zlength mdata ->
  mdata = map (floattype2init_data sz) data ->
  ⌜isptr v⌝ ∧ ⌜align_compatible (Tfloat sz noattr) v⌝ ∧
  ⌜offset_strict_in_range (sizeof (Tfloat sz noattr) * n) v⌝ ∧
  (⎡id2pred_star Delta gz sh v mdata⎤ : assert) ⊢
  ⎡data_at sh (tarray (Tfloat sz noattr) n) (map  (float_constructor sz) data) v⎤.
Proof. intros.
  subst n mdata.
  replace (Zlength (map  (floattype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  go_lowerx.
  fold id2pred_star.
  change (offset_strict_in_range (sizeof (Tfloat sz noattr) * Zlength data) v) in H1.
  assert (offset_strict_in_range (sizeof (Tfloat sz noattr) * 0) v) by
    (unfold offset_strict_in_range; destruct v; auto; pose proof Ptrofs.unsigned_range i; lia).
unfold tarray.
set (t := Tfloat sz noattr) in *.
revert v H H0 H1 H2; induction data; intros.
*
  rewrite Zlength_nil. unfold data_at, field_at; simpl.
  unfold at_offset; simpl.
   unfold nested_field_type; simpl.
   rewrite data_at_rec_eq. unfold  aggregate_pred.aggregate_pred.array_pred.
  unfold aggregate_pred.array_pred. simpl.
  repeat apply bi.and_intro; auto; try apply bi.pure_intro; try reflexivity.  
  hnf. simpl.
  split3; auto.
  split3; auto.
  hnf. destruct v; auto. replace (sizeof (Tarray (Tfloat sz noattr) 0 noattr)) with 0 by (destruct sz; simpl; auto).
  pose proof Ptrofs.unsigned_range i; lia.
  hnf; destruct v; auto. apply align_compatible_rec_Tarray. intros. lia.
*
rewrite Zlength_cons.
simpl map.
unfold id2pred_star; fold @id2pred_star.
erewrite (split2_data_at_Tarray sh t (Z.succ (Zlength data)) 1).
4: rewrite sublist_same.
4: apply eq_refl.
2: list_solve.
2: list_solve. 2: auto. 2: list_solve. 2: apply eq_refl. 2: apply eq_refl.
rewrite -> (sublist_one) by list_solve.
autorewrite with sublist.
rewrite sublist_1_cons.
rewrite -> sublist_same by list_solve.
apply bi.sep_mono.
+
clear IHdata.
fold (tarray t 1). erewrite data_at_singleton_array_eq by apply eq_refl.
rewrite <- (mapsto_data_at sh t (float_constructor sz a)
                          (float_constructor sz a) v); try reflexivity; auto.
2: subst t; destruct sz; reflexivity.
2:{
destruct v; auto. red.
assert (sizeof t > 0).
subst t; unfold sizeof; simpl. destruct sz; computable.
clearbody t.
clear - H1 H3.
rewrite Zlength_cons in H1. simpl in H1.
unfold Z.succ in H1. rewrite Z.mul_add_distr_l in H1.
pose proof (Zlength_nonneg data).
rewrite Z.mul_1_r in H1.
assert (0 <= sizeof t * Zlength data)
  by (apply Z.mul_nonneg_nonneg; lia).
 lia.
}
subst t.
normalize.
unfold init_data2pred', inttype2init_data.
destruct sz; apply derives_refl.
+
  replace (init_data_size (floattype2init_data sz a)) with (sizeof t) 
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
   rewrite -> Z.mul_0_r in *.
   assert (0 <= sizeof t * Zlength data) by (apply Z.mul_nonneg_nonneg; lia).
   unfold offset_strict_in_range, offset_val in *.
   unfold align_compatible in H0|-*.
   unfold Ptrofs.add.
   rewrite -> (Ptrofs.unsigned_repr (sizeof t))
    by (unfold sizeof, Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize;
          clear; subst t; destruct sz, Archi.ptr64; simpl; computable).
  rewrite Ptrofs.unsigned_repr.
  split3; try lia.
   assert (exists ch, access_mode t = By_value ch)
     by (clear; subst t; destruct sz; eexists; reflexivity).
  destruct H8 as [ch ?].
  apply align_compatible_rec_by_value_inv with (ch:=ch) in H0; auto.
  apply align_compatible_rec_by_value with (ch:=ch); auto.
   apply Z.divide_add_r; auto.
  clear - H8. subst t. 
  destruct sz; inv H8; simpl; (apply Zmod_divide; [lia | reflexivity]).
  unfold Ptrofs.max_unsigned.
  lia.
 }
 destruct H8 as [H8a [H8b H8c]].
  etrans; [ apply IHdata | ]; clear IHdata; auto.
  replace (Z.succ (Zlength data) - 1) with (Zlength data) by (clear; lia).
   apply bi.equiv_entails_1_1; f_equal.
 unfold field_address0.
  rewrite if_true.
  unfold offset_val. destruct v; simpl; auto. f_equiv; hnf.
  subst t; destruct sz; reflexivity.
  eapply field_compatible0_cons_Tarray.
  reflexivity.
  hnf; simpl. split3; auto. 
  destruct v; try contradiction.
  split3; auto; red.
  unfold sizeof, Ctypes.sizeof;  fold Ctypes.sizeof. fold (sizeof t).
  pose proof (Zlength_nonneg data).
  rewrite -> Z.max_r by lia.
  unfold offset_strict_in_range in H1. rewrite Zlength_cons in H1.
  lia.
  apply align_compatible_rec_Tarray; intros.
  unfold align_compatible, offset_val in H8a.
  assert (exists ch, access_mode t = By_value ch)
     by (clear; subst t; destruct sz; eexists; reflexivity).
   destruct H4 as [ch ?].
  eapply align_compatible_rec_by_value; try eassumption.
  simpl in H0.
  eapply align_compatible_rec_by_value_inv in H0; try eassumption.
  apply Z.divide_add_r; auto.
  apply Z.divide_mul_l; auto.
  clear - t H4.
  subst t.
  destruct sz; inv H4; simpl; (apply Zmod_divide; [lia | reflexivity]).
  pose proof (Zlength_nonneg data); lia.
Qed.

Lemma unpack_globvar_array_float  {cs: compspecs}:
  forall t sz (data: list (float_type sz))  n Delta gz i gv,
   (var_types Delta) !! i = None ->
   (glob_types Delta) !! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   t = Tfloat sz noattr ->
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (floattype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (`and (tc_environ Delta) (fun rho =>gz = globals_of_env rho)) ∧ ⎡globvar2pred gz(i, gv)⎤ ⊢
      ⎡data_at (readonly2share (gvar_readonly gv))
         (tarray (Tfloat sz noattr) n)
         (map (float_constructor sz) data)
         (gz i)⎤.
Proof.
  intros. subst t.
  iIntros "(#? & H)".
  iPoseProof (unpack_globvar_star with "[$H]") as "H"; first auto.
  rewrite H5.
  rewrite -(id2pred_star_ZnthV_tfloat Delta sz gz); auto.
  iStopProof; go_lowerx.
  rewrite monPred_at_intuitionistically.
  fold id2pred_star.
  iIntros "((% & ->) & $)"; iPureIntro.
  assert (headptr (globals_of_env rho i)). {
    unfold globals_of_env. destruct  (globvar_eval_var _ _ _ _ H3 H H0) as [b [_ H10]]. rewrite H10.
    exists b; auto. 
  }
  assert (align_compatible (Tfloat sz noattr) (globals_of_env rho i)). {
    destruct H7 as [b ?]. rewrite H7.
   assert (exists ch, access_mode (Tfloat sz noattr) = By_value ch)
     by (clear; destruct sz; eexists; reflexivity).
   destruct H8 as [ch ?].
    eapply align_compatible_rec_by_value; try eassumption.
    rewrite Ptrofs.unsigned_zero.
    apply Z.divide_0_r.
  }
 apply headptr_isptr in H7.
 split; first done; split; first done; split; last done.
 unfold offset_strict_in_range.
 destruct (globals_of_env rho i) eqn:?H; auto.
 rewrite H1 H5 /= /sizeof /= in H6.
 pose proof initial_world.zlength_nonneg _ (gvar_init gv).
 rewrite -> Z.max_r in H6 by lia.
 change (match sz with F32 => 4 | F64 => 8 end)
   with (sizeof (Tfloat sz noattr)) in *.
 unfold Ptrofs.max_unsigned in H6.
 pose proof init_data_list_size_pos (gvar_init gv).
 simpl in H8.
 unfold globals_of_env in H9. destruct (Map.get (ge_of rho) i) eqn:?H; inv H9.
 rewrite Ptrofs.unsigned_zero.
 split; try lia.
 rewrite Z.add_0_l.
 apply Z.mul_nonneg_nonneg.
 clear; pose proof (sizeof_pos (Tfloat sz noattr)); lia.
   apply Zlength_nonneg.
{ rewrite -H5 //. }
Qed.

Definition gv_globvars2pred (gv: ident->val) (vl: list (ident * globvar type)) : mpred :=
  (fold_right_sepcon (map (globvar2pred gv) vl)).

(*
Lemma globvars2pred_relate:
 forall gv vl rho, 
  gvars_denote gv rho ->
  globvars2pred gv vl =
  gv_globvars2pred gv vl.
Proof.
 intros.
 unfold globvars2pred, lift2.
 rewrite prop_true_andp by auto.
 unfold gv_globvars2pred.
 induction vl; simpl; auto.
 f_equal; auto.
 clear - H.
 unfold globvar2pred, initialize.gv_globvar2pred.
 simple_if_tac; auto.
 destruct a. destruct g. simpl.
 forget (gv i) as p. 
 revert p; induction gvar_init; simpl; intros; auto.
 change (predicates_sl.sepcon ?A ?B) with (sepcon A  B).
 f_equal; auto.
 destruct a; simpl; auto.
 hnf in H. rewrite H.
 destruct (Map.get (ge_of rho) i0); auto.
Qed.
 *)

Definition globvars_in_process (gv: globals) (done: list mpred)
               (halfdone: mpred)
               (al: list (ident * globvar type)) : assert :=
 local (gvars_denote gv) ∧
 ⎡fold_right_sepcon done ∗ halfdone ∗ globvars2pred gv al⎤.

Context {Espec: OracleKind} `{!externalGS OK_ty Σ} {cs: compspecs}.

Lemma start_globvars_in_process:
  forall E Delta P Q R
          gz al SF c Post,
  semax E Delta
    ((PROPx P (LOCALx (gvars gz :: Q) (SEPx R)) ∗
          globvars_in_process gz nil emp al) ∗ SF) c Post ->
  semax E Delta
    ((PROPx P (LOCALx (gvars gz :: Q) (SEPx R)) ∗
     ⎡globvars2pred gz al⎤) ∗ SF) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H].
rewrite /globvars_in_process; go_lowerx.
iIntros "((($ & ((% & %) & $)) & $ ) & $)"; auto.
Qed.

Lemma semax_process_globvars:
  forall E Delta P Q R R'
          gz al SF c Post,
  ENTAIL Delta, globvars_in_process gz R emp al ⊢ globvars_in_process gz R' emp nil ->
  semax E Delta
    ((PROPx P (LOCALx (gvars gz :: Q) (SEPx R')) ∗ emp) ∗ SF) c Post ->
  semax E Delta
    ((PROPx P (LOCALx (gvars gz :: Q) (SEPx R)) ∗
          ⎡globvars2pred gz al⎤) ∗ SF) c Post.
Proof.
intros.
apply start_globvars_in_process.
eapply semax_pre; [ | apply H0].
iIntros "(#? & (($ & $ & HR) & Hglob) & $)".
rewrite /globvars_in_process in H |- *.
iPoseProof (H with "[-]") as "(_ & $ & _)".
iDestruct "Hglob" as "($ & _ & $ & $)"; auto.
Qed.

Lemma process_globvar':
  forall {cs: compspecs} Delta done (i: ident)
          gz gv al (idata : init_data) t,
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_info gv = t ->
       gvar_init gv = (idata::nil) ->
       init_data_size idata <= sizeof t ->
       sizeof t <= Ptrofs.max_unsigned ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz done
            (id2pred_star Delta gz
                         (readonly2share (gvar_readonly gv))
                         (gz i) (idata ::nil))
                  al.
Proof.
intros.
pose proof  (unpack_globvar Delta gz i t gv idata H H0 H1 H2 H3 H4 H5 H6).
clear H H0 H1 H2 H3 H4 H5 H6.
unfold globvars_in_process.
unfold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
iApply (H7 with "[-]"); iFrame; eauto.
Qed.

Lemma process_globvar_array:
  forall Delta done gz (i: ident)
          gv al (n: Z) (t: type)  (sz : intsize) (sign : signedness) (data : list int),
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some (gvar_info gv) ->
       gvar_info gv = tarray t n ->
       gvar_volatile gv = false ->
       t = Tint sz sign noattr ->
       notboolsize sz ->
       n = Zlength (gvar_init gv) ->
       gvar_init gv = map (inttype2init_data sz) data ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  ENTAIL Delta,   
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz 
        (data_at
                   (readonly2share (gvar_readonly gv))
                   (tarray (Tint sz sign noattr) n)
                   (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data) (gz i) :: done)
        emp al.
Proof.
intros.
pose proof (unpack_globvar_array _ _ _ _ _ _ gz _ _ H H0 H1 H2 H3 H4 H5 H6 H7).
clear H H0 H1 H2 H3 H4 H5 H6 H7.
unfold globvars_in_process.
unfold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
iApply (H8 with "[-]"); iFrame; eauto.
Qed.

Lemma process_globvar_array_float:
  forall Delta done gz (i: ident)
          gv al (n: Z) (t: type)  (sz : floatsize)
         (data : list (float_type sz)),
       Maps.PTree.get i (var_types Delta) = None ->
       Maps.PTree.get i (glob_types Delta) = Some (gvar_info gv) ->
       gvar_info gv = tarray t n ->
       gvar_volatile gv = false ->
       t = Tfloat sz noattr ->
       n = Zlength (gvar_init gv) ->
       gvar_init gv = map (floattype2init_data sz) data ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz 
        (data_at
                   (readonly2share (gvar_readonly gv))
                   (tarray (Tfloat sz noattr) n)
                   (map (float_constructor sz) data) (gz i) :: done)
        emp al.
Proof.
intros.
assert (H8 := unpack_globvar_array_float _ _ _ _ _ gz _ _ H H0 H1 H2 H3 H4 H5 H6).
clear H H0 H1 H2 H3 H4 H5 H6.
unfold globvars_in_process.
unfold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
iApply (H8 with "[-]"); iFrame; eauto.
Qed.

Lemma process_globvar_star':
  forall {cs: compspecs} Delta done gz (i: ident)
          gv al,
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some (gvar_info gv) ->
       gvar_volatile gv = false ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz done
            (id2pred_star Delta gz
                         (readonly2share (gvar_readonly gv))
                         (gz i) (gvar_init gv))
                  al.
Proof.
intros.
assert (H5 := unpack_globvar_star _ gz _ _ H H0 H1).
clear H H0 H1.
unfold globvars_in_process, globvars2pred.
go_lowerx.
iIntros "($ & _ & ? & $)".
iApply (H5 with "[-]"); iFrame; eauto.
Qed.

Fixpoint init_datalist2pred' {cs: compspecs}
     (Delta: tycontext) (gv: globals) (dl: list init_data)  (sh: share) (ofs: Z) (v: val) : mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta gv d sh (offset_val ofs v) 
                ∗ init_datalist2pred' Delta gv dl' sh (ofs + init_data_size d) v
 | nil => emp
 end.

Lemma halfprocess_globvar_star:
  forall {cs: compspecs} Delta done gz (i: ident)
          gv al,
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
  ENTAIL Delta,   
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz
       (init_datalist2pred' Delta gz (gvar_init gv) (readonly2share (gvar_readonly gv)) 0 (gz i) :: done)
            emp  al.
Proof.
intros.
unfold globvars_in_process.
unfold globvars2pred; fold globvars2pred.
go_lowerx.
iIntros "($ & _ & H & $)".
unfold globvar2pred.
simpl.
rewrite H2.
pose proof (readable_readonly2share (gvar_readonly gv)).
forget (readonly2share (gvar_readonly gv)) as sh.
replace gz with (globals_of_env rho).
rewrite <- offset_zero_globals_of_env at 1.
set (ofs:=0).
clearbody ofs.
iInduction (gvar_init gv)as [|] "IH" forall (ofs); simpl.
{ done. }
iDestruct "H" as "(H & ?)"; iSplitL "H".
- destruct (globvar_eval_var _ _ _ _ H4 H H0) as [b [? ?]].
  iApply init_data2pred_rejigger; eauto.
  unfold globals_of_env.
  rewrite H8. reflexivity.
- iApply "IH".
  + iPureIntro.
    simpl in H3.
    pose proof (init_data_size_pos a).
    lia.
  + rewrite offset_offset_val //.
Qed.

Lemma map_instantiate:
  forall {A B} (f: A -> B) (x: A) (y: list B) z,
    y = map f z ->  f x :: y = map f (x :: z).
Proof. intros. subst. reflexivity. Qed.

(*
Lemma main_pre_start:
 forall {Z} prog (gv:ident -> val) (ora : Z),
   main_pre prog ora gv = (PROPx nil (LAMBDAx (gv::nil) nil (SEPx (has_ext ora::nil)))%assert * (globvars2pred gv (prog_vars prog))).
Proof.
intros.
unfold main_pre.
unfold gglobvars2pred, globvars2pred, PROPx, GLOBALSx, PARAMSx, LOCALx, SEPx, argsassert2assert. simpl.
unfold lift2. simpl.
extensionality rho.
simpl.
normalize. destruct rho; simpl.
unfold gvars_denote. unfold_lift. unfold local, lift1.
rewrite sepcon_comm. unfold Clight_seplog.mkEnv; simpl. unfold seplog.globals_only, globals_of_env; simpl.
apply pred_ext; normalize.
+ apply bi.and_intro. apply bi.pure_intro. intuition. trivial.
+ apply bi.and_intro. apply bi.pure_intro. intuition. trivial.
Qed.
 *)

Definition main_pre_old (prog: Clight.program) (ora: OK_ty) (gv: globals) : assert :=
local (fun rho => gv = globals_of_env rho) ∧
   ⎡globvars2pred gv (prog_vars prog) ∗ has_ext ora⎤.

Lemma main_pre_start_old:
 forall prog gv ora,
   main_pre_old prog ora gv ⊣⊢ (PROP() LOCAL(gvars gv) SEP(has_ext ora))%assert ∗ ⎡globvars2pred gv (prog_vars prog)⎤.
Proof.
intros.
unfold main_pre_old.
unfold globvars2pred,  PROPx, LOCALx, SEPx.
split => rho; monPred.unseal.
unfold_lift; rewrite /lift1.
normalize.
rewrite and_True True_and bi.sep_comm //.
Qed.

(*
Lemma init_data2pred_ge_eq {rho sigma a sh v} (RS : ge_of rho = ge_of sigma):
      init_data2pred a sh v = init_data2pred a sh v sigma.
Proof. destruct a; simpl; intros; trivial. rewrite RS; trivial. Qed.

Lemma initdata_list2pred_ge_eq {rho sigma} (RS : ge_of rho = ge_of sigma):
      forall l sh v, init_data_list2pred l sh v rho = init_data_list2pred l sh v sigma.
Proof.
induction l; simpl; intros; trivial.
rewrite IHl, (init_data2pred_ge_eq RS); clear IHl. trivial.
Qed.

Lemma globvar2pred_ge_eq {rho sigma gz x} (RS: ge_of rho = ge_of sigma):
      globvar2pred gz x rho = globvar2pred gz x sigma.
Proof.
destruct x; unfold globvar2pred; simpl.
destruct (gvar_volatile g). reflexivity.
apply (initdata_list2pred_ge_eq RS).
Qed.

Lemma globvars2pred_ge_eq_entails {rho sigma gz} (RS: ge_of rho = ge_of sigma):
      forall l, globvars2pred gz l rho ⊢ globvars2pred gz l sigma.
Proof.
unfold globvars2pred, lift2. induction l.
+ simpl. unfold globals_of_env; rewrite RS; trivial.
+ eapply derives_trans. simpl. rewrite sepcon_comm, <- sepcon_andp_prop'.
  apply bi.sep_mono. apply IHl. apply derives_refl. clear IHl.
  simpl. rewrite sepcon_andp_prop', sepcon_comm, (globvar2pred_ge_eq RS). trivial.
Qed.

Lemma globvars2pred_ge_eq {rho sigma gz l} (RS: ge_of rho = ge_of sigma):
      globvars2pred gz l rho = globvars2pred gz l sigma.
Proof. apply pred_ext; apply globvars2pred_ge_eq_entails; [ | symmetry]; trivial. Qed.
 *)

Lemma close_precondition_main {p ora gv}:
close_precondition nil (main_pre p ora gv) ⊣⊢ main_pre_old p ora gv.
Proof.
rewrite /close_precondition /main_pre /main_pre_old.
split => rho; simpl; monPred.unseal; rewrite /lift1.
iSplit.
- iIntros "H"; iDestruct "H" as (? _ (-> & ?)) "$"; auto.
- iIntros "(% & $)"; iExists []; auto.
Qed.


Lemma process_globvar_space0:
  forall {cs: compspecs} Delta done (i: ident)
          gz gv al t,
       gvar_info gv = t ->
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv)
   && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0
   && fully_nonvolatile (rank_type cenv_cs t) t)%bool = true ->
       gvar_volatile gv = false ->
       gvar_init gv = (Init_space (sizeof t)::nil) ->
       sizeof t <= Ptrofs.max_unsigned ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz
       (data_at (readonly2share (gvar_readonly gv)) t  (zero_val t) (gz i) :: done)
            emp  al.
Proof.
intros until t. intros H3; intros.
rewrite andb_true_iff in H1. destruct H1 as [H1 Hvol].
assert (H7 := unpack_globvar Delta gz i t gv _ H H0 H1 H2 H3 H4).
spec H7.
simpl. pose proof (sizeof_pos t). rewrite -> Z.max_l by lia. lia.
specialize (H7 H5).
unfold globvars_in_process.
unfold globvars2pred; fold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
apply andb_true_iff in H1 as [H1 H9].
rewrite -> H3 in *.
iApply mapsto_zero_data_at_zero; last iApply H7; auto.
- apply readable_readonly2share.
- pose proof (la_env_cs_sound 0 t H1 H9).
  apply headptr_field_compatible; auto.
  + eapply go_lower.gvars_denote_HP; eauto.
  + red; auto.
  + rep_lia.
Qed.

Lemma process_globvar_space:
  forall {cs: compspecs} Delta done (i: ident)
          gz gv al t,
       gvar_info gv = t ->
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_init gv = (Init_space (sizeof t)::nil) ->
       sizeof t <= Ptrofs.max_unsigned ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz
       (data_at_  (readonly2share (gvar_readonly gv)) t (gz i) :: done)
            emp  al.
Proof.
intros until t. intros H3; intros.
assert (H7 := unpack_globvar Delta gz i t gv _ H H0 H1 H2 H3 H4).
spec H7.
simpl. pose proof (sizeof_pos t). rewrite -> Z.max_l by lia. lia.
specialize (H7 H5).
unfold globvars_in_process.
unfold globvars2pred; fold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
apply andb_true_iff in H1 as [H1 H9].
rewrite -> H3 in *.
iApply memory_block_data_at_.
{ subst t.
  pose proof (la_env_cs_sound 0 (gvar_info gv) H1 H9).
  apply headptr_field_compatible; auto.
  + eapply go_lower.gvars_denote_HP; eauto.
  + red; auto.
  + rep_lia. }
iApply mapsto_zeros_memory_block; iApply H7; auto.
Qed.

Lemma process_globvar_ptrarray_space:
  forall Delta done (i: ident)
          gz gv al t t' n,
       t = Tarray (Tpointer t' noattr) n noattr ->
       gvar_info gv = t ->
       (var_types Delta) !! i = None ->
       (glob_types Delta) !! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_init gv = (Init_space (sizeof t)::nil) ->
       sizeof t <= Ptrofs.max_unsigned ->
  ENTAIL Delta,   
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz
       (data_at  (readonly2share (gvar_readonly gv)) (Tarray (Tpointer t' noattr) n noattr)
                                  (Zrepeat nullval n)  (gz i) :: done)
            emp  al.
Proof.
intros until n. intros Ht H3; intros.
assert (H7 := unpack_globvar Delta gz i t gv _ H H0 H1 H2 H3 H4).
spec H7.
simpl. pose proof (sizeof_pos t). rewrite -> Z.max_l by lia. lia.
specialize (H7 H5).
unfold globvars_in_process.
unfold globvars2pred; fold globvars2pred.
go_lowerx.
iIntros "($ & $ & ? & $)".
apply andb_true_iff in H1 as [H1 H9].
rewrite -> H3 in *.
iPoseProof (H7 with "[-]") as "H"; first auto; simpl.
subst t; simpl.
destruct (zlt n 0).
-
unfold sizeof; simpl.
rewrite -> Z.max_l by lia.
rewrite Z.mul_0_r.
assert (readable_share (readonly2share (gvar_readonly gv)))
  by apply readable_readonly2share.
forget  (readonly2share (gvar_readonly gv)) as sh.
unfold mapsto_zeros.
destruct (gz i); try done.
unfold data_at, field_at.
change (nested_field_offset _ _) with 0.
unfold at_offset.
unfold nested_field_type; simpl.
rewrite data_at_rec_eq.
rewrite -> Z.max_l by lia.
change (unfold_reptype _) with (repeat nullval (Z.to_nat n)).
rewrite -> Z2Nat_neg by auto.  simpl repeat.
rewrite -> aggregate_pred.aggregate_pred.array_pred_len_0 by auto.
iDestruct "H" as "(% & _)"; iPureIntro.
split; last done.
split3; auto. apply I.
split3.
simpl. unfold sizeof; simpl.  lia.
2: apply I.
red. constructor; auto. intros. lia.
-
rewrite -> Z.max_r by lia.
unfold data_at.
erewrite @field_at_Tarray with (n:=n);
  [ | apply I | reflexivity | lia | apply JMeq_refl].
unfold mapsto_zeros.
destruct (gz i) eqn:?H; try done.
iDestruct "H" as "(% & H)".
assert (field_compatible0 (Tarray (Tpointer t' noattr) n noattr) (ArraySubsc 0::nil) (gz i)).
{ rewrite H10; split3; auto. apply I. split; auto. simpl. unfold sizeof; simpl.
   rewrite -> Z.max_r by lia. lia.
  split. red. apply align_compatible_rec_Tarray. intros.
     eapply align_compatible_rec_by_value. reflexivity.
     simpl.
  rewrite H8 in H10; unfold globals_of_env in H10. destruct (Map.get (ge_of rho) i); inv H10.
  normalize. apply Z.divide_mul_l. unfold Mptr.  destruct Archi.ptr64; exists 1; simpl; auto.
  simpl. split; auto. lia.
}
assert (Halign: (align_chunk Mptr | Ptrofs.unsigned i0)). {
  rewrite H8 in H10;
 clear - H10. unfold globals_of_env in H10. destruct (Map.get (ge_of rho) i); inv H10.
 apply Z.divide_0_r.
}
forget (gz i) as p.
assert (readable_share (readonly2share (gvar_readonly gv)))
  by apply readable_readonly2share.
forget (readonly2share (gvar_readonly gv)) as sh.
subst p.
unfold array_at.
rewrite prop_true_andp.
2:{ split; auto.
destruct H12 as [? [? [? [? [? ?]]]]].
split3; auto. split3; auto. simpl; split; auto. lia.
}
iSplit.
{ autorewrite with sublist; auto. }
rewrite -> Z2Nat.inj_mul; [ | destruct Archi.ptr64; lia| lia].
rewrite -> Z2Nat.inj_sub by lia.
change (Z.to_nat 0) with O. rewrite Nat.sub_0_r.
unfold nested_field_type; simpl.
unfold nested_field_offset; simpl.
unfold at_offset.
rewrite <- (Z2Nat.id n) in H11 by lia.
unfold Zrepeat.
clear - H11 H13 Halign.
rewrite mapsto_memory_block.address_mapsto_zeros_eq.
iInduction (Z.to_nat n) as [|] "IH" forall (i0 H11 Halign); intros; simpl.
{ done. }
autorewrite with sublist. normalize.
rewrite !Nat2Z.inj_mul.
rewrite -> Z2Nat.id by (destruct Archi.ptr64; computable).
rewrite inj_S. unfold Z.succ.
rewrite Z.add_comm.
rewrite -> Z.mul_add_distr_l.
rewrite -> Z.mul_1_r.
rewrite -> mapsto_memory_block.address_mapsto_zeros'_split by (destruct Archi.ptr64; rep_lia).
iDestruct "H" as "(H & ?)"; iSplitL "H".
+ unfold data_at_rec; simpl.
  unfold mapsto. simpl. rewrite -> if_true by done.
  rewrite andb_false_r.
  iLeft.
  rewrite -> prop_true_andp by apply mapsto_memory_block.is_pointer_or_null_nullval.
  iApply mapsto_memory_block.address_mapsto_address_mapsto_zeros; auto.
+ unfold adr_add.
  simpl.
  assert (H20: 0 <= (if Archi.ptr64 then 8 else 4) <= Ptrofs.max_unsigned)
    by (destruct Archi.ptr64; clear; rep_lia).
  change (if Archi.ptr64 then 8 else 4) with (size_chunk Mptr) in *.
  iSpecialize ("IH" $! (Ptrofs.add i0 (Ptrofs.repr (size_chunk Mptr)))).
  replace (Ptrofs.unsigned i0 + (size_chunk Mptr))
  with (Ptrofs.unsigned
           (Ptrofs.add i0 (Ptrofs.repr (size_chunk Mptr)))).
  iPoseProof ("IH" with "[%] [%] [$]") as "?".
  { split; first rep_lia.
    rewrite inj_S in H11.
    unfold Ptrofs.add.
    rewrite Ptrofs.unsigned_repr.
    rewrite -> Ptrofs.unsigned_repr by lia.
    lia.
    rewrite -> Ptrofs.unsigned_repr by lia.
    rep_lia. }
  { unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr.
    apply Z.divide_add_r; auto.
    rewrite -> Ptrofs.unsigned_repr by lia.
    apply align_size_chunk_divides.
    rewrite -> Ptrofs.unsigned_repr by lia.
    rep_lia. }
  iApply (aggregate_pred.rangespec_shift_derives with "[$]").
  intros.
  rewrite Z.sub_0_r in H0. subst i.
  rewrite !Z.sub_0_r.
  rewrite -> Znth_pos_cons by lia.
  rewrite <- (Nat2Z.id n0).
  rewrite -> !Znth_repeat_inrange by lia.
  apply bi.equiv_entails_1_1. f_equiv; hnf; simpl.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr.
  f_equal. f_equal. lia.
  { unfold Ptrofs.add.
    rewrite Ptrofs.unsigned_repr //.
    rewrite -> Ptrofs.unsigned_repr by (destruct Archi.ptr64; rep_lia).
    rep_lia. }
Qed.

Lemma process_globvar_extern:
 forall {CS: compspecs} Delta done gz i gv al,
       gvar_init gv = nil ->
       gvar_volatile gv = false ->
  ENTAIL Delta,
       globvars_in_process gz done emp ((i,gv)::al) ⊢
    globvars_in_process gz done emp  al.
Proof.
intros.
unfold globvars_in_process.
go_lowerx.
iIntros "($ & $ & ?)".
rewrite /globvars2pred /= /globvar2pred /=.
rewrite H0 H /= bi.emp_sep //.
Qed.

Lemma finish_process_globvars: 
 forall E Delta PQR SF c Post,
  semax E Delta (PQR ∗ SF) c Post ->
  semax E Delta ((PQR ∗ emp) ∗ SF) c Post.
Proof.
intros.
rewrite bi.sep_emp //.
Qed.

Definition is_array_type t :=
 match t with Tarray _ _ _ => true | _ => false end.

End mpred.

Ltac process_one_globvar' :=
 first
  [ simple eapply process_globvar_extern; [reflexivity | reflexivity ]
  | match goal with |- ENTAIL ?Delta, globvars_in_process ?gv _ emp ((?i,?v)::_) ⊢ _ =>
        (* need this hack because, for some reason, simple eapply does not work here *)
           unify (is_array_type (gvar_info v)) true
     end;
    (* simple *) eapply process_globvar_ptrarray_space;
     [  reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
     | compute; clear; congruence
     ]
  | simple eapply process_globvar_space0;
    [simpl; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | simpl; computable ]
  | simple eapply process_globvar';
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence ]
  | match goal with |- ENTAIL ?Delta, globvars_in_process ?gv _ emp ((?i,?v)::_) ⊢ _ =>
        (* need this hack because, for some reason, simple eapply does not work here *)
           unify (is_array_type (gvar_info v)) true
     end;
     (*simple*) eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence  ]
  | match goal with |- ENTAIL ?Delta, globvars_in_process ?gv _ emp ((?i,?v)::_) ⊢ _ =>
        (* need this hack because, for some reason, simple eapply does not work here *)
           unify (is_array_type (gvar_info v)) true
     end;
      eapply process_globvar_array_float;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence  ]
  | simple eapply process_globvar_star';
        [reflexivity | reflexivity | reflexivity ]
  | simple eapply halfprocess_globvar_star;
        [reflexivity | reflexivity | reflexivity | reflexivity|
         simpl; compute; split; clear; congruence ]
  ].
Ltac process_one_globvar :=
  eapply ENTAIL_trans; [process_one_globvar' | simpl float_constructor].

Lemma move_globfield_into_done:
 forall `{!heapGS Σ} Delta gv done S1 R al R',
  ENTAIL Delta, globvars_in_process gv (S1::done) R al ⊢ R' ->
  ENTAIL Delta, globvars_in_process gv done (S1 ∗ R) al ⊢ R'.
Proof.
intros.
rewrite -H.
apply bi.and_mono; first done.
unfold globvars_in_process; simpl.
iIntros "($ & $ & ($ & $) & $)".
Qed.

(*
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

Lemma move_globfield_into_SEP0:
 forall {cs: compspecs}{Espec: OracleKind} Delta
   (S0 S3 S4: environ -> mpred) c Post,
 semax Delta (S0 * S3 * S4) c Post ->
 semax Delta (S0 * emp * S3 * S4) c Post.
Proof.
intros.
rewrite bi.sep_emp; auto.
Qed.

*)

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
     lazymatch goal with Delta := @abbreviate tycontext _ 
                             |- ENTAIL _, globvars_in_process _ _ ?A _ ⊢ _ =>
      match A with id2pred_star _ _ _ (_ ?i) _ =>
         let p := fresh "p" in set (p:=A);
         simpl in p;
         unfold id2pred_star, init_data2pred' in p;
         simpl PTree.get in p; simpl zeq in p;
         cbv beta iota zeta in p;
         simpl init_data_size in p;
         revert p; rewrite ?offset_offset_val; intro p; simpl Z.add in p;
         let t := constr:(match (glob_types Delta) !! i with Some x => x | _ => Tvoid end) in
         let t := eval hnf in t in
         match t with Tpointer ?t2 _ =>
           repeat match goal with p := ?D |- _ =>
                       match D with context [mapsto ?sh ?t' ?q ?v] =>
                            revert p;
                           change (mapsto sh t' q v) with (mapsto sh size_t q nullval);
                           rewrite <- (mapsto_tuint_tptr_nullval sh q t2);
                           intro p
                       end end
         | _ => idtac end;
         try change (mapsto ?sh _ (?gv i) ?v) with (mapsto sh t (gv i) v) in p;
         subst p;
         repeat simple apply move_globfield_into_done
      | _ => idtac
       end
    | |- ENTAIL _, _ ⊢ _ => idtac
    end.

Create HintDb zero_val discriminated.

Lemma zero_val_tarray {cs: compspecs}:
 forall t n, zero_val (tarray t n) = Zrepeat (zero_val t) n.
Proof.
intros.
rewrite zero_val_eq; reflexivity.
Qed.

Lemma zero_val_tint {cs: compspecs}:
    zero_val tint = Vint Int.zero.
Proof.
intros.
apply zero_val_Tint.
Qed.

Lemma zero_val_tuint {cs: compspecs}:
    zero_val tuint = Vint Int.zero.
Proof.
intros.
apply zero_val_Tint.
Qed.

Lemma zero_val_tlong {cs: compspecs}:
    zero_val tlong = Vlong Int64.zero.
Proof.
intros.
apply zero_val_Tlong.
Qed.

Lemma zero_val_tulong {cs: compspecs}:
    zero_val tulong = Vlong Int64.zero.
Proof.
intros.
apply zero_val_Tlong.
Qed.

Lemma zero_val_tptr {cs: compspecs}:
    forall t, zero_val (tptr t) = nullval.
Proof.
intros.
apply zero_val_Tpointer.
Qed.

#[export] Hint Rewrite @zero_val_tarray : zero_val.
#[export] Hint Rewrite @zero_val_Tpointer @zero_val_Tfloat32 @zero_val_Tfloat64 : zero_val.
#[export] Hint Rewrite @zero_val_Tlong @zero_val_Tint : zero_val.
#[export] Hint Rewrite @zero_val_tint @zero_val_tuint @zero_val_tlong @zero_val_tulong @zero_val_tptr : zero_val.

Lemma prog_defs_Clight_mkprogram:
 forall c g p m w,
 prog_defs (Clightdefs.mkprogram c g p m w) = g.
Proof.
intros. unfold Clightdefs.mkprogram.
destruct (build_composite_env' c w).
reflexivity.
Qed.

Ltac process_globals :=
  repeat process_idstar; 
  change (Share.lub extern_retainer _) with Ews;
  change (Share.lub extern_retainer _) with Ers;
  try change (Basics.compose Vint _) with (Basics.compose Vint id);
  fold_types;
  rewrite ?Combinators.compose_id_right;
  apply ENTAIL_refl.

Ltac expand_main_pre_old :=
 match goal with | |- semax _ _ (main_pre_old ?prog _ _ ∗ _) _ _ =>
    rewrite main_pre_start_old;
    unfold prog_vars, prog
                          | |- semax _ _ (main_pre_old ?prog _ _) _ _ =>
    rewrite main_pre_start_old;
    unfold prog_vars, prog
 end;
rewrite prog_defs_Clight_mkprogram;
simpl globvars2pred;
simple eapply semax_process_globvars;
 [process_globals
 | tryif (simple apply finish_process_globvars) then idtac
    else idtac "Warning: could not process all the extern variables in main_pre"
 ];
 rewrite ?offset_val_unsigned_repr;
 simpl readonly2share;
 autorewrite with zero_val.
