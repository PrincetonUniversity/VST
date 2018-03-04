Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
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
  forall Delta i t gv idata rho,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
   gvar_volatile gv = false ->
   gvar_init gv = idata ->
   tc_environ Delta rho ->
   globvar2pred(i, gv) rho |-- init_data_list2pred idata (readonly2share (gvar_readonly gv)) (eval_var i t rho) rho.
Proof.
pose (H2:=True).
pose (H4:=True).
pose (H5:=True); intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b ?].
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
   globvar2pred(i, gv) rho |--
   (EX s:val, local (locald_denote (gvar i s)) && init_data_list2pred idata (readonly2share (gvar_readonly gv)) s) rho.
Proof.
pose (H2:=True).
pose (H4:=True).
pose (H5:=True); intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b ?].
rewrite H11. rewrite H1.
rewrite H3; simpl.
apply exp_right with (Vptr b Ptrofs.zero).
apply andp_right. apply prop_right. hnf; rewrite H11.
unfold Map.get. rewrite H10. auto.
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
     (Delta: tycontext)  (d: init_data)  (sh: share) (ty: type) (v: val) : environ -> mpred :=
 match d with
  | Init_int8 i => `(mapsto sh tuchar v (Vint (Int.zero_ext 8 i)))
  | Init_int16 i => `(mapsto sh tushort v (Vint (Int.zero_ext 16 i)))
  | Init_int32 i => `(mapsto sh tuint v (Vint i))
  | Init_int64 i => `(mapsto sh tulong v (Vlong i))
  | Init_float32 r =>  `(mapsto sh tfloat v (Vsingle r))
  | Init_float64 r =>  `(mapsto sh tdouble v (Vfloat r))
  | Init_space n => if zeq n (sizeof ty)
                                   then `(data_at_ sh ty v)
                                   else if zlt n 0 then TT
                                   else`(memory_block sh n v)
  | Init_addrof symb ofs =>
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Tarray t n' att) =>
         EX s:val, local (locald_denote (gvar symb s)) && `(mapsto sh (Tpointer t noattr) v (offset_val (Ptrofs.unsigned ofs) s))
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

Lemma unpack_globvar_aux1 {cs: compspecs}:
  forall sh t b v i_ofs,
  Ptrofs.unsigned i_ofs + sizeof (Tpointer t noattr) <= Ptrofs.max_unsigned ->
               mapsto sh (Tpointer t noattr) (Vptr b i_ofs) v
                   |-- memory_block sh 4 (Vptr b i_ofs).
Proof.
 intros.
 eapply derives_trans; [ apply mapsto_mapsto_ | ].
 rewrite (memory_block_mapsto_ _ (Tpointer t noattr)); auto.
 unfold size_compatible; unfold Ptrofs.max_unsigned in H; omega.
 admit. (* align_compatible can be FOUND inside mapsto *)
Admitted.

Search sizeof Tpointer.

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
  forall (Delta : tycontext) (t : type) (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs v,
  field_compatible t nil (Vptr b (Ptrofs.repr ofs)) ->
  (*legal_alignas_type t = true -> *)
  (*nested_legal_fieldlist t = true -> *) True ->
  (*nested_non_volatile_type t = true -> *) True ->
  0 <= ofs ->
  ofs + init_data_size idata <= Ptrofs.max_unsigned ->
  tc_environ Delta rho ->
  v = Vptr b (Ptrofs.repr 0) ->
  (alignof t | Ptrofs.unsigned (Ptrofs.repr ofs)) ->
  readable_share sh ->
   init_data2pred idata sh (offset_val ofs v) rho
    |-- init_data2pred' Delta idata sh t (offset_val ofs v) rho.
Proof.
intros until v.
intros H1 HH H1' H6' H6 H7 H8 H1'' RS.
 unfold init_data2pred', init_data2pred.
 rename H8 into H8'.
 assert (H8: offset_val ofs v = Vptr b (Ptrofs.repr ofs)).
 rewrite H8'; simpl. rewrite Ptrofs.add_zero_l; auto.
 clear H8'.
 simpl.
 destruct idata; super_unfold_lift; try apply derives_refl.
*  repeat if_tac; try rewrite H8.
   + subst z; rewrite init_data_size_space in H6.
     rewrite data_at__memory_block by (auto; unfold Ptrofs.max_unsigned in H6; omega).
     repeat apply andp_right.
     - apply prop_right. auto.
     - unfold Ptrofs.max_unsigned in H6.
       apply mapsto_zeros_memory_block; auto.
       1: pose proof (sizeof_pos t); omega.
       1: pose proof unsigned_repr_range ofs H6'; omega.
   + simpl; apply TT_right.
   + unfold init_data_size in H6. rewrite Z.max_l in H6 by omega.
     unfold Ptrofs.max_unsigned in H6.
     apply mapsto_zeros_memory_block; auto.
     - pose proof (sizeof_pos t); omega.
     - pose proof unsigned_repr_range ofs H6'; omega.
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
    (apply exp_right with (Vptr b' Ptrofs.zero); apply andp_right;
      [unfold local, lift1; apply prop_right; auto
      |      unfold offset_val; simpl; try rewrite Ptrofs.repr_unsigned, Ptrofs.add_zero_l; auto; try apply derives_refl]).

  unfold mapsto. simpl. rewrite !if_true by auto.
  rewrite andb_false_r. simpl.
  apply orp_right1.
  apply orp_left. auto.
  normalize. inv H0.
Qed.

Lemma readable_share_readonly2share:
 forall b, readable_share (readonly2share b).
Proof.
destruct b; simpl.
intro.
apply fst_split_glb_orthogonal in H.
rewrite Share.glb_idem in H.
contradiction juicy_mem.nonidentity_Rsh.
unfold readable_share.
rewrite Share.glb_idem.
apply juicy_mem.nonidentity_Rsh.
Qed.

Lemma unpack_globvar  {cs: compspecs}:
  forall Delta i t gv idata,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0 = true)%bool ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   init_data_size idata <= sizeof t ->
   sizeof t <= Ptrofs.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |--
       EX s: val, local (locald_denote (gvar i s)) &&
       init_data2pred' Delta idata (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) t s.
Proof.
intros.
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound'; try eassumption | ].
assert (RS: forall sh', readable_share (Share.lub sh' (readonly2share (gvar_readonly gv)))).
intros.
apply readable_share_lub. apply readable_share_readonly2share.
forget (readonly2share (gvar_readonly gv)) as sh.
autorewrite with subst norm1 norm2; normalize.
apply exp_right with x.
autorewrite with subst norm1 norm2; normalize.
unfold init_data_list2pred.
simpl.
rewrite sepcon_emp.
destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?].
assert (x = offset_val 0 x).
hnf in H8. destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
destruct (ge_of rho i); try contradiction. subst; reflexivity.
rewrite H10.
 unfold eval_var in H9.
 hnf in H8. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
 destruct (ge_of rho i); try contradiction.
 apply derives_trans with
    (init_data2pred' Delta idata (Share.lub extern_retainer sh) t
      (offset_val 0 x) rho).
+ rewrite andb_true_iff in H1; destruct H1.
  eapply init_data2pred_rejigger; eauto.
   - clear H10 H8 x. inv H9.
      split; simpl; auto.
       change Ptrofs.max_unsigned with (Ptrofs.modulus-1) in H6.
      split3; auto.
      omega. split; auto. apply la_env_cs_sound in H11; auto.
   - omega.
   - omega.
   - apply Z.divide_0_r.
 +
 unfold init_data2pred'.
 destruct idata; unfold_lift;
   try (rewrite H8; simpl; rewrite Ptrofs.add_zero_l; auto);
 try apply derives_refl.
Qed.

Fixpoint id2pred_star   {cs: compspecs}
   (Delta: tycontext) (sh: share) (t: type) (v: val) (ofs: Z) (dl: list init_data) : environ->mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta d sh t (offset_val ofs v)
                   * id2pred_star Delta sh t v (ofs + init_data_size d) dl'
 | nil => emp
 end.

Arguments id2pred_star cs Delta sh t v ofs dl rho  / .

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
  forall Delta i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)% bool = true ->
   gvar_volatile gv = false ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
      EX s:val, local (locald_denote (gvar i s)) && 
       id2pred_star Delta (Share.lub extern_retainer (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0 (gvar_init gv).
Proof.
assert (H5:=true).
intros until 4.
remember (gvar_info gv) as t eqn:H3; symmetry in H3.
remember (gvar_init gv) as idata eqn:H4; symmetry in H4.
intros.
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound'; eassumption | ].
normalize.
  autorewrite with subst norm1 norm2; normalize.
apply exp_right with x.  normalize.
  autorewrite with subst norm1 norm2; normalize.
assert (RS: forall sh', readable_share (Share.lub sh' (readonly2share (gvar_readonly gv)))).
 {intros. 
  apply readable_share_lub. apply readable_share_readonly2share.
}
forget (readonly2share (gvar_readonly gv)) as sh.
(*rename H8 into H20. *)
(* destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?]. *)
set (ofs:=0%Z).
assert (alignof t | Ptrofs.unsigned (Ptrofs.repr ofs)) by (subst ofs; simpl; apply Z.divide_0_r).
hnf in H8.  destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
assert (H10: x = offset_val ofs x) by (subst; reflexivity).
rewrite H10 at 1.
(*replace (eval_var i t rho) with (offset_val (Ptrofs.repr ofs) (eval_var i t rho))
    by (rewrite H8; reflexivity). *)
clear H10.
assert (H11: init_data_list_size idata + ofs <= sizeof t)  by (unfold ofs; omega).
assert (H12:  sizeof t <= Ptrofs.max_unsigned)  by omega.
assert (0 <= ofs) by (unfold ofs; omega).
clearbody ofs.
revert ofs H9 H10 H11 H12.
clear dependent gv. clear H H0 H6.
induction idata; simpl; auto; intros. apply derives_refl.
apply sepcon_derives.
* rewrite andb_true_iff in H1.
  eapply init_data2pred_rejigger; destruct H1; eauto; try tauto.
  split3; simpl; auto.
  change Ptrofs.max_unsigned with (Ptrofs.modulus-1) in H12.
  admit.
 pose proof (init_data_list_size_pos idata); omega.
* specialize (IHidata (ofs + init_data_size a)).
rewrite offset_offset_val.
 pose proof (init_data_list_size_pos idata).
pose proof (init_data_size_pos a).
 apply IHidata; try omega.
 rewrite Ptrofs.unsigned_repr by omega.
 rewrite Ptrofs.unsigned_repr in H9 by omega.
 apply Z.divide_add_r; auto.
 admit. (* alignment issue *)
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
   (!! ((align_compatible t) (eval_var i t rho))) && globvar2pred (i, gv) rho |-- 
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
 forall Delta sh n (v: val) (data: list int) sz sign mdata
  (NBS: notboolsize sz),
  n = Zlength mdata ->
  mdata = map (inttype2init_data sz) data ->
  !! isptr v && !! align_compatible (Tint sz sign noattr) v &&
  !! (offset_in_range (sizeof (Tint sz sign noattr) * n)) v &&
  id2pred_star Delta sh (tarray (Tint sz sign noattr) n) v 0 mdata |--
  `(data_at sh (tarray (Tint sz sign noattr) n)
           (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data) v).
Proof.
  intros. subst n mdata.
  replace (Zlength (map  (inttype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  set (ofs:=0%Z).
  unfold ofs at 1.
  go_lowerx.
  assert (offset_in_range (sizeof (Tint sz sign noattr) * ofs) v) by
    (unfold ofs, offset_in_range; destruct v; auto;
     pose proof Ptrofs.unsigned_range i; omega).
  change 0 with (ofs* sizeof (Tint sz sign noattr))%Z.
  set (N := Zlength data). unfold N at 2. clearbody N.
  replace (Zlength data) with (ofs + Zlength data) in * by (unfold ofs; omega).
Admitted.
(*
  replace (map (Basics.compose Vint (cast_int_int sz sign)) data)
    with (skipn (Z.to_nat ofs) (map (Basics.compose Vint (cast_int_int sz sign)) data))
    by (unfold ofs; reflexivity).

  clearbody ofs.
  rename H into H'.

revert ofs H1 H2;
induction data; intros; simpl; auto.
Focus 1. {
  rewrite Zlength_nil. unfold data_at; simpl.
  unfold array_at', rangespec; simpl.
  replace (ofs+0-ofs) with 0 by omega. simpl. normalize.
} Unfocus.
rewrite Zlength_cons.
set (w := match sz with
             | I8 => 1
             | I16 => 2
             | I32 => 4
             | IBool => 1
             end) in *.
replace (sizeof (Tint sz sign noattr)) with w in * by (destruct sz; reflexivity).
replace (align w w) with w in * by (unfold w; destruct sz; reflexivity).
replace (init_data_size (inttype2init_data sz a))
  with w by (destruct sz; reflexivity).
replace (ofs*w+w) with ((Z.succ ofs) * w)%Z
 by (destruct sz; unfold Z.succ; rewrite Z.mul_add_distr_r; reflexivity).

replace (ofs + Z.succ (Zlength data)) with (Z.succ ofs + Zlength data) by omega.
rewrite (split3_array_at ofs).
rewrite array_at_emp.
rewrite prop_true_andp by auto. normalize. (* rewrite emp_sepcon. *)
apply sepcon_derives; auto.
+ unfold_lift.
  apply derives_trans with
    (`(mapsto sh (Tint sz sign noattr))
     (fun x : environ => offset_val (Ptrofs.repr (ofs * w)) (v x))
     `(Vint (cast_int_int sz sign a)) rho).
  - apply derives_refl'.
    destruct sz; simpl; unfold_lift; auto.
    destruct sign; simpl; auto.
    apply (mapsto_unsigned_signed Unsigned Signed sh I8).
    destruct sign; simpl; auto.
    apply (mapsto_unsigned_signed Unsigned Signed sh I16).
    contradiction.
  - simpl_data_at; fold w.
 (*   replace ((w-1)/w*w)%Z with 0%Z by (destruct sz; reflexivity).
    simpl. *)
    unfold_lift.
    rewrite mapsto_isptr.
    apply derives_extract_prop. intro.
    destruct (v rho); inv H.
    simpl offset_val.
    unfold add_ptr_int; simpl.
    fold w.
    rewrite mul_repr.
    unfold ZnthV.
    (* replace (align w w) with w by (destruct sz; reflexivity). *)
    rewrite Zmult_comm.
    rewrite if_false by omega.
    rewrite Z.sub_diag. simpl nth.
    apply andp_right; [|auto].
    admit. (* align_compatible and size_compatible, should be provable *)
+ auto.
  eapply derives_trans; [ apply IHdata | ].
  - rewrite Zlength_cons in H1.
    Z_and_int.
    replace (ofs + 1 + Zlength data) with (ofs + (Zlength data + 1)) by omega.
    exact H1.
  - replace w with (sizeof (Tint sz sign noattr)) in * by (destruct sz; reflexivity).
    eapply offset_in_range_mid; [| exact H2 | exact H1].
    rewrite Zlength_cons.
    Z_and_int.
    pose proof (initial_world.zlength_nonneg _ data).
    omega.
  - apply derives_refl'.
    apply equal_f. apply array_at_ext.
    intros. unfold ZnthV. if_tac. rewrite if_true by omega. auto.
    rewrite if_false by omega.
    assert (Z.to_nat (i-ofs) = S (Z.to_nat (i - Z.succ ofs))).
    apply Nat2Z.inj. rewrite inj_S. rewrite Z2Nat.id by omega.
    rewrite Z2Nat.id by omega. omega.
    rewrite H4. simpl. auto.
+ rewrite Zlength_correct; clear; omega.
Qed.
*)

Lemma id2pred_star_ZnthV_tint  {cs: compspecs}:
 forall Delta sh n (v: val) (data: list int) mdata,
  n = Zlength mdata ->
  mdata = map Init_int32 data ->
  !! isptr v && !! align_compatible tint v &&
  !! offset_in_range (sizeof tint * n) v &&
  id2pred_star Delta sh (tarray tint n) v 0 mdata |--
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

Lemma unpack_globvar_array  {cs: compspecs}:
  forall t sz sign (data: list int)  n Delta i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   t = Tint sz sign noattr ->
  forall    (NBS: notboolsize sz),
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (inttype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Ptrofs.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |--
   EX s:val, local (locald_denote (gvar i s)) &&
      `(data_at (Share.lub extern_retainer (readonly2share (gvar_readonly gv)))
         (tarray (Tint sz sign noattr) n)
         (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)
         s).
Proof.
  intros. subst t.
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (tc_environ Delta)))
  end.
  2: solve [apply andp_left1; cancel].
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (`isptr (eval_var i (tarray (Tint sz sign noattr) n)))))
  end.
  Focus 2. {
    go_lowerx. apply prop_right. eapply eval_var_isptr; eauto.
    right; split; auto. rewrite <- H1; auto.
   } Unfocus.
  eapply derives_trans;[ apply andp_derives; [ apply andp_derives; [ eapply unpack_globvar_star; try eassumption; try reflexivity | apply derives_refl]  | apply derives_refl] |].
* rewrite andb_true_iff.
  split; rewrite H1.
  reflexivity.
  admit.
*
  rewrite H1. (* rewrite H3.*)  rewrite H5.
  normalize. apply exp_right with s.
  apply andp_right. repeat apply andp_left1; auto.
  eapply derives_trans; [| apply (id2pred_star_ZnthV_Tint Delta); auto].
 2: rewrite <- H5; auto.
Opaque sizeof.
  go_lowerx.
Transparent sizeof.
  normalize.
 rename H8 into H19.
  destruct (globvar_eval_var Delta rho _ _ H7 H H0) as [? [? ?]].
  rewrite H1 in H8.
  assert (align_compatible (Tint sz sign noattr) (eval_var i (tarray (Tint sz sign noattr) n) rho)). {
    rewrite H8.
    unfold align_compatible.
    simpl.
    admit.
  } 
  assert (offset_in_range (sizeof (Tint sz sign noattr) * n)
           (eval_var i (tarray (Tint sz sign noattr) n) rho)). {
    rewrite H8.
    unfold offset_in_range; simpl.
    rewrite H1 in H6; simpl in H6.
    pose proof initial_world.zlength_nonneg _ (gvar_init gv).
    rewrite Z.max_r in H6 by omega.
    unfold Ptrofs.max_unsigned in H6.
    pose proof init_data_list_size_pos (gvar_init gv).
    omega.
  }
  apply andp_right; auto.
  apply prop_right.
  hnf in H3;
  destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
  destruct ((ge_of rho) i); try contradiction.
  subst s.
  rewrite H8 in *.
  split3; auto.
Admitted.

Lemma process_globvar:
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gv gvs SF c Post (idata : init_data) t,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_info gv = t ->
       gvar_init gv = (idata::nil) ->
       init_data_size idata <= sizeof t ->
       sizeof t <= Ptrofs.max_unsigned ->
 (forall v: val,
   semax Delta (PROPx P (LOCALx (gvar i v :: Q) (SEPx R))
                       * (init_data2pred' Delta idata 
                         (Share.lub  extern_retainer (readonly2share (gvar_readonly gv)))
                         t v * globvars2pred gvs) * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R))
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre.
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q)
          (SEPx R)) * (init_data2pred' Delta idata
             (Share.lub extern_retainer
                (readonly2share (gvar_readonly gv))) t s 
                *fold_right sepcon emp (map globvar2pred gvs)) * SF).
unfold globvars2pred.
change  (fold_right sepcon emp (map globvar2pred ((i, gv) :: gvs)))
 with (globvar2pred (i,gv) * fold_right sepcon emp (map globvar2pred gvs)).
rewrite <- (sepcon_comm SF).
 rewrite <- sepcon_assoc.
rewrite <- (sepcon_comm (fold_right _ _ _)).
 rewrite <- !sepcon_assoc.
rewrite <- local_sepcon_assoc2.
eapply derives_trans.
apply sepcon_derives; [apply derives_refl | ].
eapply unpack_globvar; try eassumption.
normalize.
apply exp_right with s.
rewrite <- (sepcon_comm SF).
rewrite ! sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- insert_local.
rewrite ! local_sepcon_assoc2.
rewrite ! local_sepcon_assoc1.
apply andp_derives; auto.
apply sepcon_derives; auto.
rewrite sepcon_comm; auto.
apply extract_exists_pre.
apply H7.
Qed.

Lemma process_globvar':
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gv gvs SF c Post (idata : init_data) t,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some t ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       gvar_info gv = t ->
       gvar_init gv = (idata::nil) ->
       init_data_size idata <= sizeof t ->
       sizeof t <= Ptrofs.max_unsigned ->
 (forall v: val,
   semax Delta (PROPx P (LOCALx (gvar i v :: Q) (SEPx R))
                       * id2pred_star Delta
                         (Share.lub  extern_retainer (readonly2share (gvar_readonly gv)))
                         t v 0 (idata ::nil) * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R))
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre.
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q)
          (SEPx R)) * id2pred_star Delta
                         (Share.lub  extern_retainer (readonly2share (gvar_readonly gv)))
                         t s 0 (idata ::nil)
                *fold_right sepcon emp (map globvar2pred gvs) * SF).
unfold globvars2pred.
change  (fold_right sepcon emp (map globvar2pred ((i, gv) :: gvs)))
 with (globvar2pred (i,gv) * fold_right sepcon emp (map globvar2pred gvs)).
rewrite <- (sepcon_comm SF).
 rewrite <- sepcon_assoc.
rewrite <- (sepcon_comm (fold_right _ _ _)).
 rewrite <- !sepcon_assoc.
rewrite <- local_sepcon_assoc2.
eapply derives_trans.
apply sepcon_derives; [apply derives_refl | ].
eapply unpack_globvar; try eassumption.
normalize.
apply exp_right with s.
unfold id2pred_star.
rewrite <- (sepcon_comm SF).
rewrite ! sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- insert_local.
rewrite ! local_sepcon_assoc2.
rewrite ! local_sepcon_assoc1.
match goal with |- ?A |-- ?B => apply derives_trans with  (!!isptr s && A) end.
apply andp_right; auto.
apply andp_left1; auto.
intro rho. simpl. apply prop_derives.
unfold gvar_denote. intro; destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction. subst; apply I.
apply derives_extract_prop; intro.
rewrite isptr_offset_val_zero; auto.
clear H8.
apply andp_derives; auto.
rewrite emp_sepcon.
apply sepcon_derives; auto.
rewrite sepcon_comm; auto.
apply extract_exists_pre.
apply H7.
Qed.

Lemma process_globvar_array:
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
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
 (forall v: val,
   semax Delta (PROPx P (LOCALx (gvar i v :: Q)
                      (SEPx ((data_at
                   (Share.lub extern_retainer (readonly2share (gvar_readonly gv)))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo Cop.cast_int_int sz sign) data) v)
                    :: R)))
                       * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R))
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre.
instantiate (1 := EX  v : val,
           PROPx P (LOCALx (gvar i v :: Q)
          (SEPx ((data_at
                   (Share.lub extern_retainer (readonly2share (gvar_readonly gv)))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo Cop.cast_int_int sz sign) data) v) :: R))) * fold_right sepcon emp (map globvar2pred gvs) * SF).
unfold globvars2pred.
change  (fold_right sepcon emp (map globvar2pred ((i, gv) :: gvs)))
 with (globvar2pred (i,gv) * fold_right sepcon emp (map globvar2pred gvs)).
rewrite <- (sepcon_comm SF).
 rewrite <- sepcon_assoc.
rewrite <- (sepcon_comm (fold_right _ _ _)).
 rewrite <- !sepcon_assoc.
rewrite <- local_sepcon_assoc2.
eapply derives_trans.
apply sepcon_derives; [apply derives_refl | ].
eapply unpack_globvar_array; try eassumption.
normalize.
apply exp_right with s.
rewrite <- (sepcon_comm SF).
rewrite ! sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- insert_local.
rewrite <- insert_SEP.
rewrite ! local_sepcon_assoc2.
rewrite ! local_sepcon_assoc1.
apply andp_derives; auto.
pull_left (PROPx P (LOCALx Q (SEPx R))).
rewrite ! sepcon_assoc.
apply sepcon_derives; auto.
rewrite sepcon_comm; auto.
apply extract_exists_pre.
assumption.
Qed.

Lemma process_globvar_star':
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gv gvs SF c Post,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
 (forall s: val,
   semax Delta (PROPx P (LOCALx (gvar i s :: Q)
                      (SEPx R))
                  * (id2pred_star Delta
                          (Share.lub extern_retainer
                               (readonly2share (gvar_readonly gv)))
                       (gvar_info gv) s 0 (gvar_init gv))
             * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R))
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre.
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q)
          (SEPx R))
    * id2pred_star Delta
             (Share.lub extern_retainer
                (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0
             (gvar_init gv)
     * fold_right sepcon emp (map globvar2pred gvs) * SF).
unfold globvars2pred.
change  (fold_right sepcon emp (map globvar2pred ((i, gv) :: gvs)))
 with (globvar2pred (i,gv) * fold_right sepcon emp (map globvar2pred gvs)).
rewrite <- (sepcon_comm SF).
 rewrite <- sepcon_assoc.
rewrite <- (sepcon_comm (fold_right _ _ _)).
 rewrite <- !sepcon_assoc.
rewrite <- local_sepcon_assoc2.
eapply derives_trans.
apply sepcon_derives; [apply derives_refl | ].
eapply unpack_globvar_star; try eassumption.
normalize.
apply exp_right with s.
rewrite <- (sepcon_comm SF).
rewrite ! sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- insert_local.
rewrite ! local_sepcon_assoc2.
rewrite ! local_sepcon_assoc1.
apply andp_derives; auto.
apply sepcon_derives; auto.
rewrite sepcon_comm; auto.
apply extract_exists_pre.
assumption.
Qed.

Lemma process_globvar_star:
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gv gvs SF c Post,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some (gvar_info gv) ->
  (complete_legal_cosu_type (gvar_info gv) && is_aligned cenv_cs ha_env_cs la_env_cs (gvar_info gv) 0)%bool = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <=
       Ptrofs.max_unsigned ->
 (forall s: val,
   semax Delta (PROPx P (LOCALx (gvar i s :: Q)
                      (SEPx R))
                       * (id2pred_star Delta
             (Share.lub extern_retainer
                (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0
             (gvar_init gv) *
                    globvars2pred gvs) * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R))
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre.
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q)
          (SEPx R)) * ((id2pred_star Delta
             (Share.lub extern_retainer
                (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0
             (gvar_init gv)) * fold_right sepcon emp (map globvar2pred gvs)) * SF).
unfold globvars2pred.
change  (fold_right sepcon emp (map globvar2pred ((i, gv) :: gvs)))
 with (globvar2pred (i,gv) * fold_right sepcon emp (map globvar2pred gvs)).
rewrite <- local_sepcon_assoc1.
rewrite <- sepcon_assoc.
pull_left (globvar2pred (i, gv)).
rewrite <- local_sepcon_assoc1.
rewrite <- local_sepcon_assoc1.
rewrite !sepcon_assoc.
eapply derives_trans; [ apply sepcon_derives; [ | apply derives_refl] | ].
eapply unpack_globvar_star; try eassumption.
Intros s. Exists s.
rewrite <- insert_local.
rewrite ! local_sepcon_assoc1.
apply andp_derives; auto.
rewrite <- sepcon_assoc.
pull_left (PROPx P (LOCALx Q (SEPx R))).
rewrite ! sepcon_assoc.
apply derives_refl.
apply extract_exists_pre.
assumption.
Qed.

Lemma map_instantiate:
  forall {A B} (f: A -> B) (x: A) (y: list B) z,
    y = map f z ->  f x :: y = map f (x :: z).
Proof. intros. subst. reflexivity. Qed.

Lemma main_pre_eq:
 forall prog u v, main_pre prog u v =
  fold_right_sepcon' (map globvar2pred (prog_vars prog)).
Proof.
intros. rewrite fold_right_sepcon'_eq; reflexivity.
Qed.

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
 forall prog u v,
   main_pre prog u v = (PROP() LOCAL() SEP())%assert * globvars2pred (prog_vars prog).
Proof.
intros.
unfold main_pre, prog_vars, prog_vars', PROPx, LOCALx, SEPx.
normalize.
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
Admitted.

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
  | |- semax _ (_ * globvars2pred ((?i,_)::_) * _) _ _ =>
    match goal with
    | n: name i |- _ => idtac
    | |- _ => let n := fresh "v" i in assert (n: name i) by apply Logic.I
    end;
    match goal with
    | n: name i |- _ => process_one_globvar; clear n; intro n;
     match goal with |- semax _ (_ * ?A * _ * _) _ _ =>
         let p := fresh "p" in set (p:=A);
         simpl in p;
         unfold id2pred_star, init_data2pred' in p;
         simpl PTree.get in p; simpl zeq in p;
         cbv beta iota zeta in p;
         simpl init_data_size in p; simpl Z.add in p;
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
   end
 end.

Ltac expand_main_pre :=
 rewrite main_pre_start;
 unfold prog_vars, prog_vars'; simpl globvars2pred;
 repeat  process_idstar;
 change (globvars2pred nil) with (@emp (environ->mpred) _ _);
 rewrite (sepcon_emp (PROPx _ _));
 rewrite ?offset_val_unsigned_repr.
