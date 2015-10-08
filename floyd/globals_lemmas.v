Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.closed_lemmas.
Require Import floyd.nested_pred_lemmas.
(*Require Import floyd.unfold_data_at.*)
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

Lemma unsigned_repr_range: forall i, 0 <= i -> 0 <= Int.unsigned (Int.repr i) <= i.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  pose proof Z.mod_le i Int.modulus H.
  spec H0; [change Int.modulus with 4294967296; omega |].
  pose proof Z.mod_bound_pos i Int.modulus H.
  spec H1; [change Int.modulus with 4294967296; omega |].
  omega.
Qed.

Lemma mapsto_zeros_memory_block: forall sh n b ofs,
  0 <= n < Int.modulus ->
  Int.unsigned ofs+n <= Int.modulus ->
  readable_share sh ->
  mapsto_zeros n sh (Vptr b ofs) |--
  memory_block sh n (Vptr b ofs).
Proof.
  unfold mapsto_zeros.
  intros.
  rename H0 into H'. rename H1 into RS.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  repeat rewrite Int.unsigned_repr by omega.
  apply andp_right.
  + apply prop_right; auto.
  + rewrite <- (Z2Nat.id n) in H' by omega.
    rewrite <- (Z2Nat.id n) in H by omega.
    change nat_of_Z with Z.to_nat.
    forget (Z.to_nat n) as n'.
    clear n.
    remember (Int.unsigned ofs) as ofs'.
    assert (Int.unsigned (Int.repr ofs') = ofs')
      by (subst; rewrite Int.repr_unsigned; reflexivity).
    assert (0 <= ofs' /\ ofs' + Z.of_nat n' <= Int.modulus).
    Focus 1. {
      pose proof Int.unsigned_range ofs.
      omega.
    } Unfocus.
    clear Heqofs' H'.
    assert (Int.unsigned (Int.repr ofs') = ofs' \/ n' = 0%nat) by tauto.
    clear H0; rename H2 into H0.
    revert ofs' H H1 H0; induction n'; intros.
    - simpl; auto.
    - destruct H1.
      rewrite inj_S in H2. unfold Z.succ in H2.
      apply sepcon_derives; auto.
      * unfold mapsto_, mapsto. simpl.
        rewrite if_true by auto.
        apply orp_right2.
        rewrite prop_true_andp by auto.
        apply exp_right with (Vint Int.zero).
        destruct H0; [| omega].
        rewrite H0.
        auto.
      * fold address_mapsto_zeros. fold memory_block'.
        apply IHn'. omega. omega.
        destruct (zlt (ofs' + 1) Int.modulus).
        1: rewrite Int.unsigned_repr; [left; reflexivity | unfold Int.max_unsigned; omega].
        1: right.
           destruct H0; [| inversion H0].
           omega.
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
destruct (H8 _ _ H0) as [b [? ?]].
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
   (EX s:val, local (gvar i s) && init_data_list2pred idata (readonly2share (gvar_readonly gv)) s) rho.
Proof.
pose (H2:=True).
pose (H4:=True).
pose (H5:=True); intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b [? ?]].
rewrite H11. rewrite H1.
rewrite H3; simpl.
apply exp_right with (Vptr b Int.zero).
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
| Some b => Vptr b Int.zero
| None => Vundef
end.

Lemma eval_sgvar_lemma1:
  forall (F: val -> mpred) ofs id t,
    F Vundef |-- FF ->
   `F (`(offset_val ofs) (eval_sgvar id t)) =
   (EX v:val, local (sgvar id v) && `(F (offset_val ofs v))).
Proof.
intros.
extensionality rho.
unfold_lift. unfold local, lift1.
unfold sgvar, eval_sgvar.
unfold Map.get. simpl.
apply pred_ext.
destruct (ge_of rho id).
apply exp_right with (Vptr b Int.zero).
normalize.
eapply derives_trans; [ apply H | ].
apply FF_left.
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
  | Init_space n => if zeq n (sizeof cenv_cs ty)
                                   then `(data_at_ sh ty v)
                                   else if zlt n 0 then TT
                                   else`(memory_block sh n v)
  | Init_addrof symb ofs => 
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Tarray t n' att) =>
         EX s:val, local (sgvar symb s) && `(mapsto sh (Tpointer t noattr) v (offset_val ofs s))
      | None, Some Tvoid => TT
(*
      | None, Some t => `(mapsto sh (Tpointer t noattr) v) (`(offset_val ofs) (eval_sgvar symb t))
*)
      | None, Some t => EX s:val, local (sgvar symb s) && `((mapsto sh (Tpointer t noattr) v) (offset_val ofs s))
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
  Int.unsigned i_ofs + sizeof cenv_cs (Tpointer t noattr) <= Int.max_unsigned ->
               mapsto sh (Tpointer t noattr) (Vptr b i_ofs) v
                   |-- memory_block sh 4 (Vptr b i_ofs).
Proof.
 intros.
 eapply derives_trans; [ apply mapsto_mapsto_ | ].
 rewrite (memory_block_mapsto_ _ (Tpointer t noattr)); auto.
 unfold size_compatible; unfold Int.max_unsigned in H; omega.
 admit. (* align_compatible can be FOUND inside mapsto *)
Qed.

Lemma sizeof_Tpointer {cs: compspecs} : forall t, sizeof cenv_cs (Tpointer t noattr) = 4.
Proof.
intros. reflexivity.
Qed.

Lemma init_data_size_space {cs: compspecs}:
 forall t, init_data_size (Init_space (sizeof cenv_cs t)) = sizeof cenv_cs t.
Proof. intros.
 pose proof (sizeof_pos cenv_cs t).
 unfold init_data_size. rewrite Z.max_l; auto. omega.
Qed.

Lemma mapsto_pointer_void:
  forall sh t a, mapsto sh (Tpointer t a) = mapsto sh (Tpointer Tvoid a).
Proof.
intros.
unfold mapsto.
extensionality v1 v2.
simpl. auto.
Qed.

Lemma init_data2pred_rejigger {cs: compspecs}:
  forall (Delta : tycontext) (t : type) (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs v,
  field_compatible t nil (Vptr b (Int.repr ofs)) ->
  (*legal_alignas_type t = true -> *) 
  (*nested_legal_fieldlist t = true -> *) True ->
  (*nested_non_volatile_type t = true -> *) True ->
  0 <= ofs ->
  ofs + init_data_size idata <= Int.max_unsigned ->
  tc_environ Delta rho ->
  v = Vptr b (Int.repr 0) ->
  (alignof cenv_cs t | Int.unsigned (Int.repr ofs)) ->
  readable_share sh ->
   init_data2pred idata sh (offset_val (Int.repr ofs) v) rho 
    |-- init_data2pred' Delta idata sh t (offset_val (Int.repr ofs) v) rho.
Proof.
intros until v.
intros H1 HH H1' H6' H6 H7 H8 H1'' RS.
 unfold init_data2pred', init_data2pred.
 rename H8 into H8'.
 assert (H8: offset_val (Int.repr ofs) v = Vptr b (Int.repr ofs)).
 rewrite H8'; simpl. rewrite Int.add_zero_l; auto.
 clear H8'.
 simpl.
 destruct idata; super_unfold_lift; try apply derives_refl.
*  repeat if_tac; try rewrite H8. 
   + subst z; rewrite init_data_size_space in H6.
     rewrite data_at__memory_block by (auto; unfold Int.max_unsigned in H6; omega).
     repeat apply andp_right.
     - apply prop_right. auto.
     - unfold Int.max_unsigned in H6.
       apply mapsto_zeros_memory_block; auto.
       1: pose proof (sizeof_pos cenv_cs t); omega.
       1: pose proof unsigned_repr_range ofs H6'; omega.
   + simpl; apply TT_right.
   + unfold init_data_size in H6. rewrite Z.max_l in H6 by omega.
     unfold Int.max_unsigned in H6.
     apply mapsto_zeros_memory_block; auto.
     - pose proof (sizeof_pos cenv_cs t); omega.
     - pose proof unsigned_repr_range ofs H6'; omega.
*  destruct ((var_types Delta) ! i) eqn:Hv;
   destruct ((glob_types Delta) ! i) eqn:Hg; 
    try destruct g; try solve [simpl; apply TT_right].
 +   destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' [H15 H16]]; rewrite H15.
     simpl.
     rewrite H8.
     eapply derives_trans.     
     apply unpack_globvar_aux1.
     pose proof unsigned_repr_le ofs.
     rewrite sizeof_Tpointer; simpl in H6; omega.
    destruct t1; try (apply prop_right; auto).
    destruct t1; try (apply prop_right; auto).
    auto.
    auto.
 +
   destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' [H15 H16]]; rewrite H15.
   assert (sgvar i (Vptr b' Int.zero) rho)
     by (unfold sgvar; rewrite H15; auto).
(*
    assert (eval_sgvar i t0 rho = Vptr b' Int.zero).
    {unfold eval_sgvar, Map.get. rewrite H15. auto.
    }
*)
    destruct t0; simpl; try apply TT_right; try rewrite H8; try rewrite H;
    (apply exp_right with (Vptr b' Int.zero); apply andp_right;
      [unfold local, lift1; apply prop_right; auto 
      |      unfold offset_val; simpl; try rewrite Int.add_zero_l; auto]).
Qed.

Lemma unpack_globvar  {cs: compspecs}:
  forall Delta i t gv idata, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
  (legal_alignas_type (gvar_info gv) = true /\
   legal_cosu_type (gvar_info gv) = true /\
   complete_type cenv_cs (gvar_info gv) = true) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   init_data_size idata <= sizeof cenv_cs t ->
   sizeof cenv_cs t <= Int.max_unsigned ->  
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
       EX s: val, local (gvar i s) &&
       init_data2pred' Delta idata (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) t s.
Proof.
intros.
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound'; try eassumption | ].
assert (RS: forall sh', readable_share (Share.splice sh' (readonly2share (gvar_readonly gv)))).
intros.
apply right_nonempty_readable.
unfold readonly2share.
if_tac; auto.
apply Lsh_nonidentity.
forget (readonly2share (gvar_readonly gv)) as sh.
normalize. 
  autorewrite with subst norm1 norm2; normalize.
apply exp_right with x. normalize.
  autorewrite with subst norm1 norm2; normalize.
unfold init_data_list2pred.
simpl.
rewrite sepcon_emp.
destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?].
assert (x = offset_val Int.zero x).
hnf in H8. destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
destruct (ge_of rho i); try contradiction. subst; reflexivity.
rewrite H10.
 unfold eval_var in H9.
 hnf in H8. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
 destruct (ge_of rho i); try contradiction. 
 apply derives_trans with
    (init_data2pred' Delta idata (Share.splice extern_retainer sh) t
      (offset_val (Int.repr 0) x) rho).
 + eapply init_data2pred_rejigger; destruct H1; eauto.
   - clear H10 H8 x. inv H9.
      split; simpl; auto.
       change Int.max_unsigned with (Int.modulus-1) in H6.
       destruct H11.
      split3; auto. split3; auto.
      omega. split3; auto. omega. apply Z.divide_0_r.
   - omega.
   - omega.
   - apply Z.divide_0_r.
 + 
 unfold init_data2pred'.
 destruct idata; unfold_lift;
   try (rewrite H8; simpl; rewrite Int.add_zero_l; auto);
 try apply derives_refl.
Qed.

Fixpoint id2pred_star   {cs: compspecs}
   (Delta: tycontext) (sh: share) (t: type) (v: val) (ofs: Z) (dl: list init_data) : environ->mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta d sh t (offset_val (Int.repr ofs) v)
                   * id2pred_star Delta sh t v (ofs + init_data_size d) dl'
 | nil => emp
 end.

Arguments id2pred_star cs Delta sh t v ofs dl rho  / .

Lemma init_data_size_pos : forall a, init_data_size a >= 0.
Proof. 
 destruct a; simpl; try omega.
 pose proof (Zmax_spec z 0).
 destruct (zlt 0 z); omega.
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
  (legal_alignas_type (gvar_info gv) = true /\
   legal_cosu_type (gvar_info gv) = true /\
   complete_type cenv_cs (gvar_info gv) = true) ->
   gvar_volatile gv = false ->
   init_data_list_size (gvar_init gv) <= sizeof cenv_cs (gvar_info gv) <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
      EX s:val, local (gvar i s) && 
       id2pred_star Delta (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0 (gvar_init gv).
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
assert (RS: forall sh', readable_share (Share.splice sh' (readonly2share (gvar_readonly gv)))).
 {intros. 
  apply right_nonempty_readable.
  unfold readonly2share.
  if_tac; auto.
  apply Lsh_nonidentity.
}
forget (readonly2share (gvar_readonly gv)) as sh.
(*rename H8 into H20. *)
(* destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?]. *)
set (ofs:=0%Z).
assert (alignof cenv_cs t | Int.unsigned (Int.repr ofs)) by (subst ofs; simpl; apply Z.divide_0_r).
hnf in H8.  destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
assert (H10: x = offset_val (Int.repr ofs) x) by (subst; reflexivity).
rewrite H10 at 1.
(*replace (eval_var i t rho) with (offset_val (Int.repr ofs) (eval_var i t rho))
    by (rewrite H8; reflexivity). *)
clear H10.
assert (H11: init_data_list_size idata + ofs <= sizeof cenv_cs t)  by (unfold ofs; omega).
assert (H12:  sizeof cenv_cs t <= Int.max_unsigned)  by omega.
assert (0 <= ofs) by (unfold ofs; omega).
clearbody ofs.
revert ofs H9 H10 H11 H12.
clear dependent gv. clear H H0 H6.
induction idata; simpl; auto; intros.
apply sepcon_derives.
* eapply init_data2pred_rejigger; destruct H1; eauto; try tauto.
  split3; simpl; auto. destruct H0; split3; auto.
  change Int.max_unsigned with (Int.modulus-1) in H12.
 split3; auto. omega.
  admit. 
 pose proof (init_data_list_size_pos idata); omega.
* specialize (IHidata (ofs + init_data_size a)).
rewrite offset_offset_val.
rewrite add_repr.
 pose proof (init_data_list_size_pos idata).
pose proof (init_data_size_pos a).
 apply IHidata; try omega.
 rewrite Int.unsigned_repr by omega.
 rewrite Int.unsigned_repr in H9 by omega.
 apply Z.divide_add_r; auto.
 admit. (* alignment issue *)
Qed.

Lemma tc_globalvar_sound_space {cs: compspecs} :
  forall Delta i t gv rho, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
  (legal_alignas_type (gvar_info gv) = true /\
   legal_cosu_type (gvar_info gv) = true /\
   complete_type cenv_cs (gvar_info gv) = true) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof cenv_cs t) :: nil ->
   sizeof cenv_cs t <= Int.max_unsigned ->
   tc_environ Delta rho ->
   (!! ((align_compatible t) (eval_var i t rho))) && globvar2pred (i, gv) rho |-- 
   data_at_ (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) t (eval_var i t rho).
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
unfold mapsto_zeros. rewrite sepcon_emp.
rewrite Int.unsigned_zero.
pose proof (mapsto_zeros_memory_block
  (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) (sizeof cenv_cs t) b Int.zero).
unfold mapsto_zeros in H9. change (Int.repr 0) with Int.zero in H9.
rewrite Int.unsigned_zero in H9.
apply andp_right.
+ normalize.
  apply prop_right. subst t.
  destruct Hno as [? [? ?]]. split3; simpl; auto.
  split3; auto.
  change Int.max_unsigned with (Int.modulus-1) in H5.
 split3. omega. omega. split; auto.
+ apply H9.
  pose (sizeof_pos cenv_cs t).
  - unfold Int.max_unsigned in H5. omega.
  - unfold Int.max_unsigned in H5. omega.
  - apply right_nonempty_readable.
     unfold readonly2share.
     if_tac; auto.
     apply Lsh_nonidentity.
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

Lemma mapsto_unsigned_signed:
 forall sign1 sign2 sh sz v i,
  mapsto sh (Tint sz sign1 noattr) v (Vint (cast_int_int sz sign1 i)) =
  mapsto sh (Tint sz sign2 noattr) v (Vint (cast_int_int sz sign2 i)).
Proof.
 intros.
 unfold mapsto.
 unfold address_mapsto, res_predicates.address_mapsto.
 simpl.
 destruct sz; auto;
 destruct sign1, sign2; auto;
 destruct v; auto; simpl cast_int_int;
 repeat rewrite (prop_true_andp (_ <= _ <= _)) by
  first [ apply (expr_lemmas3.sign_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.sign_ext_range' 16 i); compute; split; congruence
          ];
 repeat rewrite (prop_true_andp (_ <= _)) by
  first [ apply (expr_lemmas3.zero_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 16 i); compute; split; congruence
          ];
 simpl;
 repeat rewrite (prop_true_andp True) by auto;
 repeat rewrite (prop_false_andp  (Vint _ = Vundef) ) by (intro; discriminate);
 cbv beta;
 repeat first [rewrite @FF_orp | rewrite @orp_FF].
*
 f_equal. if_tac; [| auto]; clear H.
 f_equal; extensionality bl.
 f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite initialize.rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H1. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
 inv H3.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite initialize.rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
  if_tac; [| auto]; clear H.
 f_equal; extensionality bl.
 f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite initialize.rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite initialize.rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
  if_tac; [| auto]; clear H.
  f_equal; extensionality bl.
 f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
  if_tac; [| auto]; clear H.
 f_equal; extensionality bl.
 f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
Qed.

Lemma id2pred_star_ZnthV_Tint  {cs: compspecs} :
 forall Delta sh n (v: val) (data: list int) sz sign mdata
  (NBS: notboolsize sz),
  n = Zlength mdata -> 
  mdata = map (inttype2init_data sz) data ->
  !! isptr v && !! align_compatible (Tint sz sign noattr) v &&
  !! (offset_in_range (sizeof cenv_cs (Tint sz sign noattr) * n)) v &&
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
  assert (offset_in_range (sizeof cenv_cs (Tint sz sign noattr) * ofs) v) by
    (unfold ofs, offset_in_range; destruct v; auto;
     pose proof Int.unsigned_range i; omega).
  change 0 with (ofs* sizeof cenv_cs (Tint sz sign noattr))%Z.
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
     (fun x : environ => offset_val (Int.repr (ofs * w)) (v x))
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
  !! offset_in_range (sizeof cenv_cs tint * n) v &&
  id2pred_star Delta sh (tarray tint n) v 0 mdata |--
  `(data_at sh (tarray tint n) (map Vint data) v).
Proof. intros; apply id2pred_star_ZnthV_Tint; auto; apply I.
Qed.

Lemma gvar_isptr:
  forall i s rho, gvar i s rho -> isptr s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst; apply I.
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
   init_data_list_size (gvar_init gv) <= sizeof cenv_cs (gvar_info gv) <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
   EX s:val, local (gvar i s) &&
      `(data_at (Share.splice extern_retainer (readonly2share (gvar_readonly gv)))
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
  split; rewrite H1.
  assert (((0 <=? n) && true)%bool = true).
  rewrite Zle_imp_le_bool; [reflexivity | ]; rewrite Zlength_correct in H4; omega.
unfold legal_alignas_type.
rewrite nested_pred_ind. simpl.
rewrite nested_pred_ind.
unfold local_legal_alignas_type.
simpl.  destruct sz; auto.
split. destruct sz; reflexivity.
 split; cbv; destruct n, sz, sign; reflexivity.
  rewrite H1. (* rewrite H3.*)  rewrite H5.
(* change (Share.splice extern_retainer (readonly2share false)) with Ews. *)
  normalize. apply exp_right with s.
  apply andp_right. repeat apply andp_left1; auto.
  eapply derives_trans; [| apply id2pred_star_ZnthV_Tint; auto].
 2: rewrite <- H5; auto.
Opaque sizeof. 
  go_lower.
Transparent sizeof.
  normalize.
 rename H8 into H19.
  destruct (globvar_eval_var Delta rho _ _ H7 H H0) as [? [? ?]].
  rewrite H1 in H8.
  assert (align_compatible (Tint sz sign noattr) (eval_var i (tarray (Tint sz sign noattr) n) rho)).
  Focus 1. {
    rewrite H8.
    unfold align_compatible.
    simpl.
    apply Z.divide_0_r.
  } Unfocus.
  assert (offset_in_range (sizeof cenv_cs (Tint sz sign noattr) * n)
           (eval_var i (tarray (Tint sz sign noattr) n) rho)).
  Focus 1. {
    rewrite H8.
    unfold offset_in_range; simpl.
    rewrite H1 in H6; simpl in H6.
    pose proof initial_world.zlength_nonneg _ (gvar_init gv).
    rewrite Z.max_r in H6 by omega.
    unfold Int.max_unsigned in H6.
    pose proof init_data_list_size_pos (gvar_init gv).
    omega.
  } Unfocus.
 rewrite prop_true_andp.
  normalize.
 hnf in H19.
 destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
 rewrite H9 in H19. subst s.
 rewrite H8 in *. split3; auto.
Qed.

Lemma process_globvar:
  forall {cs: compspecs} {Espec: OracleKind} Delta P Q R (i: ident)
          gv gvs SF c Post (idata : init_data) t,
       (var_types Delta) ! i = None ->
       (glob_types Delta) ! i = Some t ->
       legal_alignas_type (gvar_info gv) = true /\
       legal_cosu_type (gvar_info gv) = true /\
       complete_type cenv_cs (gvar_info gv) = true ->
       gvar_volatile gv = false ->
       gvar_info gv = t ->
       gvar_init gv = (idata::nil) ->
       init_data_size idata <= sizeof cenv_cs t ->
       sizeof cenv_cs t <= Int.max_unsigned ->
 (forall v: val,
   semax Delta (PROPx P (LOCALx (gvar i v :: Q)
                      (SEPx (init_data2pred' Delta idata 
                         (Share.splice  extern_retainer (readonly2share (gvar_readonly gv)))
                         t v :: R)))
                       * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) 
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q) 
          (SEPx (init_data2pred' Delta idata
             (Share.splice extern_retainer
                (readonly2share (gvar_readonly gv))) t s :: R))) * fold_right sepcon emp (map globvar2pred gvs) * SF).
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
rewrite <- insert_SEP.
rewrite ! local_sepcon_assoc2.
rewrite ! local_sepcon_assoc1.
apply andp_derives; auto.
pull_left (PROPx P (LOCALx Q (SEPx R))).
rewrite ! sepcon_assoc.
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
       init_data_list_size (gvar_init gv) <= sizeof cenv_cs (gvar_info gv) <=
       Int.max_unsigned ->
 (forall v: val,
   semax Delta (PROPx P (LOCALx (gvar i v :: Q)
                      (SEPx (`(data_at
                   (Share.splice extern_retainer (readonly2share (gvar_readonly gv)))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo cast_int_int sz sign) data) v)
                    :: R)))
                       * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) 
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX  v : val,
           PROPx P (LOCALx (gvar i v :: Q) 
          (SEPx (`(data_at
                   (Share.splice extern_retainer (readonly2share (gvar_readonly gv)))
                   (tarray (Tint sz sign noattr) n)
                   (map (Vint oo cast_int_int sz sign) data) v) :: R))) * fold_right sepcon emp (map globvar2pred gvs) * SF).
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
       legal_alignas_type (gvar_info gv) = true /\
       legal_cosu_type (gvar_info gv) = true /\
       complete_type cenv_cs (gvar_info gv) = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof cenv_cs (gvar_info gv) <=
       Int.max_unsigned ->
 (forall s: val,
   semax Delta (PROPx P (LOCALx (gvar i s :: Q)
                      (SEPx R))
                  * (id2pred_star Delta
                          (Share.splice extern_retainer
                               (readonly2share (gvar_readonly gv)))
                       (gvar_info gv) s 0 (gvar_init gv))
             * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) 
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q) 
          (SEPx R))
    * id2pred_star Delta
             (Share.splice extern_retainer
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
       legal_alignas_type (gvar_info gv) = true /\
       legal_cosu_type (gvar_info gv) = true /\
       complete_type cenv_cs (gvar_info gv) = true ->
       gvar_volatile gv = false ->
       init_data_list_size (gvar_init gv) <= sizeof cenv_cs (gvar_info gv) <=
       Int.max_unsigned ->
 (forall s: val,
   semax Delta (PROPx P (LOCALx (gvar i s :: Q)
                      (SEPx (id2pred_star Delta
             (Share.splice extern_retainer
                (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0
             (gvar_init gv)
                    :: R)))
                       * globvars2pred gvs * SF)
     c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) 
                      * globvars2pred ((i,gv)::gvs) * SF)
     c Post.
Proof.
intros.
eapply semax_pre_post; [ | intros; apply andp_left2; apply derives_refl | ].
instantiate (1 := EX  s : val,
           PROPx P (LOCALx (gvar i s :: Q) 
          (SEPx (id2pred_star Delta
             (Share.splice extern_retainer
                (readonly2share (gvar_readonly gv))) (gvar_info gv) s 0
             (gvar_init gv) :: R))) * fold_right sepcon emp (map globvar2pred gvs) * SF).
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

Lemma map_instantiate:
  forall {A B} (f: A -> B) (x: A) (y: list B) z,
    y = map f z ->  f x :: y = map f (x :: z).
Proof. intros. subst. reflexivity. Qed.

Lemma main_pre_eq:
 forall prog u, main_pre prog u = 
  fold_right_sepcon' (map globvar2pred (prog_vars prog)).
Proof.
intros. rewrite fold_right_sepcon'_eq; reflexivity.
Qed.

Definition expand_globvars (Delta: tycontext)  (R R': list (environ -> mpred)) :=
 forall rho, 
    tc_environ Delta rho ->
  SEPx R rho |-- SEPx R' rho.

Lemma do_expand_globvars:
 forall R' Espec {cs: compspecs} Delta P Q R c Post,
 expand_globvars Delta R R' ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R'))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H0].
clear H0.
go_lower.
normalize.
Qed.

Lemma do_expand_globvars_cons: 
   forall Delta A A' R R',
  local (tc_environ Delta) && A |-- A' ->
  expand_globvars Delta R R' ->
  expand_globvars Delta (A::R) (A'::R').
Proof.
intros.
hnf in H|-*.
intros.
apply sepcon_derives; auto.
specialize (H rho).
simpl in H. unfold local in H.
eapply derives_trans; [ | apply H].
apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma do_expand_globvars_nil:
  forall Delta, expand_globvars Delta nil nil.
Proof.
intros. hnf; intros.
auto.
Qed.

Ltac expand_one_globvar :=
 (* given a proof goal of the form   local (tc_environ Delta) && globvar2pred (_,_) |-- ?33 *)
first [
    eapply unpack_globvar;
      [reflexivity | reflexivity | split; [| split]; reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence ]
 | eapply unpack_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply I 
      | compute; clear; congruence 
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence ]
 | eapply derives_trans;
    [ apply unpack_globvar_star; 
        [reflexivity | reflexivity | split; [| split]; reflexivity
        | reflexivity | compute; split; clear; congruence ]
    |  cbv beta; simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
      change (Share.splice extern_retainer Tsh) with Ews
    ]; apply derives_refl
 | apply andp_left2; apply derives_refl
 ].

Lemma start_main_pre:
  forall p u Q, main_pre p u * Q = PROP() LOCAL() (SEP (main_pre p u;Q)).
Proof. intros. unfold_for_go_lower. simpl. extensionality rho; normalize.
  autorewrite with subst norm1 norm2; normalize.
Qed.

Definition is_Tint sz t :=
  match t with 
  | Tint s _ _ => s = sz
  | _ => False
  end.

(*
Inductive init_rep : list init_data -> forall {t}, reptype t -> Prop :=
  | IRi8: forall {t} i, is_Tint I8 t -> init_rep (Init_int8 i :: nil) (valinject t (Vint i))
  | IRi16: forall {t} i, is_Tint I16 t -> init_rep (Init_int16 i :: nil) (valinject t (Vint i))
  | IRi32: forall {t} i, is_Tint I32 t -> init_rep (Init_int32 i :: nil) (valinject t (Vint i))
*)

Ltac simpl_main_pre' := 
  repeat match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
        match R with
        | context [ (EX s:val, local (gvar ?i s) && id2pred_star _ _ _ _ _ _) :: ?R'] =>
            let n := length_of R in
            let n' := length_of R' in
            rewrite (grab_nth_SEP (n - S n')); simpl minus;
             unfold nth, delete_nth; 
             rewrite extract_exists_in_SEP; 
             apply extract_exists_pre;
             match goal with j: name i |- _ => clear j; intro j | _ => intro end; 
             rewrite move_local_from_SEP';
             simpl gvar_init; unfold id2pred_star at 1;
             unfold init_data2pred';
             simpl PTree.get; cbv beta iota;
             simpl offset_val;
             try rewrite sepcon_emp; repeat flatten_sepcon_in_SEP
        end
  end.

(* OLD 
Ltac expand_main_pre :=
   rewrite start_main_pre, main_pre_eq; simpl map; unfold fold_right_sepcon';
   repeat flatten_sepcon_in_SEP; eapply do_expand_globvars;
   [ repeat (eapply do_expand_globvars_cons; [ expand_one_globvar | idtac ]);
      apply do_expand_globvars_nil
   | idtac ]; cbv beta;
   simpl_main_pre';
  (* is the next bunch of folds necessary? *)
  fold Ews; fold Ers; fold tint;
   fold tuint; fold tuchar; fold tschar; fold tshort; fold tushort.
*)

(*
 change (Share.splice extern_retainer Tsh) with Ews;
*)

Lemma main_pre_start:
 forall prog u,
   main_pre prog u = (PROP() LOCAL() SEP()) * globvars2pred (prog_vars prog).
Proof.
intros.
unfold main_pre, prog_vars, prog_vars', PROPx, LOCALx, SEPx.
normalize.
Qed.

Ltac process_one_globvar := 
 first
  [ simple eapply process_globvar;
      [reflexivity | reflexivity | split; [| split]; reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence | ]
  | simple eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply I 
      | compute; clear; congruence 
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence |  ]
  | simple eapply process_globvar_star';
        [reflexivity | reflexivity | split; [| split]; reflexivity
        | reflexivity | compute; split; clear; congruence 
       | simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
         change (Share.splice extern_retainer Tsh) with Ews
         ]
  ].
  
Lemma move_globfield_into_SEP:
 forall {cs: compspecs}{Espec: OracleKind} Delta P Q R 
   (S1: mpred) (S2 S3 S4: environ -> mpred) c Post,
 semax Delta (PROPx P (LOCALx Q (SEPx (`S1::R))) * S2 * S3 * S4) c Post ->
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
   (f: val -> environ -> Prop)
   (g: val -> mpred)
   (h: val -> val) (S2 S3 S4: environ -> mpred) c Post,
  (forall x: val,
   semax Delta (PROPx P (LOCALx (f x :: Q) (SEPx (`(g (h x))::R))) * S2 * S3 * S4) c Post) ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) * ((EX x:val, local (f x) && `(g (h x))) * S2) * S3 * S4) c Post.
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
auto.
Qed.

Lemma move_globfield_into_SEP'':
 forall {cs: compspecs}{Espec: OracleKind} Delta P Q R 
   (i: ident) (v: val)
   (g: val -> mpred)
   (h: val -> val) (S2 S3 S4: environ -> mpred) c Post,
   In (gvar i v) Q ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`(g (h v))::R))) * S2 * S3 * S4) c Post ->
 semax Delta (PROPx P (LOCALx Q (SEPx R)) * ((EX x:val, local (sgvar i x) && `(g (h x))) * S2) * S3 * S4) c Post.
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

Ltac process_idstar := 
  match goal with
  | |- semax _ (_ * globvars2pred ((?i,_)::_) * _) _ _ =>
    match goal with
    | n: name i |- _ => process_one_globvar; clear n; intro n
    | |- _ => process_one_globvar; intros ?gvar0
    end;
    match goal with |- semax _ (_ * ?A * _ * _) _ _ =>
         let p := fresh "p" in set (p:=A);
         simpl in p;
         unfold id2pred_star, init_data2pred' in p;
         simpl PTree.get in p;
         cbv beta iota zeta in p;
         simpl init_data_size in p; simpl Z.add in p;
         subst p;
      repeat first
        [simple apply move_globfield_into_SEP
        | simple eapply move_globfield_into_SEP''; [ now repeat econstructor | ]
        | simple apply move_globfield_into_SEP'; intros ?gvar0
        ];
      simple apply move_globfield_into_SEP0
   | |- _ => idtac    
   end
 end.

Ltac expand_main_pre := 
 rewrite main_pre_start;
 unfold prog_vars, prog_vars'; simpl globvars2pred;
 repeat  process_idstar;
 change (globvars2pred nil) with (@emp (environ->mpred) _ _);
 rewrite (sepcon_emp (PROPx _ _)).
