Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.array_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.unfold_data_at.
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
  mapsto_zeros n sh (Vptr b ofs) |--
  memory_block sh (Int.repr n) (Vptr b ofs).
Proof.
  unfold mapsto_zeros.
  intros.
  rename H0 into H'.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  rewrite (Int.unsigned_repr n) by (unfold Int.max_unsigned; omega).
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
      * unfold mapsto_, mapsto.
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

Definition zero_of_type (t: type) : val :=
 match t with
  | Tfloat _ _ => Vfloat Float.zero
  | _ => Vint Int.zero
 end.

Definition init_data2pred' (Delta: tycontext)  (d: init_data)  (sh: share) (ty: type) (v: environ->val) : environ -> mpred :=
 match d with
  | Init_int8 i => `(mapsto sh tuchar) v `(Vint (Int.zero_ext 8 i))
  | Init_int16 i => `(mapsto sh tushort) v ` (Vint (Int.zero_ext 16 i))
  | Init_int32 i => `(mapsto sh tuint) v ` (Vint i)
  | Init_int64 i => `(mapsto sh tulong) v ` (Vlong i)
  | Init_float32 r =>  `(mapsto sh tfloat) v ` (Vsingle r)
  | Init_float64 r =>  `(mapsto sh tdouble) v ` (Vfloat r)
  | Init_space n => if zeq n (sizeof ty)
                                   then `(data_at_ sh ty) v
                                   else if zlt n 0 then TT
                                   else`(memory_block sh (Int.repr n)) v
  | Init_addrof symb ofs => 
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Tarray t n' att) =>`(mapsto sh (Tpointer t noattr)) v (`(offset_val ofs) (eval_var symb (Tarray t n' att)))
      | None, Some Tvoid => TT
      | None, Some t => `(mapsto sh (Tpointer t noattr)) v (`(offset_val ofs) (eval_var symb t))
      | Some _, Some (Tarray t _ att) => `(memory_block sh (Int.repr 4)) v
      | Some _, Some Tvoid => TT
      | Some _, Some (Tpointer (Tfunction _ _ _) _) => `(memory_block sh (Int.repr 4)) v 
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

Lemma unpack_globvar_aux1:
  forall sh t b v i_ofs, 
  Int.unsigned i_ofs + sizeof (Tpointer t noattr) <= Int.max_unsigned ->
               mapsto sh (Tpointer t noattr) (Vptr b i_ofs) v
                   |-- memory_block sh (Int.repr 4) (Vptr b i_ofs).
Proof.
intros.
 eapply derives_trans; [ apply mapsto_mapsto_ | ].
 rewrite (memory_block_mapsto_ _ _ (Tpointer t noattr)); auto.
 apply I.
 unfold size_compatible; unfold Int.max_unsigned in H; omega.
 admit. (* align_compatible can be FOUND inside mapsto *)
Qed.

Lemma sizeof_Tpointer: forall t, sizeof (Tpointer t noattr) = 4.
Proof.
intros. reflexivity.
Qed.

Lemma init_data_size_space:
 forall t, init_data_size (Init_space (sizeof t)) = sizeof t.
Proof. intros.
 pose proof (sizeof_pos t).
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

Lemma init_data2pred_rejigger:
  forall (Delta : tycontext) (t : type) (idata : init_data) (rho : environ)
     (sh : Share.t) (b : block) ofs (v : environ -> val),
  legal_alignas_type t = true -> 
  nested_legal_fieldlist t = true -> 
  nested_non_volatile_type t = true ->
  0 <= ofs ->
  ofs + init_data_size idata <= Int.max_unsigned ->
  tc_environ Delta rho ->
  v rho = Vptr b (Int.repr 0) ->
  (alignof t | Int.unsigned (Int.repr ofs)) ->
   init_data2pred idata sh (offset_val (Int.repr ofs) (v rho)) rho 
    |-- init_data2pred' Delta idata sh t (`(offset_val (Int.repr ofs)) v) rho.
Proof.
intros until v.
intros H1 HH H1' H6' H6 H7 H8 H1''.
 unfold init_data2pred', init_data2pred.
 rename H8 into H8'.
 assert (H8: offset_val (Int.repr ofs) (v rho) = Vptr b (Int.repr ofs)).
 rewrite H8'; simpl. rewrite Int.add_zero_l; auto.
 clear H8'.
 destruct idata; super_unfold_lift; try apply derives_refl.
*  repeat if_tac; try rewrite H8. 
   + subst z; rewrite init_data_size_space in H6.
     rewrite data_at__memory_block by (auto; unfold Int.max_unsigned in H6; omega).
     repeat apply andp_right.
     - apply prop_right. auto.
     - apply prop_right. auto.
     - apply prop_right.
       unfold align_compatible.
       exact H1''.
     - unfold Int.max_unsigned in H6.
       apply mapsto_zeros_memory_block; auto.
       1: pose proof (sizeof_pos t); omega.
       1: pose proof unsigned_repr_range ofs H6'; omega.
   + simpl; apply TT_right.
   + unfold init_data_size in H6. rewrite Z.max_l in H6 by omega.
     unfold Int.max_unsigned in H6.
     apply mapsto_zeros_memory_block; auto.
     - pose proof (sizeof_pos t); omega.
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
    rewrite H8; auto.
    rewrite H8; auto.
 +
   destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' [H15 H16]]; rewrite H15.
    assert (eval_var i t0 rho = Vptr b' Int.zero).
    {destruct (globvar_eval_var _ _ _ _ H7 Hv Hg) as [bx [? ?]].
      rewrite H15 in H0. symmetry in H0; inv H0.
      rewrite <- H. reflexivity.
     }
    destruct t0; simpl; try apply TT_right; try rewrite H8; try rewrite H;
     unfold offset_val; simpl; rewrite Int.add_zero_l;
    apply derives_refl.
Qed.

Lemma unpack_globvar:
  forall Delta i t gv idata, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
   (legal_alignas_type t = true /\ nested_legal_fieldlist t = true /\
    nested_non_volatile_type t = true) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   init_data_size idata <= sizeof t ->
   sizeof t <= Int.max_unsigned ->  
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
       init_data2pred' Delta idata (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) t (eval_var i t).
Proof.
intros.
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound; try eassumption | ].
forget (readonly2share (gvar_readonly gv)) as sh.
unfold init_data_list2pred.
simpl.
rewrite sepcon_emp.
destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?].
 replace (eval_var i t rho) with (offset_val Int.zero (eval_var i t rho)) by (rewrite H8; reflexivity).
 eapply derives_trans.
 + eapply init_data2pred_rejigger; destruct H1; eauto.
   - tauto.
   - tauto.
   - omega.
   - omega.
   - simpl. apply Z.divide_0_r.
 + 
 unfold init_data2pred'.
 destruct idata; unfold_lift;
   try (rewrite H8; simpl; rewrite Int.add_zero_l; auto);
 try apply derives_refl.
 if_tac. rewrite H8. simpl; rewrite Int.add_zero_l; auto.
 if_tac; auto.  rewrite H8. simpl; rewrite Int.add_zero_l; auto.
 destruct ((var_types Delta)!i0); auto;
 destruct ( (glob_types Delta) ! i0); try destruct g;try destruct gv0; try apply derives_refl;
   try (rewrite H8; simpl; rewrite Int.add_zero_l; auto).
 destruct t1; auto.
 destruct t1; auto.
 rewrite H8; simpl; rewrite Int.add_zero_l; auto.
 rewrite H8; simpl; rewrite Int.add_zero_l; auto.
 destruct t0; auto;
  try (rewrite H8; simpl; rewrite Int.add_zero_l; auto).
Qed.

Fixpoint id2pred_star (Delta: tycontext) (sh: share) (t: type) (v: environ->val) (ofs: Z) (dl: list init_data) : environ->mpred :=
 match dl with
 | d::dl' => init_data2pred' Delta d sh t (`(offset_val (Int.repr ofs)) v)
                   * id2pred_star Delta sh t v (ofs + init_data_size d) dl'
 | nil => emp
 end.

Arguments id2pred_star Delta sh t v ofs dl rho  / .

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

Lemma unpack_globvar_star:
  forall Delta i gv, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
   (legal_alignas_type (gvar_info gv) = true /\
    nested_legal_fieldlist (gvar_info gv) = true /\
    nested_non_volatile_type (gvar_info gv) = true) -> 
   gvar_volatile gv = false ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
       id2pred_star Delta (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) (gvar_info gv) (eval_var i (gvar_info gv)) 0 (gvar_init gv).
Proof.
assert (H5:=true).
intros until 4.
remember (gvar_info gv) as t eqn:H3; symmetry in H3.
remember (gvar_init gv) as idata eqn:H4; symmetry in H4.
intros. 
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound; eassumption | ].
forget (readonly2share (gvar_readonly gv)) as sh.
destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?].
set (ofs:=0%Z).
assert (alignof t | Int.unsigned (Int.repr ofs)) by (subst ofs; simpl; apply Z.divide_0_r).
replace (eval_var i t rho) with (offset_val (Int.repr ofs) (eval_var i t rho))
   by (rewrite H8; reflexivity).
assert (H11: init_data_list_size idata + ofs <= sizeof t)  by (unfold ofs; omega).
assert (H12:  sizeof t <= Int.max_unsigned)  by omega.
assert (0 <= ofs) by (unfold ofs; omega).
clearbody ofs.
revert ofs H9 H10 H11 H12.
clear dependent gv. clear H H0 H6.
induction idata; simpl; auto; intros.
apply sepcon_derives.
* eapply init_data2pred_rejigger; destruct H1; eauto; try tauto.
 pose proof (init_data_list_size_pos idata); omega.
* specialize (IHidata (ofs + init_data_size a)).
rewrite offset_offset_val.
rewrite add_repr.
 pose proof (init_data_list_size_pos idata).
pose proof (init_data_size_pos a).
 apply IHidata; try omega.
admit. (* alignment issue *)
Qed.

Lemma tc_globalvar_sound_space:
  forall Delta i t gv rho, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some t ->
   (legal_alignas_type t = true /\ nested_legal_fieldlist t = true /\
    nested_non_volatile_type t = true) ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   sizeof t <= Int.max_unsigned ->
   tc_environ Delta rho ->
   (!! ((align_compatible t) (eval_var i t rho))) && globvar2pred (i, gv) rho |-- 
   data_at_ (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) t (eval_var i t rho).
Proof.
assert (H4 := true).
intros until 1. intros ? Hno; intros.
normalize.
eapply derives_trans; [eapply tc_globalvar_sound; eassumption | ].
simpl.
rewrite data_at__memory_block by (try tauto; unfold Int.max_unsigned in H5; omega).
destruct (tc_eval_gvar_zero _ _ _ _ H6 H H0) as [b ?].
rewrite H8 in H7 |- *.
unfold mapsto_zeros. rewrite sepcon_emp.
rewrite Int.unsigned_zero.
pose proof (mapsto_zeros_memory_block
  (Share.splice extern_retainer (readonly2share (gvar_readonly gv))) (sizeof t) b Int.zero).
unfold mapsto_zeros in H9. change (Int.repr 0) with Int.zero in H9.
rewrite Int.unsigned_zero in H9.
apply andp_right.
+ normalize.
  apply prop_right.
  tauto.
+ apply H9.
  pose (sizeof_pos t).
  - unfold Int.max_unsigned in H5. omega.
  - unfold Int.max_unsigned in H5. omega.
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
 f_equal. f_equal; extensionality bl.
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
 f_equal. f_equal; extensionality bl.
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
 f_equal. f_equal; extensionality bl.
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
 f_equal. f_equal; extensionality bl.
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

Lemma id2pred_star_ZnthV_Tint:
 forall Delta sh n v (data: list int) sz sign mdata
  (NBS: notboolsize sz),
  n = Zlength mdata -> 
  mdata = map (inttype2init_data sz) data ->
  local (`isptr v) && local (`(align_compatible (Tint sz sign noattr)) v) &&
  local (`(offset_in_range (sizeof (Tint sz sign noattr) * n)) v) &&
  id2pred_star Delta sh (tarray (Tint sz sign noattr) n) v 0 mdata |--
  `(data_at sh (tarray (Tint sz sign noattr) n) 
           (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)) v.
Proof.
  intros. subst n mdata.
  replace (Zlength (map  (inttype2init_data sz) data)) with (Zlength data)
    by (repeat rewrite Zlength_correct; rewrite map_length; auto).
  set (ofs:=0%Z).
  unfold ofs at 1.
  go_lowerx.
  assert (offset_in_range (sizeof (Tint sz sign noattr) * ofs) (v rho)) by
    (unfold ofs, offset_in_range; destruct (v rho); auto;
     pose proof Int.unsigned_range i; omega).
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

Lemma id2pred_star_ZnthV_tint:
 forall Delta sh n v (data: list int) mdata,
  n = Zlength mdata ->
  mdata = map Init_int32 data ->
  local (`isptr v) && local (`(align_compatible tint) v) &&
  local (`(offset_in_range (sizeof tint * n)) v) &&
  id2pred_star Delta sh (tarray tint n) v 0 mdata |--
  `(data_at sh (tarray tint n) (map Vint data)) v.
Proof. intros; apply id2pred_star_ZnthV_Tint; auto; apply I.
Qed.

Lemma unpack_globvar_array:
  forall t sz sign (data: list int)  n Delta i gv,
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (gvar_info gv) ->
   gvar_info gv = tarray t n ->
   gvar_volatile gv = false ->
   t = Tint sz sign noattr -> 
  forall    (NBS: notboolsize sz),
   n = Zlength (gvar_init gv) ->
   gvar_init gv = map (inttype2init_data sz) data ->
   init_data_list_size (gvar_init gv) <= sizeof (gvar_info gv) <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
      `(data_at (Share.splice extern_retainer (readonly2share (gvar_readonly gv)))
       (tarray (Tint sz sign noattr) n)
    (map (Basics.compose Vint (Cop.cast_int_int sz sign)) data)) (eval_var i (tarray t n)).
Proof.
  intros. subst t.
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (tc_environ Delta)))
  end.
  Focus 2. {
    apply andp_left1; cancel.
  } Unfocus.
  match goal with |- ?A |-- _ =>
    erewrite (add_andp A (local (`isptr (eval_var i (tarray (Tint sz sign noattr) n)))))
  end.
  Focus 2. {
    go_lowerx. apply prop_right. eapply eval_var_isptr; eauto.
    right; split; auto. rewrite <- H1; auto.
   } Unfocus.
  eapply derives_trans;[ apply andp_derives; [ apply andp_derives; [ eapply unpack_globvar_star; try eassumption; try reflexivity | apply derives_refl]  | apply derives_refl] |].
  split; rewrite H1. cbv; destruct n; reflexivity. split; cbv; destruct n, sz, sign; reflexivity.
  rewrite H1. (* rewrite H3.*)  rewrite H5.
(* change (Share.splice extern_retainer (readonly2share false)) with Ews. *)
  eapply derives_trans; [| apply id2pred_star_ZnthV_Tint; auto].
Opaque sizeof. 
  go_lower.
Transparent sizeof.
  normalize.
  destruct (globvar_eval_var Delta rho _ _ H7 H H0) as [? [? ?]].
  rewrite H1 in H8.
  assert (align_compatible (Tint sz sign noattr) (eval_var i (tarray (Tint sz sign noattr) n) rho)).
  Focus 1. {
    rewrite H8.
    unfold align_compatible.
    simpl.
    apply Z.divide_0_r.
  } Unfocus.
  assert (offset_in_range (sizeof (Tint sz sign noattr) * n)
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
  normalize.
rewrite <- H5; auto.
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
 forall R' Espec Delta P Q R c Post,
 expand_globvars Delta R R' ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx R'))) c Post ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
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
Qed.

Definition Ers (* Extern read share *) := 
    Share.splice extern_retainer Share.Lsh.

Ltac expand_main_pre :=
 rewrite start_main_pre, main_pre_eq; simpl map; 
  unfold fold_right_sepcon'; repeat flatten_sepcon_in_SEP;
 eapply do_expand_globvars;
 [ repeat 
   (eapply do_expand_globvars_cons;
    [ expand_one_globvar | ]);
   apply do_expand_globvars_nil
 | ];
 cbv beta;
 simpl init_data2pred';
 fold Ews; fold Ers; fold tint; fold tuint; fold tuchar; fold tschar; fold tshort; fold tushort.
(*
 change (Share.splice extern_retainer Tsh) with Ews;
*)
