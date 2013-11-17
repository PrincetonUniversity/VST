Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.malloc_lemmas.
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

Lemma address_mapsto_zeros_memory_block:
 forall sh n b,
  0 <= n <= Int.max_unsigned ->
  address_mapsto_zeros sh (nat_of_Z n) (b, 0) |--
  memory_block sh (Int.repr n) (Vptr b Int.zero).
Proof.
intros.
Transparent memory_block.
 unfold memory_block.
Opaque memory_block.
 rewrite Int.unsigned_repr by auto.
rewrite Int.unsigned_zero.
 assert (exists i, i=0) as [i ?] by eauto.
 rewrite <- H0.
 assert (0 <= i) by omega.
 assert (i + n <= Int.max_unsigned).
 subst. omega.
 rewrite <- (Z2Nat.id n) in H2 by omega.
 change nat_of_Z with Z.to_nat.
 clear - H1 H2.
 forget (Z.to_nat n) as n'.
 revert i H1 H2;  induction n'; intros.
 simpl; auto.
 rewrite inj_S in H2. unfold Z.succ in H2.
 apply sepcon_derives; auto.
 unfold mapsto_, umapsto.
 apply orp_right2.
 rewrite prop_true_andp by auto.
 apply exp_right with (Vint Int.zero).
 rewrite Int.unsigned_repr by omega. 
 auto.
 fold address_mapsto_zeros. fold memory_block'.
 apply IHn'. omega. omega.
Qed.

Lemma tc_globalvar_sound:
  forall Delta i t gv idata rho, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   no_attr_type t = true ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   tc_environ Delta rho ->
   globvar2pred(i, gv) rho |-- init_data2pred idata Ews (eval_var i t rho) rho.
Proof.
intros until 1. intros ? Hno; intros.
unfold globvar2pred.
simpl.
destruct H6 as [? [? [? ?]]].
destruct (H9 i _ H0); [ | destruct H10; congruence].
destruct (H8 _ _ H0) as [b [? ?]].
rewrite H11. rewrite H1.
rewrite H3; simpl.
unfold eval_var.
unfold Map.get. rewrite H10. rewrite H11.
simpl. rewrite eqb_type_refl.
rewrite H4.
simpl.
change (Share.splice extern_retainer Tsh) with Ews.
rewrite sepcon_emp.
auto.
Qed.

Definition zero_of_type (t: type) : val :=
 match t with
  | Tfloat _ _ => Vfloat Float.zero
  | _ => Vint Int.zero
 end.

Definition init_data2pred' (Delta: tycontext)  (d: init_data)  (sh: share) (id: ident)(ty: type) : environ -> mpred :=
 match d with
  | Init_int8 i => `(mapsto sh tuchar) (eval_var id ty) `(Vint (Int.zero_ext 8 i))
  | Init_int16 i => `(mapsto sh tushort) (eval_var id ty) ` (Vint (Int.zero_ext 16 i))
  | Init_int32 i => `(mapsto sh tuint) (eval_var id ty) ` (Vint i)
  | Init_int64 i => `(mapsto sh tulong) (eval_var id ty) ` (Vlong i)
  | Init_float32 r =>  `(mapsto sh tfloat) (eval_var id ty) ` (Vfloat ((Float.singleoffloat r)))
  | Init_float64 r =>  `(mapsto sh tdouble) (eval_var id ty) ` (Vfloat r)
  | Init_space n => 
     if andb (Z.leb 0 n) (Z.leb n Int.max_unsigned)
     then
      match ty  with
      | Tarray t j att => if zeq n (sizeof ty)
                                  then `(array_at_ t sh 0 j) (eval_var id ty) (* FIXME *)
                                  else `(memory_block sh (Int.repr n)) (eval_var id ty) 
      | Tvoid => TT
      | Tfunction _ _ => TT
      | Tstruct _ _ _ => TT (* FIXME *)
      | Tunion _ _ _ => TT (* FIXME *)
      | Tcomp_ptr _ _ => TT
      | t=> if zeq n (sizeof t) 
                               then `(mapsto sh t) (eval_var id ty) `(zero_of_type t)
                               else `(memory_block sh (Int.repr n)) (eval_var id ty) 
      end
    else TT
  | Init_addrof symb ofs => 
      match (var_types Delta) ! symb, (glob_types Delta) ! symb with
      | None, Some (Global_var (Tarray t _ att)) =>`(memory_block sh (Int.repr 4)) (eval_var id ty)
      | None, Some (Global_var Tvoid) => TT
      | None, Some (Global_var t) => `(mapsto sh (Tpointer t noattr)) (eval_var id ty) (`(offset_val ofs) (eval_var symb t))
      | Some _, Some (Global_var (Tarray t _ att)) => `(memory_block sh (Int.repr 4)) (eval_var id ty)
      | Some _, Some (Global_var Tvoid) => TT
      | Some _, Some (Global_var t) => `(memory_block sh (Int.repr 4)) (eval_var id ty) 
      | _, _ => TT
      end
 end.


Lemma mapsto_zeros_Tint:
  forall i s a b,
   mapsto_zeros (sizeof (Tint i s a)) Ews (Vptr b Int.zero)
|-- mapsto Ews (Tint i s a) (Vptr b Int.zero) (Vint Int.zero).
Admitted.

Lemma mapsto_zeros_Tlong:
  forall s a b,
   mapsto_zeros (sizeof (Tlong s a)) Ews (Vptr b Int.zero)
|-- mapsto Ews (Tlong s a) (Vptr b Int.zero) (Vint Int.zero).
Admitted.

Lemma mapsto_zeros_Tfloat:
  forall f a b, 
  mapsto_zeros (sizeof (Tfloat f a)) Ews (Vptr b Int.zero)
|-- mapsto Ews (Tfloat f a) (Vptr b Int.zero) (Vfloat Float.zero).
Admitted.

Lemma mapsto_zeros_Tpointer:
  forall t a b, 
mapsto_zeros (sizeof (Tpointer t a)) Ews (Vptr b Int.zero)
|-- mapsto Ews (Tpointer t a) (Vptr b Int.zero) (Vint Int.zero).
Admitted.

Lemma unpack_globvar_aux1:
  forall sh t a b v, umapsto sh (Tpointer t a) (Vptr b Int.zero) v
                   |-- memory_block sh (Int.repr 4) (Vptr b Int.zero).
Admitted.

Lemma unpack_globvar:
  forall Delta i t gv idata, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   no_attr_type t = true ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = idata :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
       init_data2pred' Delta idata Ews i t.
Proof.
intros.
go_lowerx.
eapply derives_trans; [eapply tc_globalvar_sound; eassumption | ].
destruct (tc_eval_gvar_zero _ _ _ _ H7 H H0) as [b ?].
 unfold init_data2pred', init_data2pred.
 destruct idata; super_unfold_lift;
 try solve [apply andp_right; [apply prop_right; apply I | apply derives_refl]].
 destruct (0 <=? z) eqn:? ; [ | simpl; apply TT_right].
 destruct (z <=? Int.max_unsigned) eqn:? ; [ | simpl; apply TT_right].
 apply Zle_bool_imp_le in Heqb0.
 apply Zle_bool_imp_le in Heqb1.
* destruct t;
  try (simpl; apply TT_right);
  try (simpl andb; cbv iota; if_tac;
        [rewrite H8; unfold zero_of_type; subst z;
         first [simple apply mapsto_zeros_Tint | simple apply mapsto_zeros_Tlong 
                |simple apply mapsto_zeros_Tfloat | simple apply mapsto_zeros_Tpointer
                ]
        | rewrite H8; apply address_mapsto_zeros_memory_block; split; auto
        ]).
 + simpl andb; cbv iota; if_tac; rewrite H8.
   eapply derives_trans; [ apply address_mapsto_zeros_memory_block; split; auto | ].
   subst z.
 rewrite memory_block_typed.
 rewrite array_at_arrayof'.
 unfold typed_mapsto_. simpl.
 rewrite withspacer_spacer. unfold spacer. rewrite align_0. simpl.
 rewrite emp_sepcon.
 rewrite Z.mul_0_r. rewrite Z.sub_0_r.
 apply derives_refl.
 apply alignof_pos.
 apply H1.
 apply address_mapsto_zeros_memory_block; split; auto.
* destruct ((var_types Delta) ! i0) eqn:Hv;
   destruct ((glob_types Delta) ! i0) eqn:Hg; 
    try destruct g; try solve [simpl; apply TT_right].
 destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' [H15 H16]]; rewrite H15.
  rewrite H8.
 destruct gv0; simpl; try apply TT_right; try rewrite H8;
   try  apply unpack_globvar_aux1.
  destruct (proj1 (proj2 (proj2 H7)) _ _ Hg) as [b' [H15 H16]]; rewrite H15.
 assert (eval_var i0 gv0 rho = Vptr b' Int.zero)
   by admit.  (* straightforward *)
 destruct gv0; simpl; try apply TT_right; try rewrite H8; try rewrite H9;
 unfold mapsto; try (apply andp_right; [apply prop_right; apply I | apply derives_refl ]).
apply unpack_globvar_aux1.
Qed.

Lemma tc_globalvar_sound_space:
  forall Delta i t gv rho, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   no_attr_type t = true ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   tc_environ Delta rho ->
   globvar2pred(i, gv) rho |-- 
   typed_mapsto_ Ews t (eval_var i t rho).
Proof.
intros until 1. intros ? Hno; intros.
eapply derives_trans; [eapply tc_globalvar_sound; eassumption | ].
simpl.
rewrite <- memory_block_typed by auto.
destruct (tc_eval_gvar_zero _ _ _ _ H6 H H0) as [b ?].
rewrite H7.
unfold mapsto_zeros.
rewrite Int.unsigned_zero.
apply address_mapsto_zeros_memory_block.
pose (sizeof_pos t); omega.
Qed.

(*
Lemma tc_globalvar_sound':
  forall Delta i t gv, 
   (var_types Delta) ! i = None ->
   (glob_types Delta) ! i = Some (Global_var t) ->
   no_attr_type t = true ->
   gvar_volatile gv = false ->
   gvar_info gv = t ->
   gvar_init gv = Init_space (sizeof t) :: nil ->
   gvar_readonly gv = false ->
   sizeof t <= Int.max_unsigned ->
   local (tc_environ Delta) && globvar2pred(i, gv) |-- 
   `(typed_mapsto_ Ews t) (eval_var i t).
Proof.
intros.
go_lowerx.
eapply tc_globalvar_sound; eauto.
Qed.
*) 

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
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence ]
 | apply andp_left2; apply derives_refl
 ].

Ltac expand_main_pre := 
 rewrite main_pre_eq; simpl fold_right_sepcon;
 eapply do_expand_globvars;
 [repeat 
   (eapply do_expand_globvars_cons;
    [ expand_one_globvar | ]);
   apply do_expand_globvars_nil
 |  ];
 unfold init_data2pred'; simpl.


