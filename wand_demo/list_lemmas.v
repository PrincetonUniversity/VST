Require Import floyd.proofauto.
Require Import wand_demo.wand_frame.
Require Import wand_demo.wandQ_frame.
Require Import wand_demo.list.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share) (contents: list int) (x: val) : mpred :=
 match contents with
 | h::hs => field_at sh t_struct_list [StructField _head] (Vint h) x *
              EX y:val,
                field_at sh t_struct_list [StructField _tail] y x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Module ListHead.

Lemma wand_frame_intro_list_head: forall sh (x y: int) (s: list int) (l: val),
  listrep sh (x :: s) l |--
    field_at sh t_struct_list [StructField _head] (Vint x) l *
      (field_at sh t_struct_list [StructField _head] (Vint y) l -* listrep sh (y :: s) l).
Proof.
  intros; simpl.
  apply sepcon_derives; auto.
  apply wand_frame_intro.
Qed.

End ListHead.

Module LsegWandFrame.

Definition lseg (sh: share) (tcontents contents: list int) (x z: val) : mpred :=
  listrep sh tcontents z -* listrep sh (contents ++ tcontents) x.

Lemma singleton_lseg: forall sh (contents: list int) (a: int) (x y: val),
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x |--
  lseg sh contents [a] x y.
Proof.
  intros.
  unfold lseg.
  apply -> wand_sepcon_adjoint.
  simpl app.
  simpl listrep.
  Exists y.
  cancel.
Qed.

Lemma app_lseg: forall sh (s1 s2 t: list int) (x y z: val),
  lseg sh t s2 y z * lseg sh (s2 ++ t) s1 x y |-- lseg sh t (s1 ++ s2) x z.
Proof.
  intros.
  unfold lseg.
  eapply derives_trans; [apply wand_frame_ver |].
  rewrite app_assoc; auto.
Qed.

End LsegWandFrame.

Module LsegWandQFrame.

Definition lseg (sh: share) (contents: list int) (x z: val) : mpred :=
  ALL tcontents: list int, listrep sh tcontents z -* listrep sh (contents ++ tcontents) x.

Lemma singleton_lseg: forall sh (contents: list int) (a: int) (x y: val),
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x |--
  lseg sh [a] x y.
Proof.
  intros.
  unfold lseg.
  apply allp_right; intros.
  apply -> wand_sepcon_adjoint.
  simpl app.
  simpl listrep.
  Exists y.
  cancel.
Qed.

Lemma app_lseg: forall sh (s1 s2: list int) (x y z: val),
  lseg sh s2 y z * lseg sh s1 x y |-- lseg sh (s1 ++ s2) x z.
Proof.
  intros.
  unfold lseg.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl |] | apply wandQ_frame_ver].
  eapply derives_trans; [apply (wandQ_frame_refine _ _ _ (app s2)) |].
  apply derives_refl'.
  f_equal; extensionality tcontents; simpl.
  rewrite app_assoc.
  auto.
Qed.

End LsegWandQFrame.

Arguments listrep sh contents x : simpl never.

Module ListLib.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H4.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply field_at_valid_ptr0; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents x,
  x = nullval ->
  listrep sh contents x = !! (contents=nil) && emp.
Proof.
  intros; subst.
  destruct contents; unfold listrep; fold listrep.
  normalize.
  apply pred_ext.
  Intros y. entailer. destruct H; contradiction.
  Intros.
Qed.

Lemma listrep_nonnull: forall sh contents x,
  x <> nullval ->
  listrep sh contents x = EX h: int, EX hs: list int, EX y:val,
    !! (contents = h :: hs) &&
    field_at sh t_struct_list [StructField _head] (Vint h) x *
    field_at sh t_struct_list [StructField _tail] y x *
    listrep sh hs y.
Proof.
  intros.
  destruct contents; unfold listrep; fold listrep.
  + apply pred_ext; [normalize |].
    Intros h hs y.
  + apply pred_ext.
    - Intros y. Exists i contents y.
      entailer!.
    - Intros h hs y. Exists y.
      inv H0; subst.
      entailer!.
Qed.

(*
Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.
*)
End ListLib.

