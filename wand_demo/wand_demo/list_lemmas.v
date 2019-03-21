Require Import VST.floyd.proofauto.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.
Require Import WandDemo.list.
Require Import WandDemo.wandQ_frame_tactic.
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

Module LsegRecursiveLoopFree.

Fixpoint lseg (sh: share) (contents: list int) (x z: val) : mpred :=
  match contents with
  | h::hs => !! (x<>z) && 
             EX y:val,
               field_at sh t_struct_list [StructField _head] (Vint h) x *
               field_at sh t_struct_list [StructField _tail] y x *
               lseg sh hs y z
 | nil => !! (x = z) && emp
 end.

Arguments lseg sh contents x z : simpl never.

Lemma singleton_lseg: forall sh (contents: list int) (a: int) (x y: val),
  readable_share sh ->
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x *
  listrep sh contents y |--
  lseg sh [a] x y *
  listrep sh contents y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  entailer.
  destruct contents; unfold listrep at 1; fold listrep;
  entailer.
Qed.

Lemma singleton_lseg': forall sh (a b: int) (x y: val),
  readable_share sh ->
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x *
  field_at sh t_struct_list [StructField _head] (Vint b) y |--
  lseg sh [a] x y *
  field_at sh t_struct_list [StructField _head] (Vint b) y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  entailer.
Qed.

Lemma lseg_lseg: forall sh (s1 s2: list int) (a: int) (x y z: val),
  readable_share sh ->
  lseg sh s2 y z * lseg sh s1 x y * field_at sh t_struct_list [StructField _head] (Vint a) z |--
  lseg sh (s1 ++ s2) x z * field_at sh t_struct_list [StructField _head] (Vint a) z.
Proof.
  intros.
  revert x; induction s1; intros; simpl.
  + unfold lseg at 2; entailer!.
  + unfold lseg at 2 3; fold lseg.
    Intros y'; Exists y'.
    entailer.
    sep_apply (IHs1 y').
    cancel.
Qed.
(* TODO: swap the order of * *)
Lemma list_lseg: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s1 x y |-- listrep sh (s1 ++ s2) x.
Proof.
  intros.
  revert x; induction s1; intros; simpl.
  + unfold lseg at 1. entailer!.
  + unfold lseg; fold lseg.
    Intros x'; Exists x'.
    entailer!.
    apply IHs1.
Qed.

End LsegRecursiveLoopFree.

Module LsegRecursiveMaybeLoop.

Fixpoint lseg (sh: share) (contents: list int) (x z: val) : mpred :=
  match contents with
  | h::hs => EX y:val,
               field_at sh t_struct_list [StructField _head] (Vint h) x *
               field_at sh t_struct_list [StructField _tail] y x *
               lseg sh hs y z
 | nil => !! (x = z) && emp
 end.

Arguments lseg sh contents x z : simpl never.

Lemma singleton_lseg: forall sh (a: int) (x y: val),
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x |--
  lseg sh [a] x y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  entailer!.
Qed.

Lemma lseg_lseg: forall sh (s1 s2: list int) (x y z: val),
  lseg sh s2 y z * lseg sh s1 x y |-- lseg sh (s1 ++ s2) x z.
Proof.
  intros.
  revert x; induction s1; intros; simpl.
  + unfold lseg at 2; entailer!.
  + unfold lseg at 2 3; fold lseg.
    Intros y'; Exists y'.
    entailer.
    sep_apply (IHs1 y').
    cancel.
Qed.

Lemma list_lseg: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s1 x y |-- listrep sh (s1 ++ s2) x.
Proof.
  intros.
  revert x; induction s1; intros; simpl.
  + unfold lseg at 1. entailer!.
  + unfold lseg; fold lseg.
    Intros x'; Exists x'.
    entailer!.
    apply IHs1.
Qed.

End LsegRecursiveMaybeLoop.

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

Lemma lseg_lseg: forall sh (s1 s2 t: list int) (x y z: val),
  lseg sh t s2 y z * lseg sh (s2 ++ t) s1 x y |-- lseg sh t (s1 ++ s2) x z.
Proof.
  intros.
  unfold lseg.
  eapply derives_trans; [apply wand_frame_ver |].
  rewrite app_assoc; auto.
Qed.

Lemma list_lseg: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s2 s1 x y |-- listrep sh (s1 ++ s2) x.
Proof.
  intros.
  unfold lseg.
  apply wand_frame_elim.
Qed.

End LsegWandFrame.

Module GeneralLseg.

Section GeneralLseg.

Variable listrep: share -> list int -> val -> mpred.

Definition lseg (sh: share) (contents: list int) (x z: val) : mpred :=
  ALL tcontents: list int, listrep sh tcontents z -* listrep sh (contents ++ tcontents) x.

Lemma lseg_lseg: forall sh (s1 s2: list int) (x y z: val),
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

Lemma lseg_lseg_proof_by_tactic: forall sh (s1 s2: list int) (x y z: val),
  lseg sh s2 y z * lseg sh s1 x y |-- lseg sh (s1 ++ s2) x z.
Proof.
  intros.
  solve_wandQ lseg.
  rewrite app_assoc.
  auto.
Qed.

Lemma list_lseg: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s1 x y |-- listrep sh (s1 ++ s2) x.
Proof.
  intros.
  unfold lseg.
  change (listrep sh s2 y) with ((fun s2 => listrep sh s2 y) s2).
   change
     (ALL tcontents : list int , listrep sh tcontents y -* listrep sh (s1 ++ tcontents) x)
   with
     (allp ((fun tcontents => listrep sh tcontents y) -* (fun tcontents => listrep sh (s1 ++ tcontents) x))).
   change (listrep sh (s1 ++ s2) x) with ((fun s2 => listrep sh (s1 ++ s2) x) s2).
   apply wandQ_frame_elim.
Qed.

Lemma list_lseg_proof_by_tactic: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s1 x y |-- listrep sh (s1 ++ s2) x.
Proof.
  intros.
  solve_wandQ lseg.
  auto.
Qed.

End GeneralLseg.
End GeneralLseg.

Module LsegWandQFrame.

Definition lseg (sh: share) (contents: list int) (x z: val) : mpred :=
  ALL tcontents: list int, listrep sh tcontents z -* listrep sh (contents ++ tcontents) x.

Lemma singleton_lseg: forall sh (a: int) (x y: val),
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

Lemma singleton_lseg_proof_by_tactic: forall sh (a: int) (x y: val),
  field_at sh t_struct_list [StructField _head] (Vint a) x *
  field_at sh t_struct_list [StructField _tail] y x |--
  lseg sh [a] x y.
Proof.
  intros.
  solve_wandQ lseg.
  simpl listrep.
  Exists y.
  cancel.
Qed.

Lemma lseg_lseg: forall sh (s1 s2: list int) (x y z: val),
  lseg sh s2 y z * lseg sh s1 x y |-- lseg sh (s1 ++ s2) x z.
Proof. intros. apply (@GeneralLseg.lseg_lseg listrep). Qed.

Lemma list_lseg: forall sh (s1 s2: list int) (x y: val),
  listrep sh s2 y * lseg sh s1 x y |-- listrep sh (s1 ++ s2) x.
Proof. intros. apply (@GeneralLseg.list_lseg listrep). Qed.

End LsegWandQFrame.

Arguments listrep sh contents x : simpl never.

Module ListLib.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p <> nullval -> field_compatible t_struct_list [] p) /\ (p <> nullval -> isptr p)).
Proof.
  intros.
  destruct contents.
  + unfold listrep.
    entailer!.
  + unfold listrep; fold listrep.
    Intros y; entailer!.
    intros.
    rewrite field_compatible_cons in H.
    simpl in H.
    tauto.
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

End ListLib.

Definition listboxrep (sh: share) (contents: list int) (x: val) : mpred :=
  EX y: val, data_at sh (tptr t_struct_list) y x * listrep sh contents y.

Module LBsegWandQFrame.

Definition lbseg (sh: share) (contents: list int) (x z: val) : mpred :=
  ALL tcontents: list int, listboxrep sh tcontents z -* listboxrep sh (contents ++ tcontents) x.

Lemma singleton_lbseg: forall sh (a: int) (x y: val),
  data_at sh (tptr t_struct_list) y x * 
  field_at sh t_struct_list [StructField _head] (Vint a) y |--
  lbseg sh [a] x (field_address t_struct_list [StructField _tail] y).
Proof.
  intros.
  unfold lbseg.
  apply allp_right; intros.
  apply -> wand_sepcon_adjoint.
  simpl app.
  unfold listboxrep.
  Intros z.
  change (tptr t_struct_list) with (nested_field_type t_struct_list [StructField _tail]) at 2.
  rewrite <- field_at_data_at.
  unfold listrep at 2; fold listrep.
  Exists y z.
  cancel.
Qed.

Lemma lbseg_lbseg: forall sh (s1 s2: list int) (x y z: val),
  lbseg sh s2 y z * lbseg sh s1 x y |-- lbseg sh (s1 ++ s2) x z.
Proof. intros. apply (@GeneralLseg.lseg_lseg listboxrep). Qed.

Lemma listbox_lbseg: forall sh (s1 s2: list int) (x y: val),
  listboxrep sh s2 y * lbseg sh s1 x y |-- listboxrep sh (s1 ++ s2) x.
Proof. intros. apply (@GeneralLseg.list_lseg listboxrep). Qed.

End LBsegWandQFrame.

Arguments listboxrep sh contents x : simpl never.
