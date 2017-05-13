Require Import floyd.proofauto.
Require Import wand_demo.list.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs => field_at sh t_struct_list [StructField _head] h x *
              EX y:val,
                field_at sh t_struct_list [StructField _tail] y x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Module list_head.

Lemma wf_intro_list_head: forall sh (x y: val) (s: list val) (l: val):
listrep sh (x :: s) l
  |-- field_at sh t_struct_list [StructField _head] x l *
      (field_at sh t_struct_list [StructField _head] y l -* listrep sh (y :: s) l).
(*
Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
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
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.
*)
