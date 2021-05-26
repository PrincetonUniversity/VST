Require Import VST.floyd.proofauto.
Require Import VST.progs.list_dt. Import LsegSpecial.
Require Import VST.progs.append.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance LS: listspec _list _tail (fun _ _ => emp).
Proof. eapply mk_listspec; reflexivity. Defined.
Definition t_struct_list := Tstruct _list noattr.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Definition append_spec :=
 DECLARE _append
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ tptr t_struct_list, tptr t_struct_list]
     PROP(writable_share sh)
     PARAMS (x;y) GLOBALS()
     SEP (lseg LS sh s1 x nullval; lseg LS sh s2 y nullval)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (lseg LS sh (s1++s2) r nullval).

Definition Gprog : funspecs :=   ltac:(with_library prog [ append_spec ]).

Lemma ENTAIL_refl: forall Delta P, ENTAIL Delta, P |-- P.
Proof. intros; apply andp_left2; auto. Qed.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if.
*
 forward.
 Exists y.
 simpl app.
 entailer!.
*
 forward.
 apply semax_lseg_nonnull; [ | intros a s3 u ? ?].
 entailer!.
 apply is_pointer_or_null_not_null; auto.
 forward.
 simpl valinject.
 forward_while
      (EX s1a: list val, EX s1b: list val, EX t: val, EX u: val, EX a: val,
            PROP (s1 = s1a ++ a :: s1b)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg LS sh s1a x t;
                   list_cell LS sh a t;
                   field_at sh list_struct [StructField _tail] u t;
                   lseg LS sh s1b u nullval;
                   lseg LS sh s2 y nullval))%assert.
 + Exists (@nil val) s3 x u a.  entailer.
 + entailer!.
 + clear u H1; rename u0 into u. clear a s3 H0. rename a0 into a.
   gather_SEP (list_cell _ _ _ _) (field_at _ _ _ _ _) (lseg _ _ _ x _) (lseg _ _ _ u _).
   replace_SEP 0 (lseg LS sh (s1a++[a]) x u * lseg LS sh s1b u nullval)%logic.
   entailer.
   rewrite <- (emp_sepcon (list_cell LS sh a t)).
   apply (lseg_cons_right_list LS); auto.
   Intros. gather_SEP (lseg _ _ _ u _).
   apply semax_lseg_nonnull; [ | intros a1 s4 u2 ? ?].
   entailer!.
   apply is_pointer_or_null_not_null; auto.
   simpl valinject.
   forward.
   forward.
   subst s1b. subst s1.
  Exists (s1a++[a],s4,u,u2,a1).  simpl fst; simpl snd. entailer!.
  rewrite app_ass. reflexivity.
 +
    clear a s3 H0. subst u0. rewrite lseg_eq by reflexivity. Intros. subst s1 s1b.
    forward.
    forward.
    Exists x. entailer!.
    apply derives_trans with (lseg LS sh (s1a++[a0]) x y * lseg LS sh s2 y nullval)%logic.
    eapply derives_trans; [ | apply (lseg_cons_right_list LS) with (y:=t)]; auto.
    simpl valinject.
    cancel.
   apply (list_append_null LS).
Qed.
