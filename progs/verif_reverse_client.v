Require Import VST.floyd.proofauto.
Require Import VST.progs.reverse_client.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list int) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint h,y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Definition reverse_spec :=
 DECLARE _reverse
  WITH sigma : list int, p: val
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep sigma p)
  POST [ (tptr t_struct_list) ]
    EX q:val,
     PROP () LOCAL (temp ret_temp q)
     SEP (listrep (rev sigma) q).

Definition last_foo_spec :=
 DECLARE _last_foo
  WITH sigma : list int, p: val, sigma': list int, x: int
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP (sigma = sigma' ++ x :: nil)
     LOCAL (temp _p p)
     SEP (listrep sigma p)
  POST [ tuint ]
     PROP () LOCAL (temp ret_temp (Vint x))
     SEP (TT).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ reverse_spec; last_foo_spec ]).

Lemma body_last_foo: semax_body Vprog Gprog
                                    f_last_foo last_foo_spec.
Proof.
  start_function.
  subst sigma.
  forward_call (sigma' ++ [x], p). (* p = reverse (p); *)
  Intros p'.
  rewrite rev_app_distr; simpl.
  unfold listrep; fold listrep.
  Intros q.
  forward. (* res = p -> head; *)
  forward. (* return res; *)
Qed.
