Require Import floyd.proofauto.
Require Import progs.reverse.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list val) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (h,y) x  *  listrep hs y
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
  WITH sigma : list val, p: val
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep sigma p)
  POST [ (tptr t_struct_list) ]
    EX p:val,
     PROP () LOCAL (temp ret_temp p)
     SEP (listrep(rev sigma) p).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ reverse_spec ]).

Lemma body_reverse: semax_body Vprog Gprog
                                    f_reverse reverse_spec.
Proof.
start_function.
forward.  (* w = NULL; *)
forward.  (* v = p; *)
forward_while
   (EX s1: list val, EX s2 : list val, 
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 v)).
* (* precondition implies loop invariant *)
Exists (@nil val) sigma nullval p.
entailer!.
unfold listrep.
entailer!.
* (* loop invariant implies typechecking of loop condition *)
entailer!.
* (* loop body preserves invariant *)
destruct s2 as [ | h r].
 - unfold listrep at 2. 
   Intros. subst. contradiction.
 - unfold listrep at 2; fold listrep.
   Intros y.
   forward. (* h = v->tail *)
   forward. (* v->tail = w; *)
   forward. (* w = v; *)
   forward. (* v = t; *)
   (* At end of loop body; reestablish invariant *)
   entailer!.
   Exists (h::s1,r,v,y).
   entailer!.
   + simpl. rewrite app_ass. auto.
   + unfold listrep at 3; fold listrep.
     Exists w. entailer!.
* (* after the loop *)
forward.  (* return w; *)
Exists w; entailer!.
rewrite (proj1 H1) by auto.
unfold listrep at 2; fold listrep.
entailer!.
rewrite <- app_nil_end, rev_involutive.
auto.
Qed.
