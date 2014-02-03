Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Require Import reify_derives.
Require Import MirrorShard.ReifySepExpr.
Require Import MirrorShard.ReifyExpr.
Require Import reverse_defs.
Local Open Scope logic.


Goal forall n contents,
`(map Vint contents) = n.
intros.
fold_dependent.
repeat rewrite distribute_lift.
Admitted.

Lemma while_entail1 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
   PROP  ()
   LOCAL 
   (tc_environ
      Delta;
   `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list))
);
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
   SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
   |-- PROP  ()
       LOCAL 
       (`(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
          (eval_id _s))
       SEP  (TT; `(lseg LS sh (map Vint contents)) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
pose_env.
reify_derives.
Admitted.