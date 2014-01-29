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



Goal forall  contents rho,
tc_environ Delta rho ->
emp |-- !!True &&
       (!!(Vint (Int.sub (sum_int contents) (sum_int contents)) =
           eval_id _s rho /\ True)) && emp.
Proof.
intros.
pose_env.
prepare_reify.
reify_derives.
Admitted.

Goal forall sh contents rho,
tc_environ Delta rho ->
emp |-- 
 (lseg LS sh (map Vint contents) (eval_id _t rho) nullval * emp).
Proof.
intros.
pose_env.
reify_derives.
Admitted.

Goal
emp * emp |-- emp.
Proof.
intros.
pose_env.
reify_derives.

Goal forall rho,
tc_environ Delta rho ->
emp |-- !!True * emp.
Proof.
intros.
pose_env.
reify_derives.
Admitted.


Definition p (d:nat) : mpred:= emp.
Goal emp |-- emp.
pose_env.
reify_derives.
Admitted.

Goal p O |-- emp.
pose_env.
reify_derives.
simpl.
Admitted.

Goal forall n contents,
`(map Vint contents) = n.
intros.
fold_dependent.
repeat rewrite distribute_lift.
Admitted.



Goal forall rho sh contents, 
True ->
(lseg LS sh (map Vint contents) (eval_id _p rho) nullval) |-- emp.
Proof.
intros.
pose_env.
reify_derives. 
Admitted.


Goal forall rho ,
   (!!(eval_id _t rho = eval_id _p rho) && emp) |-- emp.
Proof.
intros.
pose_env. 
reify_derives.
Admitted.


Goal forall sh contents rho,
tc_environ Delta rho -> !!True &&
   (!!(eval_id _t rho = eval_id _p rho /\
       eval_id _s rho = Vint (Int.repr 0) /\ True) && 
   (lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp)) |-- emp.
Proof.
intros.
pose_env.
reify_derives.
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