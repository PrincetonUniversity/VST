Require Import floyd.proofauto.
Require Import reverse_defs.
Local Open Scope logic.

(* Some sample entailments for testing our solvers on
   And helping to formulate useful hints. *)
(* from verif_summarray, Lemma body_sumarray *)
(* Goal forall _a _n _i _s _x,
   name _a ->
   name _n ->
   name _i ->
   name _s ->
   name _x ->
   forall (a0 : val) (sh : share) (contents : Z -> val) (size : Z),
   0 <= size <= Int.max_signed ->
   (forall i0 : Z, 0 <= i0 < size -> is_int (contents i0)) ->
   let Delta := abbreviate in
   PROP  ()
   LOCAL  (tc_environ Delta;
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint));
   `eq (eval_id _i) (eval_expr (Econst_int (Int.repr 0) tint));
   `(eq a0) (eval_id _a); `(eq (Vint (Int.repr size))) (eval_id _n);
   `isptr (eval_id _a))
   SEP  (`(array_at tint sh contents 0 size) (eval_id _a))
   |-- PROP  (0 <= 0 <= size)
       LOCAL  (`(eq a0) (eval_id _a); `(eq (Vint (Int.repr 0))) (eval_id _i);
       `(eq (Vint (Int.repr size))) (eval_id _n); `isptr (eval_id _a);
       `(eq (Vint (fold_range (add_elem contents) Int.zero 0 0)))
         (eval_id _s))
       SEP  (`(array_at tint sh contents 0 size) (eval_id _a)). *)

(* scraped from entailer.v tactics *)


(* verif_reverse *)
(* from body_reverse *)
(* we need to have a way of autogenerating the lemmas... *)
Lemma body_reverse_fact :
   name _p ->
   name _v ->
   name _w ->
   name _t ->
   forall (sh : share) (contents : list val),
   writable_share sh ->
   PROP  ()
   LOCAL  (tc_environ Delta;
   `eq (eval_id _v) (eval_expr (Etempvar _p (tptr t_struct_list)));
   `eq (eval_id _w)
     (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
   SEP  (`(lseg LS sh contents) (eval_id _p) `nullval)
   |-- PROP  (contents = rev nil ++ contents)
       LOCAL ()
       SEP  (`(lseg LS sh nil) (eval_id _w) `nullval;
       `(lseg LS sh contents) (eval_id _v) `nullval).
ungather_entail.


(* things that are equal |--  *)

(* *)