(** Heavily annotated for a tutorial introduction. *)

(** First, import the entire Floyd proof automation system, which includes
 ** the VeriC program logic and the MSL theory of separation logic**)
Require Import VST.floyd.proofauto.

(** Import the [reverse.v] file, which is produced by CompCert's clightgen
 ** from reverse.c.   The file reverse.v defines abbreviations for identifiers
 ** (variable names, etc.) of the C program, such as _head, _reverse.
 ** It also defines "prog", which is the entire abstract syntax tree
 ** of the C program *)
Require Import VST.progs.reverse.

(* The C programming language has a special namespace for struct
** and union identifiers, e.g., "struct foo {...}".  Some type-based operators
** in the program logic need access to an interpretation of this namespace,
** i.e., the meaning of each struct-identifier such as "foo".  The next
** line (which looks identical for any program) builds this
** interpretation, called "CompSpecs" *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** Calculate the "types-of-global-variables" specification
 ** directly from the program *)
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** A convenience definition *)
Definition t_struct_list := Tstruct _list noattr.

(** Inductive definition of linked lists *)
Fixpoint listrep (sigma: list val) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (h,y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

(** Whenever you define a new spatial operator, such as
 ** [listrep] here, it's useful to populate two hint databases.
 ** The [saturate_local] hint is a lemma that extracts
 ** pure propositional facts from a spatial fact.
 ** The [valid_pointer] hint is a lemma that extracts a
 ** valid-pointer fact from a spatial lemma.
 **)

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

(** Specification of the [reverse] function.  It characterizes
 ** the precondition required for calling the function,
 ** and the postcondition guaranteed by the function.
 **)
Definition reverse_spec :=
 DECLARE _reverse
  WITH sigma : list val, p: val
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep sigma p)
  POST [ (tptr t_struct_list) ]
    EX q:val,
     PROP () LOCAL (temp ret_temp q)
     SEP (listrep(rev sigma) q).

(** The global function spec, characterizing the
 ** preconditions/postconditions of all the functions
 ** that your proved-correct program will call. 
 ** Normally you include all the functions here, but
 ** in this tutorial example we include only one. *)
Definition Gprog : funspecs :=
         ltac:(with_library prog [ reverse_spec ]).

(** For each function definition in the C program, prove that the
 ** function-body (in this case, f_reverse) satisfies its specification
 ** (in this case, reverse_spec).
 **)
Lemma body_reverse: semax_body Vprog Gprog
                                    f_reverse reverse_spec.
Proof.
(** The start_function tactic "opens up" a semax_body
 ** proof goal into a Hoare triple. *)
start_function.
(** For each assignment statement, "symbolically execute" it
 ** using the forward tactic *)
forward.  (* w = NULL; *)
forward.  (* v = p; *)
(** To prove a while-loop, you must supply a loop invariant,
 ** in this case (EX s1  PROP(...)LOCAL(...)(SEP(...)).  *)
forward_while
   (EX s1: list val, EX s2 : list val, 
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 v)).
(** The forward_while tactic leaves four subgoals,
 ** which we mark with * (the Coq "bullet") *)
* (* Prove that precondition implies loop invariant *)
Exists (@nil val) sigma nullval p.
entailer!.
unfold listrep.
entailer!.
* (* Prove that loop invariant implies typechecking of loop condition *)
entailer!.
* (* Prove that loop body preserves invariant *)
destruct s2 as [ | h r].
 - unfold listrep at 2. 
   Intros. subst. contradiction.
 - unfold listrep at 2; fold listrep.
   Intros y.
   forward. (* t = v->tail *)
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

(** See the file [progs/verif_reverse.v] for an alternate
 ** proof of this function, using a general theory of
 ** list segments.  That file also has proofs of the
 ** sumlist function, the main function, and the
 ** [semax_func] theorem that ties all the functions together
 **)

