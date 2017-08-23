Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.sumarray. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(* Some definitions relating to the functional spec of this particular program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
                     Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a).

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [sumarray_spec; main_spec]).

(* Loop invariant, for use in body_sumarray.  *)
Definition sumarray_Inv a0 sh contents size :=
 EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (temp _a a0;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a0).

(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.  (* Always do this at the beginning of a semax_body proof *)
(* The next two lines do forward symbolic execution through
   the first two executable statements of the function body *)
forward.  (* i = 0; *)
forward.  (* s = 0; *)
(* To do symbolic execution through a [while] loop, we must
 * provide a loop invariant, so we use [forward_while] with
 * the invariant as an argument .*)
forward_while (sumarray_Inv a sh contents size).
(* forward_while leaves four subgoals; here we label them
   with the * bullet. *)
* (* Prove that current precondition implies loop invariant *)
Exists 0.   (* Instantiate the existential on the right-side of |--   *)
entailer!.  (* Simplify this entailment as much as possible; in this
      case, it solves entirely; in other cases, entailer! leaves subgoals *)
* (* Prove that loop invariant implies typechecking condition *)
entailer!.  (* Typechecking conditions usually solve quite easily *)
* (* Prove postcondition of loop body implies loop invariant *)
(* In order to get to the postcondition of the loop body, of course,
   we must forward-symbolic-execute through the loop body;
   so we start that here. *)
(* "forward" fails and tells us to first make (0 <= i < Zlength contents)
   provable by auto, so we assert the following: *)
assert_PROP (Zlength contents = size). {
  entailer!. do 2 rewrite Zlength_map. reflexivity.
}

forward. (* x = a[i] *)
forward. (* s += x; *)
forward. (* i++; *)
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
 Exists (i+1).
 entailer!.
 clear - H HRE H1.
 f_equal. f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite sum_Z_app. rewrite (sublist_one i) with (d:=0) by omega.
 simpl. rewrite Z.add_0_r. reflexivity.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
autorewrite with sublist in *.
autorewrite with sublist.
reflexivity.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.
forward_call (*  s = sumarray(four,4); *)
  (four,Ews,four_contents,4).
 split3; auto. computable.
 repeat constructor; computable.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.

