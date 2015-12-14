Require Import floyd.proofauto. (* Import the Verifiable C system *)
Require Import progs.sumarray. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition sum_int := fold_right Int.add Int.zero.
  
Lemma sum_int_app:
  forall a b, sum_int (a++b) = Int.add (sum_int a) (sum_int b).
Proof.
intros.
induction a; simpl. rewrite Int.add_zero_l; auto.
rewrite IHa. rewrite Int.add_assoc. auto.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tint size) (map Vint contents) a)
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (sum_int contents)))
           SEP (data_at sh (tarray tint size) (map Vint contents) a).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

(* Packaging the API spec all together. *)
Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil. 
Definition Gprog : funspecs := sumarray_spec :: main_spec::nil.

(* Loop invariant, for use in body_sumarray.  *)
Definition sumarray_Inv a sh contents size := 
 (EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (temp _a a; 
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (sum_int (sublist 0 i contents))))
   SEP   (data_at sh (tarray tint size) (map Vint contents) a))%assert.

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
forward. (* x = a[i] *)
entailer!. (* This is an example of a typechecking condition 
   that is nontrivial; entailer! leaves a subgoal.  The subgoal basically
   says that the array-subscript index is in range;  not just in 
   the bounds of the array, but in the _initialized_ portion of the array.*)
   rewrite Znth_map with (d':=Int.zero). hnf; auto.
  rewrite Zlength_map in *; omega.
forward. (* s += x; *)
forward. (* i++; *)
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the 
   postcondition of the loop body) entails the loop invariant. *)
 Exists (Zsucc i).
 entailer!.
 rewrite Zlength_map in *.
 rewrite Znth_map with (d':=Int.zero) by omega.
 simpl. f_equal.
 rewrite (sublist_split 0 i (Z.succ i)) by omega.
 rewrite sum_int_app. f_equal.
 rewrite sublist_one with (d:=Int.zero) by omega.
 simpl. rewrite Int.add_zero. reflexivity.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
rewrite Zlength_map in *.
autorewrite with sublist.
reflexivity.
Qed.


(* Contents of the extern global initialized array "_four" *)
Definition four_contents := map Int.repr [1;2;3;4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.
forward_call (*  r = sumarray(four,4); *)
  (four,Ews,four_contents,4).
 split; auto. computable. 
Intros vret.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_sumarray.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

