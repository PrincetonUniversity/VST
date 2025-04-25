Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.sumarray2. (* Import the AST of this C program *)

(* The next line is "boilerplate", always required after importing an AST. *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; lia.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ tptr tuint, tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed)
          PARAMS (a; Vint (Int.repr size))
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () RETURN (Vint (Int.repr (sum_Z contents)))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(* The precondition of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     PROP() 
     RETURN (Vint (Int.repr (3+4))) 
     SEP(TT).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [sumarray_spec; main_spec]).

(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.  (* Always do this at the beginning of a semax_body proof *)
(* The next two lines do forward symbolic execution through
   the first two executable statements of the function body *)
forward.  (* s = 0; *)
forward_for_simple_bound size
  (EX i: Z,
   PROP  ((*0 <= i <= size*))
   LOCAL (temp _a a;
          (*temp _i (Vint (Int.repr i)); *)
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a))%assert.

* (* Prove that current precondition implies loop invariant *)
entailer!.
* (* Prove postcondition of loop body implies loop invariant *)
(* "forward" fails and tells us to first make (0 <= i < Zlength contents)
   provable by auto, so we assert the following: *)
assert_PROP (Zlength contents = size). {
  entailer!. do 2 rewrite Zlength_map. reflexivity.
}
forward. (* x = a[i] *)
forward. (* s += x; *)
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
entailer!.
 f_equal. f_equal.
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite sum_Z_app. rewrite (sublist_one i) by lia.
 simpl. lia.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
autorewrite with sublist in *.
reflexivity.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma Forall_sublist: forall {A} (P: A->Prop) lo hi (al: list A),
  Forall P al -> Forall P (sublist lo hi al).
Proof.
intros.
apply Forall_forall. rewrite -> Forall_forall in H.
intros.
apply H; auto.
apply sublist_In in H0. auto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
set (four := gv _four).
change [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4] with (map Int.repr four_contents).
set (contents :=  map Vint (map Int.repr four_contents)).
assert (Zlength contents = 4) by (subst contents; reflexivity).
assert_PROP (field_compatible (tarray tuint 4) [] four) by entailer!.
assert (Forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) four_contents)
  by (repeat constructor; computable).
 rewrite <- (sublist_same 0 4 contents), (sublist_split 0 2 4)
    by now autorewrite with sublist.
erewrite (split2_data_at_Tarray_app 2 4); try apply JMeq_refl; auto; try lia; try reflexivity.
Intros.
forward_call (*  s = sumarray(four+2,2); *)
  (field_address0 (tarray tuint 4) [ArraySubsc 2] four, Ews,
    sublist 2 4 four_contents,2).
  gather_SEP (data_at Ews (tarray tuint 2) (sublist 0 2 contents) _) 
                   (data_at Ews (tarray tuint 2) (map Vint _) _).
  erewrite <- (split2_data_at_Tarray_app 2 4); try apply JMeq_refl; auto; try lia; try reflexivity.
  rewrite <- !sublist_map. fold contents. autorewrite with sublist.
  rewrite (sublist_same 0 4) by auto.
  forward. (* return *)
Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.

(**  Here begins an alternate proof of the "for" loop.
  Instead of using forward_for_simple_bound, we use the 
  general-case loop tactic, forward_for.

To understand this verification, let's take the program,

  int sumarray(int a[], int n) {
     int i,s,x;
     s=0;
     for (i=0; i<n; i++) {
       x = a[i];
       s += x;
     }
     return s;
  }

and annotate with assertions:


  int sumarray(int a[], int n) {
     int i,s,x;
     s=0;
     for (i=0; i<n; i++) {
       assert (sumarray_Inv(i));
       x = a[i];
       s += x;
       assert (sumarray_PostBody(i));
     }
     return s;
  }

The assertions are defined in these definitions:
*)

Definition sumarray_Inv a sh contents size i :=
   PROP  (0 <= i <= size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

Definition sumarray_PostBody a sh contents size i :=
    PROP  (0 <= i < size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 (i+1) contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(* . . . and now you can see how these assertions are used
   in the proof, using the semax_loop rule. *)

Lemma body_sumarray_alt: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.  (* Always do this at the beginning of a semax_body proof *)
forward.  (* s = 0; *)
forward_for (sumarray_Inv a sh contents size).
* (* initializer establishes precondition *)
forward. (* i=0; *)
unfold sumarray_Inv. Exists 0. entailer!.
* (* loop-test expression typechecks *)
entailer!.
*
rename x into i.
assert_PROP (size=Zlength contents)
  by (entailer!; autorewrite with sublist; auto).
forward. (* x = a[i]; *)
forward. (* s += x; *)
forward.  (* i++; *)
Exists (i+1).
entailer!.
     f_equal. f_equal.
     rewrite (sublist_split 0 i (i+1)) by lia.
     rewrite sum_Z_app. rewrite (sublist_one i) by lia.
     simpl. autorewrite with sublist norm. reflexivity.
* (* after the loop *)
forward. (* return s; *)
autorewrite with sublist in *.
autorewrite with sublist.
entailer!.
Qed.
