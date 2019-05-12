(*  This file demonstrates loop verifications using two advanced techniques:
   1. Converting for-loop into while-loop
   2. Peeling off the first iteration of a loop.

  The function verified is this one, which computes integer square roots:

     int f (int b) {
       int i, a;
       for (i=b+1; i*i>b; i--) {
         a=i;
       }
       return a;
     }

Notice that the variable [a] is uninitialized until the middle of the first iteration, 
  _and_  it should be mentioned in the loop invariant.  How should this be handled?
 Let's see . . .
*)

Require Import VST.floyd.proofauto.
Require Import VST.progs.peel.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition f_spec : ident * funspec :=
 DECLARE _f
  WITH b: Z
  PRE [ _a OF tint ]
          PROP  (0 <= b; (b+1)*(b+1) < Int.max_signed)
          LOCAL (temp _b (Vint (Int.repr b)))
          SEP   ()
  POST [ tuint ]
        EX a:Z, 
        PROP ((a-1)*(a-1)<=b /\ a*a>b)
        LOCAL(temp ret_temp  (Vint (Int.repr a)))
           SEP ().

Definition Gprog : funspecs :=
        ltac:(with_library prog [f_spec ]).

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
(* First: some preliminary arithmetic assertions. *)
assert (0 <= b <= b*b). {
   split; auto.
   destruct (zeq b 0). subst. omega.
   rewrite <- Z.mul_1_l at 1.
   apply Zmult_le_compat_r;  rep_omega.
}
assert (b*b <= (b+1)*(b+1) < Int.max_signed). {
  split; auto.
  apply Z.square_le_mono_nonneg; omega.
}
clear H H0.
(* Next:  We have a for-loop here.  For ease of reasoning, let's convert it
   to a while loop, which is easy with this tactic: *)
apply semax_convert_for_while'; [reflexivity .. | ].
forward.  (*  i = b+1; *)
normalize.
(* Now comes the interesting part.  What should the loop invariant be?
  AFTER the first iteration, this invariant will work:
      (EX i:Z, PROP (0 <= i <= b+1; b < (i+1)*(i+1))
             LOCAL(temp _i (Vint (Int.repr i)); temp _b (Vint (Int.repr b)); temp _a (Vint (Int.repr (i+1))))
             SEP())
  But this does not hold before the first iteration.  

  A more general invariant would be either of these, 
   but they don't quite work in Verifiable C.  

   EX i:Z, EX a: val,
             PROP (0 <= i <= Int.max_signed; b < (i+1)*(i+1) <= Int.max_signed;
                       (i=b+1)%Z \/ (a=Vint (Int.repr (i+1))))
             LOCAL(temp _i (Vint (Int.repr i)); temp _b (Vint (Int.repr b)); temp _a a)
             SEP().
   The problem with this one is that the initial value of variable _a is Vundef, 
   and the declaration (LOCAL (temp _a ...)) requires that _a have a defined value.

   (PROP ()
             LOCAL(temp _i (Vint (Int.repr (b+1))); temp _b (Vint (Int.repr b)))
             SEP()) ||
   (EX i:Z, PROP (0 <= i <= Int.max_signed; b < (i+1)*(i+1) <= Int.max_signed)
             LOCAL(temp _i (Vint (Int.repr i)); temp _b (Vint (Int.repr b)); temp _a (Vint (Int.repr (i+1))))
             SEP()).
   The problem with this one is that forward_while requires that the loop 
   invariant be in (existentially quantified) canonical form, but this is the disjunction
   of two (existentially quantified) canonical forms, which is not canonical.

   The underlying program logic (semax_while rule, etc.) is expressive enough
    to handle assertions and invariants not in canonical form, but the Floyd
    tactical machinery in forward_while requires canonical form.

    So, there's no loop invariant that works in VST.
    
    The solution is to peel off the first iteration; that is, prove the loop 
        while (i*i>b) {a=i; i--}
    as if it were,
        if (i*i>b) then {a=i; i--; while (i*i>b) {a=i; i--}}

    We do that as follows.  First, apply a postcondition to the entire loop,
    using forward_seq:
*)
forward_seq (EX a:Z,  PROP ((a-1)*(a-1)<=b /\ a*a>b)
                     LOCAL(temp _a (Vint (Int.repr a)))
                     SEP ()).
(*  Then, peel off the first iteration: *)
eapply semax_while_peel.
(* Now the rest is straightforward. *)
-
 forward_if.
 forward.
 forward.
 apply ENTAIL_refl.
 rewrite Z.mul_add_distr_r, Z.mul_add_distr_l in *; omega.
-
 forward_while (EX i:Z, PROP (0 <= i <= b+1; b < (i+1)*(i+1))
             LOCAL(temp _i (Vint (Int.repr i)); temp _b (Vint (Int.repr b)); temp _a (Vint (Int.repr (i+1))))
             SEP()).
 *
  Exists b; entailer!.
  split.
  rewrite Z.mul_add_distr_r, Z.mul_add_distr_l in *; omega.
  f_equal; f_equal; omega.
 *
   entailer!.
   split. 
   pose proof (Z.square_nonneg i). rep_omega.
   assert (i*i <= (b+1)*(b+1)) by (apply Z.square_le_mono_nonneg; omega).
   omega.
 *
   forward.
   forward.
   Exists (i-1).
   entailer!.
   rewrite Z.sub_add. split; auto. split; try omega.
   destruct (zeq i 0); try omega. subst.
   rewrite Int.signed_repr in HRE by rep_omega. omega.
   split; auto.
   assert (i*i <= (b+1)*(b+1)) by (apply Z.square_le_mono_nonneg; omega).
   pose proof (Z.square_nonneg i).
   rewrite Int.signed_repr in HRE by rep_omega.
   omega.
 *
   forward.
   Exists (i+1).
   entailer!.
   rewrite Z.add_simpl_r.
   assert (i*i <= (b+1)*(b+1)) by (apply Z.square_le_mono_nonneg; omega).
   pose proof (Z.square_nonneg i).
   rewrite Int.signed_repr in HRE by rep_omega.
   rewrite Z.mul_add_distr_r, Z.mul_add_distr_l in *.
   omega.
-
abbreviate_semax.
Intros a.
forward.
Exists a.
entailer!.
Qed.
