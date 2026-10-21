From VST.typing Require Import typing.
From VST.typing Require Import automation_test_loop.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t04_loops.c]. *)
Section spec.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list Z) → type) → ((list Z) → type) := (λ self xs,
    ((xs <> []) @ (optional (&own (
      ∃ₜ (y : Z) (ys : list Z),
      constrained (struct _list_node [@{type}
        (y @ (int (tint))) ;
        (self (ys))
      ]) (
        ⌜xs = y :: ys⌝
      )
    )) (null)))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list Z)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (xs : (list Z)):
    (xs @ list_t)%I ≡@{type} (
      ((xs <> []) @ (optional (&own (
        ∃ₜ (y : Z) (ys : list Z),
        constrained (struct _list_node [@{type}
          (y @ (int (tint))) ;
          (ys @ list_t)
        ]) (
          ⌜xs = y :: ys⌝
        )
      )) (null)))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 list_t_rec). Qed.

  Definition list_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_place_inst_generated.
  Definition list_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_place_inst_generated.

  (* TODO check if this instance works with the addition of cty *)
  Definition list_t_simplify_hyp_val_inst_generated cty patt__ :=
    [instance simplify_hyp_val_eq cty _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_val_inst_generated.
  Definition list_t_simplify_goal_val_inst_generated cty patt__ :=
    [instance simplify_goal_val_eq cty _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  (* Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (tint))); True. *)

  (* Function [reverse_1] has been skipped. *)

  (* Specifications for function [reverse_2]. *)
  Definition type_of_reverse_2 :=
    fn(∀ xs : (list Z); (xs @ (list_t)); True)
      → ∃ () : (), ((rev xs) @ (list_t)); True.

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ (p, xs, ys) : address * (list Z) * (list Z); (p @ (&own (xs @ (list_t)))), (ys @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((xs ++ ys) @ (list_t))).

  (* Function [append_loop_1] has been skipped. *)

  (* Specifications for function [append_loop_2]. *)
  Definition type_of_append_loop_2 :=
    fn(∀ (p, xs, ys) : address * (list Z) * (list Z); (p @ (&own (xs @ (list_t)))), (ys @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((xs ++ ys) @ (list_t))).
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
