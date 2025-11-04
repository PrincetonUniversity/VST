From VST.typing Require Import typing.
Import env.

Section automation_tests.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.
  Open Scope printing_sugar.

  (* to programs.v *)
  Definition normal_type_assert R := {| T_normal := R; T_break := False; T_continue := False; T_return := λ _ _, False |}.

  Goal forall Espec ge f (_x:ident) (x:val),
  temp _x x
  ⊢ typed_stmt Espec ge (Sset _x (Ebinop Oadd (Econst_int (Int.repr 41) tint)
                                              (Econst_int (Int.repr 1) tint) tint)) f
                        (normal_type_assert (temp _x (Vint (Int.repr 42))
                                ∗ ⎡ Vint (Int.repr 42) ◁ᵥₐₗ|tint| 42 @ int tint ⎤)).
  Proof.
    iIntros.
    repeat liRStep.
    (* FIXME add these Integer facts to Lithium automation -- but where?
       Just adding them to lithium_rewrite doesn't do it. *)
    rewrite -Int.add_signed add_repr /= Int.signed_repr; last rep_lia.
    repeat liRStep.
    liShow.
    rewrite Int.signed_repr; last rep_lia.
    done.
  Qed.

  Goal forall Espec ge f (_x:ident) b (l:address) ty,
  TCDone (ty_has_op_type ty tint MCNone) ->
  ⊢ lvar _x tint b -∗
    ⎡ (b, Ptrofs.zero) ◁ₗ int tint ⎤ -∗
    typed_stmt Espec ge (Sassign (Evar _x tint) (Econst_int (Int.repr 1) tint)) f
               (normal_type_assert (⎡ (b, Ptrofs.zero) ◁ₗ Int.signed (Int.repr 1) @ int tint ⎤ ∗ True)).
  Proof.
    iIntros.
    repeat liRStep.
    Unshelve. constructor.
  Qed.

End automation_tests.

Transparent Archi.ptr64.

Section automation_tests.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

  Definition _ar : ident := $"ar".
  Definition _i : ident := $"i".
  Definition _j : ident := $"j".
  Definition _k : ident := $"k".
  Definition _main : ident := $"main".
  Definition _permute : ident := $"permute".
  Definition _t'1 : ident := 128%positive.

  Definition f_permute := {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := ((_ar, (tptr tint)) :: (_i, tint) :: (_j, tint) :: nil);
    fn_vars := nil;
    fn_temps := ((_k, tint) :: (_t'1, tint) :: nil);
    fn_body :=
  (Ssequence
    (Sset _k
      (Ederef
        (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _i tint) (tptr tint))
        tint))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _j tint)
              (tptr tint)) tint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _i tint)
              (tptr tint)) tint) (Etempvar _t'1 tint)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _j tint)
            (tptr tint)) tint) (Etempvar _k tint))))
  |}.

  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Goal forall Espec genv_t (v_k t'1: val) (v_ar v_i v_j:address) (i j: nat)  (elts:list Z) v1 v2 f,
    ⊢ ⎡ v_i ◁ᵥ| tint | i @ int tint ⎤ -∗
      ⎡ v_j ◁ᵥ| tint | j @ int tint⎤ -∗
      <affine> ⌜elts !! i = Some v1⌝ -∗
      <affine> ⌜elts !! j = Some v2⌝ -∗
      <affine> ⌜i ≠ j⌝ -∗
      temp _j v_j -∗
      temp _ar v_ar -∗
      temp _i v_i -∗
      temp _k v_k -∗
      temp _t'1 t'1 -∗
      ⎡v_ar ◁ₗ (array tint (elts `at_type` int tint))⎤ -∗
    typed_stmt Espec genv_t (fn_body f_permute) f (normal_type_assert (⎡(v_ar ◁ₗ (array tint (<[j:=v1]>(<[i:=v2]>elts) `at_type` int tint)))⎤ ∗ True)).
  Proof.
    intros.
    iStartProof.
    iIntros "#? #?".
    repeat liRStep.
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    Unshelve. all: try done; try constructor; try apply: inhabitant;  print_remaining_shelved_goal "permute".
  Qed.

End automation_tests.