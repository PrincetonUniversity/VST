From lithium Require Import hooks.
From refinedc.typing Require Import typing.

Ltac sidecond_hook ::= match goal with |- _ => idtac "SIDECOND" end.
Ltac unsolved_sidecond_hook := match goal with |- _ => idtac "UNSOLVEDSIDECOND" end.
Ltac unfold_instantiated_evar_hook H ::= idtac "EVAR".

Ltac select_smaller_option o1 o2 H1 H2 cont :=
  match o1 with
  | None => cont o2 H2
  | Some ?n1 =>
    match o2 with
    | None => cont o1 H1
    | Some ?n2 =>
      first [
          assert_succeeds (assert (n1 ≤ n2)%N as _ by lia);
          cont o1 H1
        |
        cont o2 H2
        ]
    end
  end.

Ltac liExtensible_hook ::=
  let unfold_instance G := G in
      (* eval unfold typed_un_op_val, subsume_place, simplify_goal_place, simplify_hyp_place, simplify_goal_val, simplify_hyp_val, subsume_val, subsume_place, typed_bin_op_val in G in *)
  let rec get_head e :=
  match e with
  | ?h _ => get_head constr:(h)
  | _    => constr:(e)
  end in
  match goal with
  | |- environments.envs_entails _ (i2p_P ?G) =>
    (* No idea why this is necessary here. *)
    let G := unfold_instance G in
    lazymatch G with
    | @subsume_simplify_inst _ _ _ ?o1 ?o2 ?H1 ?H2 _ _ =>
      select_smaller_option o1 o2 H1 H2 ltac:(fun _ used =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used)
    (* | @simple_subsume_place_to_subsume_inst _ _ _ _ _ _ _ ?used _ => *)
    (*   let used := unfold_instance used in *)
    (*   let used := get_head used in *)
    (*   idtac "EXTENSIBLE" used *)
    | @typed_binop_simplify_inst _ _ _ _ _ _ ?o1 ?o2 _ _ ?H1 ?H2 _ _ _ =>
      select_smaller_option o1 o2 H1 H2 ltac:(fun _ used =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used)
    | @typed_unop_simplify_inst _ _ _ _ _ _ ?used _ _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_place_simpl_inst _ _ _ _ _ _ _ ?used _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_write_end_simpl_inst _ _ _ _ _ _ _ _ _ _ ?used _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_read_end_simpl_inst _ _ _ _ _ _ _ _ ?used _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_annot_expr_simplify_inst _ _ _ _ _ _ _ _ ?used _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_annot_stmt_simplify_inst _ _ _ _ _ _ _ ?used _ =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used
    | @typed_cas_simplify_inst _ _ _ _ _ _ _ _ _ ?o1 ?o2 ?o3 ?H1 ?H2 ?H3 _ _ =>
      select_smaller_option o1 o2 H1 H2 ltac:(fun o' H' =>
      select_smaller_option o' o3 H' H3 ltac:(fun _ used =>
      let used := unfold_instance used in
      let used := get_head used in
      idtac "EXTENSIBLE" used))
    | _ =>
      let G := unfold_instance G in
      let G := get_head G in
      idtac "EXTENSIBLE" G
    end
  end.
