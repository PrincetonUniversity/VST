(********************************************)
(*                Hpattern 1.0              *)
(*              Chung-Kil Hur               *)
(*                  MPI-SWS                 *)
(********************************************)

Set Implicit Arguments.

(** Internal Use: hresolve_pre, hresove_post, hresolve_constr *)

Definition hresolve_arg (A:Type) (a:A) := True.

Ltac hresolve_pre C T tac_resolve :=
 (let hT := fresh "_temp_" in
    assert (hT : hresolve_arg T) by (exact I);
  let hx := fresh "hx" in
    set (hx := C) in hT;
    lazymatch goal with [ _ : @hresolve_arg _ ?T' |- _ ] => tac_resolve hx T' end;
    clear hT ;
  let hf := fresh "hf" in
    intro hf).

Ltac hresolve_post tac :=
 (lazymatch goal with [ hf := ?T' |- _ ] => clear hf;
    lazymatch goal with [ hx := _ |- _ ] => tac T' hx; try (clear hx) end
  end).

Tactic Notation "hresolve_constr" constr(C) "at" int_or_var(occ) "in" constr(T) :=
  hresolve_pre C T ltac:(fun hx T' => hresolve_core (hx := C) at occ in T').

Tactic Notation "hresolve_constr" constr(C) "in" constr(T) :=
  hresolve_pre C T ltac:(fun hx T' => hresolve_core (hx := C) in T').

(** get_concl and get_type *)

Ltac get_concl := lazymatch goal with [ |- ?G ] => G end.

Ltac get_hyp H := match goal with [ Hcrr : ?G |- _ ] => match Hcrr with H => G end end.

Tactic Notation "hresolve" constr(C) "at" int_or_var(occ) :=
 (let G := get_concl in hresolve_constr C at occ in G; hresolve_post ltac:(fun G' hx => change G')).

Tactic Notation "hresolve" constr(C) :=
 (let G := get_concl in hresolve_constr C in G; hresolve_post ltac:(fun G' hx => change G')).

Tactic Notation "hresolve" constr(C) "at" int_or_var(occ) "in" hyp(H) :=
 (let G := get_hyp H in hresolve_constr C at occ in G; hresolve_post ltac:(fun G' hx => change G' in H)).

Tactic Notation "hresolve" constr(C) "in" hyp(H) :=
 (let G := get_hyp H in hresolve_constr C in G; hresolve_post ltac:(fun G' hx => change G' in H)).

(**
   [*] hpattern C ( at occ ) ( in H )

   the same as pattern, but abstracts the occ-th and its dependent occurrencies of C in the conclusion (or in the hypothesis H).
*)

Tactic Notation "hpattern" constr(C) "at" int_or_var(occ) :=
 (let G := get_concl in hresolve_constr C at occ in G; hresolve_post ltac:(fun G' hx => change G'; pattern hx; change hx with C)).

Tactic Notation "hpattern" constr(C) :=
 (let G := get_concl in hresolve_constr C in G; hresolve_post ltac:(fun G' hx => change G'; pattern hx; change hx with C)).

Tactic Notation "hpattern" constr(C) "at" int_or_var(occ) "in" hyp(H) :=
 (let G := get_hyp H in hresolve_constr C at occ in G; hresolve_post ltac:(fun G' hx => change G' in H; pattern hx in H; change hx with C in H)).

Tactic Notation "hpattern" constr(C) "in" hyp(H) :=
 (let G := get_hyp H in hresolve_constr C in G; hresolve_post ltac:(fun G' hx => change G' in H; pattern hx in H; change hx with C in H)).

(**
  [*] hgeneralize C ( at occ ) as id

  generalizes the occ-th and its dependent occurrences of C
*)

Tactic Notation "hgeneralize" constr(C) "at" int_or_var(occ) "as" ident(id) :=
 (let G := get_concl in hresolve_constr C at occ in G; hresolve_post ltac:(fun G' hx => change G'; generalize hx as id)).

Tactic Notation "hgeneralize" constr(C) "as" ident(id) :=
 (let G := get_concl in hresolve_constr C in G; hresolve_post ltac:(fun G' hx => change G'; generalize hx as id)).

Tactic Notation "hgeneralize_simpl" constr(C) "at" int_or_var(occ) "as" ident(id) :=
 (hgeneralize C at occ as id; intro; lazymatch goal with [ H : _ |- _ ] => simpl in H; revert H end).

Tactic Notation "hgeneralize_simpl" constr(C) "as" ident(id) :=
 (hgeneralize C as id; intro; lazymatch goal with [ H : _ |- _ ] => simpl in H; revert H end).

(**
   [*] hrewrite ( <- ) eqn ( at occ )

   rewrites the occ-th and its dependent occurrences of lhs of eqn to rhs of eqn
*)

Ltac hrewrite_with eqn tac_res :=
 (lazymatch (type of eqn) with @eq _ ?X ?Y =>
    let G := get_concl in
      tac_res X G;
      hresolve_post ltac:(fun G' hx =>
        change G'; let Heqn := fresh "_temp_" in assert (Heqn : hx = Y) by (apply eqn); rewrite Heqn; clear Heqn)
  end).

Tactic Notation "hrewrite" constr(eqn) "at" int_or_var(occ) :=
  hrewrite_with eqn ltac:(fun X G => hresolve_constr X at occ in G).

Tactic Notation "hrewrite" "<-" constr(eqn) "at" int_or_var(occ) := (hrewrite (sym_eq eqn) at occ).

Tactic Notation "hrewrite" constr(eqn) :=
  hrewrite_with eqn ltac:(fun X G => hresolve_constr X in G).

Tactic Notation "hrewrite" "<-" constr(eqn) := (hrewrite (sym_eq eqn)).

