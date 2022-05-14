From Ltac2 Require Import Ltac2.

Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.entailer.
Require Import VST.floyd.forward. (* must come after entailer because of Ltac override *)
Require Import VST.floyd.deadvars.
Require Import VST.floyd.step.
Require Import VST.floyd.fastforward.

(* Things that we always want to simpl *)

Ltac2 mutable simpl_safe_list () : constr list := [
  'projT1; 'andb; 'orb
].

Ltac2 simpl_safe () :=
  List.iter (fun c => ltac1:(c |- simpl c) (Ltac1.of_constr c)) (simpl_safe_list ()).

Ltac simpl_safe := ltac2:(simpl_safe ()).

(* simpl within the individual terms of an entailment *)

Ltac2 rec simpl_entailment_aux (part : constr) :=
  lazy_match! part with
  | andp ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | orp ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | imp ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | sepcon ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | wand ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | ewand ?a ?b => simpl_entailment_aux a; simpl_entailment_aux b
  | exp _ => ()
  | allp _ => ()
  | _ =>
    let p := Fresh.in_goal @part in
    set (p := $part);
    simpl in p;
    subst p
  end.

Ltac2 simpl_entailment () := Control.enter (fun () =>
  lazy_match! goal with
  | [ |- ?pre |-- ?post ] =>
    simpl_entailment_aux pre;
    simpl_entailment_aux post
  end).

Ltac simpl_entailment := ltac2:(simpl_entailment ()).

Ltac2 mutable decisive_values_list () : constr list := [
  'true; 'false; 'nullval
].

Ltac2 subst_decisives () := Control.enter (fun () =>
  List.iter (fun c =>
    repeat (
      match! goal with
      | [ h : ?x = ?y |- _ ] =>
        match Constr.equal c x with
        | true => ltac1:(y |- subst y) (Ltac1.of_constr y)
        | false =>
          match Constr.equal c y with
          | true => ltac1:(x |- subst x) (Ltac1.of_constr x)
          | false => fail
          end
        end
      end
    )
  ) (decisive_values_list ())).

Ltac subst_decisives := ltac2:(subst_decisives ()).

(* finish *)

Ltac2 mutable finish_debug := false.

Ltac2 fin_log (msg : string) :=
  match finish_debug with
  | true => Message.print (Message.of_string msg)
  | false => ()
  end.

Ltac finish_pre_solve_simpl := fail.
Ltac finish_retry_solve_simpl := fail.
Ltac finish_fast_solve := fail.
Ltac finish_slow_solve := fail.
Ltac finish_entailer_solve := fail.

Ltac inst_exists :=
  repeat lazymatch goal with
  | |- exists i : _, _ => eexists + exists i
  end.

Ltac2 rec simpl_inequality () :=
  try (ltac1:(rep_lia); fin_log "rep_lia.");
  try (ltac1:(cstring); fin_log "cstring.");
  try (ltac1:(list_solve); fin_log "list_solve.");
  split; fin_log "split."; try (simpl_inequality ()).

Ltac2 simpl_plain_goal () :=
  repeat (first
  [ progress intros; fin_log "intros."
  | constructor; fin_log "constructor."
  | progress (simpl_safe ()); fin_log "simpl_safe."
  | progress (subst_decisives ()); fin_log "subst_decisives."
  | progress ltac1:(finish_pre_solve_simpl)
  | progress ltac1:(autorewrite with finish in * |-); fin_log "autorewrite with finish in * |-."
  | progress ltac1:(autounfold with finish in * |-); fin_log "autounfold with finish in * |-."
  | progress ltac1:(inst_exists); fin_log "inst_exists."
  ]).

Ltac2 finish_quick () :=
  first
  [ ltac1:(contradiction); fin_log "contradiction."
  | discriminate; fin_log "discriminate."
  | assumption; fin_log "assumption."
  ].

Ltac2 ez_solve () :=
  first
  [ ltac1:(contradiction); fin_log "contradiction."
  | discriminate; fin_log "discriminate."
  | assumption; fin_log "assumption."
  | reflexivity; fin_log "reflexivity."
  | ltac1:(cstring); fin_log "cstring."
  | solve [auto]; fin_log "auto."
  | solve [auto with valid_pointer]; fin_log "auto with valid_pointer."
  | lazy_match! goal with
    | [ |- context [field_compatible] ] => ()
    | [ |- context [field_compatible0] ] => ()
    end; solve [auto with field_compatible]; fin_log "auto with field_compatible."
  | ltac1:(finish_fast_solve)
  ].

Ltac2 norm_plain () :=
  repeat (first
  [ progress (simpl_plain_goal ())
  | progress ltac1:(finish_retry_solve_simpl)
  | progress ltac1:(autorewrite with sublist in * |-); fin_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with norm sublist); fin_log "autorewrite with norm sublist."
  | progress subst; fin_log "subst."
  ]).

Ltac2 rec finish_plain (fin : unit -> unit) :=
  simpl_plain_goal ();
  try (ez_solve ());
  first
  [ ltac1:(rep_lia); fin_log "rep_lia."
  | ltac1:(cstring'); fin_log "cstring'."
  | ltac1:(Zlength_solve); fin_log "Zlength_solve."
  (* | ltac1:(computable); fin_log "computable." *)
  | ltac1:(list_solve); fin_log "list_solve."
  | ltac1:(finish_slow_solve)
  | progress (norm_plain ()); fin ()
  ].

Ltac2 finish_false () :=
  repeat (first
  [ ltac1:(contradiction); fin_log "contradiction."
  | discriminate; fin_log "discriminate."
  | ltac1:(list_solve); fin_log "list_solve."
  | progress subst; fin_log "subst."
  ]).

Ltac inst_EX :=
  repeat first
  [ EExists_unify
  | EExists + Exists ?
  ].

Ltac2 simpl_entailer_goal () := Control.enter (fun () =>
  repeat (first
  [ progress ltac1:(Intros *); fin_log "Intros *."
  | progress (simpl_safe ()); fin_log "simpl_safe."
  | progress (subst_decisives ()); fin_log "subst_decisives."
  | progress ltac1:(finish_pre_solve_simpl)
  | progress ltac1:(autorewrite with finish in * |-); fin_log "autorewrite with finish in * |-."
  | progress ltac1:(autounfold with finish in * |-); fin_log "autounfold with finish in * |-."
  | lazy_match! goal with
    | [ |- context [if _ then _ else _]] => ltac1:(if_tac); fin_log "if_tac."
    | [ |- context [match ?expr _ with _ => _ end]] => destruct expr > [ | ]; fin_log "destruct match."
    end
  | progress ltac1:(inst_EX); fin_log "inst_EX."
  | ltac1:(cstring1); fin_log "cstring1."
  | progress ltac1:(cancel); fin_log "cancel."
  | progress ltac1:(autorewrite with sublist in * |-); fin_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with sublist); fin_log "autorewrite with sublist."
  | progress ltac1:(autorewrite with norm); fin_log "autorewrite with norm."
  | ltac1:(progress_entailer); fin_log "progress_entailer."
  ])).

Ltac2 norm_entailer () := Control.enter (fun () =>
  repeat (first
  [ progress (simpl_entailer_goal ())
  | progress (simpl_entailment ())
  | progress ltac1:(finish_retry_solve_simpl)
  ])).

Ltac2 finish_entailer_aux (fin : unit -> unit) (fin_ent : (unit -> unit) -> unit) :=
  Control.enter (fun () =>
  match! goal with
  | [ |- @derives mpred _ _ _ ] => solve [ltac1:(cancel)]; fin_log "solve [cancel]."
  | [ |- _ |-- _ ] =>
    first
    [ ltac1:(list_solve); fin_log "list_solve."
    | ltac1:(finish_entailer_solve)
    | lazy_match! goal with
      | [ |- context [ _ |-- _ ] ] => progress (norm_entailer ()); fin_ent fin
      | [ |- _ ] => fin ()
      end
    ]
  | [ |- _ ] => fin ()
  end).

Ltac2 rec finish_entailer (fin : unit -> unit) :=
  simpl_entailer_goal (); finish_entailer_aux fin finish_entailer.

Ltac2 simpl_hyps () := Control.enter (fun () =>
  repeat (
    try (progress ltac1:(autorewrite with finish in * |-); fin_log "autorewrite with finish in * |-.");
    try (progress ltac1:(autounfold with finish in * |-); fin_log "autounfold with finish in * |-.");
    ltac1:(autounfold with finish in * |-);
    try (progress (subst_decisives ()); fin_log "subst_decisives.");
    lazy_match! goal with
    | [ h : False |- _ ] =>
      let h := Control.hyp h in
      ltac1:(H |- contradiction H) (Ltac1.of_constr h); fin_log "contradiction H."
    | [ h : _ /\ _ |- _ ] =>
      (* Based on stdpp solution to bug: https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
      let h_1 := Fresh.in_goal @H_1 in
      let h_2 := Fresh.in_goal @H_2 in
      destruct h as [h_1 h_2]; try (clear h); fin_log "destruct and in H."
    | [ h : _ \/ _ |- _ ] =>
      let h' := Fresh.in_goal @H' in
      destruct h as [ h' | h' ]; try (clear h); fin_log "destruct or in H."
    | [ h_1 : ?p -> ?q, h_2 : ?p |- _ ] =>
      let h_1 := Control.hyp h_1 in
      let h_2 := Control.hyp h_2 in
      specialize ($h_1 $h_2); fin_log "specialize (H_1 H_2)."
    | [ h : exists _, _ |- _ ] =>
      let x := Fresh.in_goal @x in
      destruct h as [x hx]; try (clear h); fin_log "destruct exists in H."
    | [ h : andb _ _ = true |- _ ] => rewrite andb_true_iff in h; fin_log "rewrite andb_true_iff in H."
    | [ h : andb _ _ = false |- _ ] => rewrite andb_false_iff in h; fin_log "rewrite andb_false_iff in H."
    | [ h : orb _ _ = true |- _ ] => rewrite orb_true_iff in h; fin_log "rewrite orb_true_iff in H."
    | [ h : orb _ _ = false |- _ ] => rewrite orb_false_iff in h; fin_log "rewrite orb_false_iff in H."
    | [ h : context [ Is_true ] |- _ ] => rewrite Is_true_eq_true in h; fin_log "rewrite Is_true_eq_true in H."
    | [ |- context [ _ |-- _ ] ] => progress ltac1:(autorewrite with sublist in * |-); fin_log "autorewrite with sublist in * |-."
    end
  )).

Global Create HintDb finish.

Ltac2 rec finish_specialize (fin : unit -> unit) (agro : bool):= Control.enter (
  fun () => lazy_match! goal with
  | [ |- False ] => finish_false ()
  | [ |- ~ _ ] =>
    try (ltac1:(cstring); fin_log "cstring.");
    unfold not; intros; finish_false ()
  | [ |- _ <-> _ ] => split; fin_log "split."; intro; fin_log "intro."; fin ()
  | [ |- _ < _ < _ ] => simpl_inequality (); fin ()
  | [ |- _ <= _ < _ ] => simpl_inequality (); fin ()
  | [ |- _ < _ <= _ ] => simpl_inequality (); fin ()
  | [ |- _ <= _ <= _ ] => simpl_inequality (); fin ()
  | [ |- ?a /\ ?b ] =>
    try (lazy_match! a with
    | Forall _ _ => ltac1:(list_solve); fin_log "list_solve."
    end);
    try (lazy_match! b with
    | Forall _ _ => ltac1:(list_solve); fin_log "list_solve."
    end);
    split; fin_log "split."; fin ()
  | [ |- _ \/ _ ] => fin_log "left + right."; first
    [ left; fin ()
    | right; fin ()
    ]
  | [ |- forall _, _ ] => intro; fin_log "intro."; fin ()
  | [ |- exists _, _ ] => ltac1:(inst_exists); fin_log "inst_exists."; fin ()
  | [ |- semax_body _ _ _ _ ] => ltac1:(start_function); fin_log "start_function."; fin ()
  | [ |- semax _ _ _ _ ] => fastforward agro; fin ()
  | [ |- ?x = ?x ] => reflexivity; fin_log "reflexivity."
  (* | [ |- context [if _ then _ else _]] => ltac1:(if_tac); fin_log "if_tac."; fin () *) (* TODO: Breaks entailment matching?! Maybe checking nesting? *)
  (* | [ |- context [match ?expr _ with | _ => _ end]] => destruct expr > [ | ]; fin_log "destruct match."; fin () *)
  | [ |- context [ _ |-- _ ] ] => 
    simpl_entailer_goal ();
    Control.enter (fun () =>
      lazy_match! goal with
      | [ |- context [ _ |-- _ ] ] => finish_entailer_aux fin finish_entailer
      | [ |- _ ] => fin ()
      end
    )
  | [ |- _ ] => first
    [ solve [auto with finish]; fin_log "solve [auto with finish]."
    | finish_plain fin
    ]
  end).

Ltac2 rec finish (agro : bool) :=
  simpl_hyps ();
  finish_specialize (fun () => finish agro) agro.

Ltac finish := ltac2:(finish false).
Tactic Notation "finish!" := ltac2:(finish true).
