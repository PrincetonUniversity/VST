From Ltac2 Require Import Ltac2.

Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.entailer.
Require Import VST.floyd.forward. (* must come after entailer because of Ltac override *)
Require Import VST.floyd.deadvars.
Require Import VST.floyd.step.

Ltac2 mutable fastforward_debug := false.

Ltac2 ff_log (msg : string) :=
  match fastforward_debug with
  | true => Message.print (Message.of_string msg)
  | false => ()
  end.

Ltac fastforward_semax_pre_simpl := idtac.
Ltac fastforward_semax_post_simpl := idtac.

(* Performs a "single-step" for fastforward *)
Ltac2 fastforward_ss () :=
  first
  [ progress ltac1:(Intros *); ff_log "Intros *."
  | progress (ltac1:(simpl_implicit)); ff_log "simpl_implicit."
  | progress ltac1:(fold_Vbyte); ff_log "fold_Vbyte"
  | first
    [ ltac1:(EExists_unify); ff_log "EExists_unify."
    | ltac1:(EExists); ff_log "EExists."
    ]
  | progress ltac1:(fastforward_semax_pre_simpl)
  | ltac1:(forward); ff_log "forward."
  | ltac1:(forward_if); ff_log "forward_if."
  | ltac1:(forward_call); ff_log "forward_call."
  | ltac1:(cstring1); ff_log "cstring1."
  | ltac1:(progress_entailer); ff_log "progress_entailer."
  | progress ltac1:(autorewrite with norm); ff_log "autorewrite with norm."
  (*| match goal with |- ENTAIL _, _ |-- _ =>  go_lower end; idtac "go_lower."*)
  | progress ltac1:(autorewrite with sublist in * |-); ff_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with sublist); ff_log "autorewrite with sublist."
  | progress ltac1:(fastforward_semax_post_simpl)
  (* | lazy_match! goal with [ |- context [if _ then _ else _] ] => ltac1:(if_tac) end; print (of_string "if_tac.") *)
  ].

Ltac2 fastforward_ss' () :=
  first
  [ progress ltac1:(Intros *); ff_log "Intros *."
  | progress ltac1:(simpl_implicit); ff_log "simpl_implicit."
  | progress ltac1:(fold_Vbyte); ff_log "fold_Vbyte"
  | progress ltac1:(fastforward_semax_pre_simpl)
  | progress ltac1:(autorewrite with norm); ff_log "autorewrite with norm."
  | progress ltac1:(autorewrite with sublist); ff_log "autorewrite with sublist."
  | progress ltac1:(autorewrite with sublist in * |-); ff_log "autorewrite with sublist in * |-."
  | first
    [ ltac1:(EExists_unify); ff_log "EExists_unify."
    | ltac1:(EExists); ff_log "EExists."
    ]
  | ltac1:(cstring1); ff_log "cstring1."
  | ltac1:(forward); ff_log "forward."
  | ltac1:(forward_if); ff_log "forward_if."
  | ltac1:(forward_call); ff_log "forward_call."
  | ltac1:(progress_entailer); ff_log "progress_entailer."
  (*| match goal with |- ENTAIL _, _ |-- _ =>  go_lower end; idtac "go_lower."*)
  | progress ltac1:(fastforward_semax_post_simpl)
  (* | lazy_match! goal with [ |- context [if _ then _ else _] ] => ltac1:(if_tac) end; print (of_string "if_tac.") *)
  ].

Ltac2 simplstep (agro : bool) := Control.enter (fun () =>
  lazy_match! goal with
  | [ |- semax _ _ ?cmds _ ] =>
    (fun ss =>
      repeat (
        Control.enter (fun () =>
          lazy_match! goal with
          | [ |- semax _ _ ?cmds' _ ] =>
            match Constr.equal cmds cmds' with
            | true => ()
            | false => fail
            end
          end
        );
        ss ()
      )
    )
    (
      match agro with
      | false => fastforward_ss
      | true => fastforward_ss'
      end
    )
  end).

Ltac2 fastforward (agro : bool) :=
  progress (repeat (lazy_match! goal with
  | [ |- semax _ _ _ _ ] => simplstep agro
  | [ |- _ ] => ltac1:(clear_MORE_POST)
  end)).

Ltac2 fastforward_n (agro : bool) (n : int) :=
  do n (lazy_match! goal with
  | [ |- semax _ _ ?cmds _ ] => simplstep agro
  | [ |- _ ] => ltac1:(clear_MORE_POST)
  end).

Tactic Notation "fastforward" := ltac2:(fastforward false).
Tactic Notation "fastforward" integer(n) :=
  do n (lazymatch goal with
  | |- semax _ _ ?cmds _ => ltac2:(simplstep false)
  | |- _ => clear_MORE_POST
  end).

Tactic Notation "fastforward!" := ltac2:(fastforward true).
Tactic Notation "fastforward!" integer(n) :=
  do n (lazymatch goal with
  | |- semax _ _ ?cmds _ => ltac2:(simplstep true)
  | |- _ => clear_MORE_POST
  end).
