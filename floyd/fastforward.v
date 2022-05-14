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
  | progress ltac1:(fastforward_semax_pre_simpl)
  | ltac1:(forward); ff_log "forward."
  | ltac1:(forward_if); ff_log "forward_if."
  | ltac1:(forward_call); ff_log "forward_call."
  | ltac1:(cstring1); ff_log "cstring1."
  | progress ltac1:(autorewrite with norm); ff_log "autorewrite with norm."
  | progress ltac1:(autorewrite with sublist in * |-); ff_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with sublist); ff_log "autorewrite with sublist."
  | progress ltac1:(fastforward_semax_post_simpl)
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
  | ltac1:(cstring1); ff_log "cstring1."
  | ltac1:(forward); ff_log "forward."
  | ltac1:(forward_if); ff_log "forward_if."
  | ltac1:(forward_call); ff_log "forward_call."
  | progress ltac1:(fastforward_semax_post_simpl)
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
  progress (repeat (Control.enter(fun () =>
    lazy_match! goal with
    | [ |- semax _ _ _ _ ] => simplstep agro
    | [ |- _ ] => ltac1:(clear_MORE_POST)
    end))).

Ltac2 rec fastforward_n (agro : bool) (n : int) :=
  match Int.equal n 0 with
  | true => Control.enter (fun () =>
    lazy_match! goal with
    | [ |- semax _ _ _ _ ] => ()
    | [ |- _ ] => ltac1:(clear_MORE_POST)
    end)
  | false =>
    let f := { contents := false } in
    Control.enter(fun () =>
      lazy_match! goal with
      | [ |- semax _ _ _ _ ] => simplstep agro; f.(contents) := true
      | [ |- _ ] => ()
      end
    );
    match f.(contents) with
    | true => fastforward_n agro (Int.sub n 1)
    | false => Control.zero (Tactic_failure (Some (Message.of_string "`n` is too large")))
    end
  end.

Tactic Notation "fastforward" := ltac2:(fastforward false).
Tactic Notation "fastforward" integer(n) :=
  let step := idtac; ltac2:(
    let f := { contents := false } in
    Control.enter(fun () =>
      lazy_match! goal with
      | [ |- semax _ _ _ _ ] => simplstep false; f.(contents) := true
      | [ |- _ ] => ()
      end
    );
    match f.(contents) with
    | true => ()
    | false => Control.zero (Tactic_failure (Some (Message.of_string "`n` is too large")))
    end
  ) in 
  do n step;
  lazymatch goal with
  | |- semax _ _ _ _ => idtac
  | |- _ => clear_MORE_POST
  end.

Tactic Notation "fastforward!" := ltac2:(fastforward true).
Tactic Notation "fastforward!" integer(n) :=
  let step := idtac; ltac2:(
    let f := { contents := false } in
    Control.enter(fun () =>
      lazy_match! goal with
      | [ |- semax _ _ _ _ ] => simplstep true; f.(contents) := true
      | [ |- _ ] => ()
      end
    );
    match f.(contents) with
    | true => ()
    | false => Control.zero (Tactic_failure (Some (Message.of_string "`n` is too large")))
    end
  ) in 
  do n step;
  lazymatch goal with
  | |- semax _ _ _ _ => idtac
  | |- _ => clear_MORE_POST
  end.
