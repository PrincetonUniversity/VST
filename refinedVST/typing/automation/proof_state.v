From VST.lithium Require Import all.
From lithium Require Import hooks.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Import type globals.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
(* From VST.lithium.automation Require Import solvers. *)



(** Ke: use empty location_info for now; I guess it is for error messages like `proof failed in file x line y` *)
Definition location_info : Type := Empty_set.

(** * Markers for keeping track of the proof state *)
Definition CURRENT_LOCATION (i : list location_info) (up_to_date : bool) : Set := unit.
Arguments CURRENT_LOCATION : simpl never.
Definition CASE_DISTINCTION_INFO {B} (info : B) (i : list location_info) : Set := unit.
Arguments CASE_DISTINCTION_INFO : simpl never.

Definition pop_location_info {A} (i : location_info) (a : A) : A := a.
Arguments pop_location_info : simpl never.
Global Typeclasses Opaque pop_location_info.

Inductive BLOCK_PRECOND_HINT := | BLOCK_PRECOND (bid : label).
Inductive ASSERT_COND_HINT := | ASSERT_COND (id : string).

(* The `{!typeG Σ} is necessary to infer Σ if P is True. *)
Definition IPROP_HINT `{!typeG OK_ty Σ} {A B} (a : A) (P : B → iProp Σ) : Prop := True.
Arguments IPROP_HINT : simpl never.

Notation "'block' bid : P" := (IPROP_HINT (BLOCK_PRECOND bid) (λ _ : unit, P)) (at level 200, only printing).
Notation "'assert' id : P" := (IPROP_HINT (ASSERT_COND id) P) (at level 200, only printing).

Definition CODE_MARKER (bs : gmap label statement) : gmap label statement := bs.
Notation "'HIDDEN'" := (CODE_MARKER _) (only printing).
Arguments CODE_MARKER : simpl never.
Ltac unfold_code_marker_and_compute_map_lookup :=
  unfold CODE_MARKER in *; solvers.compute_map_lookup.

Definition RETURN_MARKER `{!typeG OK_ty Σ} {cs:compspecs} (R : val → type → iProp Σ) : val → type → iProp Σ := R.
Notation "'HIDDEN'" := (RETURN_MARKER _) (only printing).


(** * Tactics for manipulating location information *)
Ltac get_loc_info cont :=
  first [ lazymatch reverse goal with
          | H : CURRENT_LOCATION ?icur _ |- _ => cont icur
          end | cont constr:(@nil location_info)
        ].

Ltac update_loc_info i :=
  first [
      lazymatch reverse goal with
      | H : CURRENT_LOCATION ?icur _ |- _ =>
        lazymatch i with
        | Some ?i2 =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION [i2] true) in H
        (* Push *)
        | [ ?i2 ] =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION (i2 :: icur) true) in H
        (* Pop *)
        | [ ?i2; _ ] =>
          lazymatch icur with
          | i2 :: ?iprevh :: ?iprevt =>
            change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION (iprevh :: iprevt) true) in H
          | [i2] =>
            change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION ([i2]) false) in H
          | _ =>
            (* mismatched pop *)
            change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION ([i2]) false) in H
          end
        | None =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION icur false) in H
        end
      end
    |
    (* TODO: unify the first two branches *)
    lazymatch i with
    | Some ?i2 =>
      let Hcur := fresh "HCURLOC" in
      have Hcur := (() : CURRENT_LOCATION [i2] true)
    | [?i2] =>
      let Hcur := fresh "HCURLOC" in
      have Hcur := (() : CURRENT_LOCATION [i2] true)
    | None => idtac
    end
    ].

Ltac add_case_distinction_info info :=
    get_loc_info ltac:(fun icur =>
    let Hcase := fresh "HCASE" in
    have Hcase := (() : (CASE_DISTINCTION_INFO info icur))).

(** * Tactics cleaning the proof state *)
Ltac clear_unused_vars :=
  repeat match goal with
         | H : ?T |- _ =>
           (* Keep current location and case distinction info. *)
           lazymatch T with
           | CURRENT_LOCATION _ _ => fail
           | CASE_DISTINCTION_INFO _ _ => fail
           | _ => idtac
           end;
           let ty := (type of T) in
           match ty with | Type => clear H | Set => clear H end
         end.

Ltac prepare_sideconditions :=
  li_unfold_lets_in_context;
  repeat match goal with | H : IPROP_HINT _ _ |- _ => clear H end;
  (* get rid of Q *)
  repeat match goal with | H := CODE_MARKER _ |- _ => clear H end;
  repeat match goal with | H := RETURN_MARKER _ |- _ => clear H end;
  clear_unused_vars.

Ltac solve_goal_prepare_hook ::=
  prepare_sideconditions;
  repeat match goal with | H : CASE_DISTINCTION_INFO _ _ |- _ => clear H end.

(** * Tactics for showing failures to the user *)

(** FIXME 
Ltac print_current_location :=
  try lazymatch reverse goal with
      | H : CURRENT_LOCATION ?l ?up_to_date |- _ =>
        let rec print_loc_info l :=
            match l with
            | ?i :: ?l =>
              lazymatch eval unfold i in i with
              | LocationInfo ?f ?ls ?cs ?le ?ce =>
                let f := eval unfold f in f in
                idtac "Location:" f "[" ls ":" cs "-" le ":" ce "]";
                print_loc_info l
              end
            | [] => idtac "up to date:" up_to_date
            end in
        print_loc_info l;
        clear H
      end.
*)

Ltac print_case_distinction_info :=
   repeat lazymatch reverse goal with
          | H : CASE_DISTINCTION_INFO ?i ?l |- _ =>
            lazymatch i with
            | (?a, ?b) => idtac "Case distinction" a "->" b
            | ?a => idtac "Case distinction" a
            end;
            (** FIXME
            lazymatch l with
            | ?i :: ?l =>
              lazymatch eval unfold i in i with
              | LocationInfo ?f ?ls ?cs ?le ?ce =>
                let f := eval unfold f in f in
                idtac "at" f "[" ls ":" cs "-" le ":" ce "]"
              end
            | [] => idtac 
            end; *)
            clear H
          end.

Ltac print_coq_hyps :=
  try match reverse goal with
  | H : ?X |- _ =>
    lazymatch X with
    | IPROP_HINT _ _ => fail
    | gFunctors => fail
    | typeG _ _ => fail
    | globalG _ => fail
    | _ => idtac H ":" X; fail
    end
  end.

Ltac print_goal :=
  (* FIXME print_current_location; *)
  print_case_distinction_info;
  idtac "Goal:";
  print_coq_hyps;
  idtac "---------------------------------------";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "";
  idtac "".

Ltac print_typesystem_goal fn block :=
  lazymatch goal with
  (* TODO: Is something like the following useful? *)
  (* | |- ?P ∧ ?Q => *)
  (*   idtac "Cannot instantiate evar in" fn "in block" block "!"; *)
  (*   print_current_location; *)
  (*   print_case_distinction_info; *)
  (*   idtac "Goal:"; *)
  (*   print_coq_hyps; *)
  (*   idtac "---------------------------------------"; *)
  (*   idtac P; *)
  (*   (* TODO: Should we print the continuation? It might confuse the user and *)
  (*      it usually is not helpful. *) *)
  (*   (* idtac ""; *) *)
  (*   (* idtac "Continuation:"; *) *)
  (*   (* idtac Q; *) *)
  (*   idtac ""; *)
  (*   idtac ""; *)
  (*   admit *)
  | |- _ =>
    idtac "Type system got stuck in function" fn "in block" block "!";
    print_goal; admit
  end.

Ltac print_sidecondition_goal fn :=
  idtac "Cannot solve side condition in function" fn "!";
  print_goal; admit.

Ltac print_remaining_shelved_goal fn :=
  idtac "Shelved goal remaining in " fn "!";
  print_goal; admit.
