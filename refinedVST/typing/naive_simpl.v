From lithium Require Export base.
From lithium Require Import hooks pure_definitions normalize.
From VST.lithium Require Import simpl_classes solvers proof_state.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO: clean up this file *)

Lemma tac_eq_replace (P1 P2 : Prop):
  P2 = P1 → P1 → P2.
Proof. by move => ->. Qed.

Lemma tac_f_equal_fn {A B} (f1 f2 : A → B) x1 x2 r:
  x1 = x2 → f1 = f2 → f2 x2 = r → f1 x1 = r.
Proof. by move => -> -> ->. Qed.
Lemma tac_f_equal_fn2 {A B} (f1 f2 : A → B) x1 x2 r:
  x1 = x2 → f1 = f2 → f2 x2 = r → r = r → f1 x1 = r.
Proof. by move => -> -> ->. Qed.

(* Lemma tac_apply_Normalize {A B} (f1 f2 : A → B) x1 x2 r: *)
(*   x1 = x2 → f1 = f2 → f1 x1 = r. *)
(* Proof. by move => -> -> ->. Qed. *)


Goal ∀ l i (x : Z),
    -1 < length (<[i:=x]> $ <[i:=x]> (<[length (<[i:=x]>l) :=x]> l ++ <[length (<[i:=x]>l) :=x]> l)).
  move => ???.

  (* Time normalize_goal. *)
  (* Time notypeclasses refine (tac_normalize_goal _ _ _ _); [normalize_autorewrite|]. *)
  lia.


Abort.

Ltac normalize2 P cont :=
  let typeP := type of P in
  let do_nothing x :=
      (* idtac "do nothing " P; *)
      cont P uconstr:(@eq_refl typeP P) in
  (* idtac "starting" P; *)
  lazymatch P with
  | ?f ?a =>
    lazymatch type of f with
    | ?A → ?B =>
      normalize2 a ltac:(fun a' Heqa =>
      normalize2 f ltac:(fun f' Heqf =>
        let r := fresh "r" in
        let Hr := fresh "Hr" in
        first [
          simple notypeclasses refine (let r := _ in let Hr := _ : Normalize (f' a') r in _); [shelve| unfold r; solve [refine _ ] |];
          (* simple notypeclasses refine (let r := _ in (λ Hr : Normalize (f' a') r, _) _); [shelve| | unfold r; solve [refine _ ]]; *)
          let r' := eval unfold r in r in
          (* let Hr' := eval unfold Hr in Hr in *)
          unfold r,Normalize in Hr;
          (* clear r Hr; *)
          clear r;
                                   (* idtac f a "-" r'; *)
          assert_fails (constr_eq_strict constr:(f a) r');
        (* idtac "found!" r'; *)
        (* let Hrt := type of Hr in idtac "Hr" Hr Hrt; *)
        (* let c:= constr:(normalize (Normalize := Hr)) in let ct := type of c in idtac c ct; *)
        cont r' uconstr:(@tac_f_equal_fn A B f f' a a' r' Heqa Heqf Hr);
                          clear Hr
        (* idtac "constr2" r' *)
        | do_nothing O
        ]))
        (* idtac "nothong..."; *)
        (* do_nothing () *)
        (* idtac "after do nothing1" P *)
      (* else ( *)
        (* idtac "found!" r'; *)
        (* idtac "cont!" P; *)
        (* idtac "found2!" r'; *)
        (* idtac "cont2!" P; *)
        (* idtac "after cont" P *)
      (* ))) *)
    | _ => do_nothing O
    end
  | _ => do_nothing O
  end.

Ltac normalize3 :=
  lazymatch goal with
  | |- @eq ?A ?P _ =>
  lazymatch P with
  | ?f ?a =>
    lazymatch type of f with
    | ?A → ?B => (
                    notypeclasses refine (tac_f_equal_fn _ _ _ _ _ _ _ _);
                    [normalize3|normalize3|
                     lazymatch goal with
                     | |- ?A = ?B => change_no_check (Normalize A B)
                     end; solve [ refine _ ] ]) ||
                    exact: eq_refl
    | _ => exact: eq_refl
    end
    | _ => exact: eq_refl
  end
  end.

Ltac normalize_goal2 :=
  match goal with
  | |- ?P => normalize2 P ltac:(fun P' Heq =>
                                notypeclasses refine (tac_eq_replace P' P Heq _)
                             )
  end.

Ltac normalize_goal3 :=
  match goal with
  | |- ?P =>
    notypeclasses refine (tac_eq_replace _ _ _ _); [normalize3|]
  end.

Ltac normalize4 :=
  lazymatch goal with
  | |- @eq ?A ?P ?B =>
  let rec go ctx P :=
  lazymatch P with
  | ?f ?a =>
    lazymatch type of f with
    | ?A → ?B =>
      (
        (* idtac ctx P f a; *)
      let fctx := eval lazy beta in (λ x, ctx (x a)) in
      go fctx f;
      let actx := eval lazy beta in (λ x, ctx (f x)) in
      go actx a;
         refine (eq_ind_r ctx _ _);[|
                                    lazymatch goal with
         | |- ?A = ?B => change_no_check (Normalize A B)
         end; solve [ refine _ ]
                                   ]

      ) || idtac
    (* ( *)
        (* notypeclasses refine (tac_f_equal_fn _ _ _ _ _ _ _ _); *)
        (* [normalize3|normalize3| *)
         (* lazymatch goal with *)
         (* | |- ?A = ?B => change_no_check (Normalize A B) *)
         (* end; solve [ refine _ ] ]) || *)
                                    (* exact: eq_refl *)
    | _ => idtac
(* idtac "end" P *)
(* exact: eq_refl *)
    end
| _ => idtac
(* idtac "end" P *)
  (* exact: eq_refl *)
  end in go constr:(λ x: A, x = B) P; exact: eq_refl
  (* end in *)
  (* go ltac:(fun i => uconstr:(λ x, i x = B)) P; exact: eq_refl *)
  end.

Ltac normalize_goal4 :=
  match goal with
  | |- ?P =>
    notypeclasses refine (tac_eq_replace _ _ _ _); [normalize4|]
  end.

(* Goal True. *)
(*   simple notypeclasses refine (let x := _ in let H := _ : Normalize 0 x in _); [shelve| unfold x; solve [refine _ ] |]. *)
(*   (* Set Printing All. *) *)
(*   let Hr := eval unfold H in H in idtac Hr. *)
(*   notypeclasses refine ( (λ x : Z, λ H : Normalize 0 x, _ ) _ _). *)

#[export] Hint Rewrite @length_insert @length_app : test_db.
Goal ∀ l i (x : Z),
    0%nat = length (<[i:=x]> l).
  intros.
  (* let ctx := ltac:(fun i => uconstr:(λ x, ltac:(i x) = 0)) in *)
  (* let ctx' := ctx ltac:(fun x => idtac x; x) in idtac ctx'. *)

  (* Set Typeclasses Debug Verbosity 2. *)
  (* normalize_goal. *)

  normalize_goal4.

  (* unshelve let a := uconstr:(fun xxx => uconstr:(xxx)) in idtac a. *)

  (* Show Proof. *)
  (* Time normalize_goal. *)
  (* Time autorewrite with test_db. *)
  (* Show Proof. *)
  notypeclasses refine (tac_eq_replace _ _ _ _). 2: shelve.

  (* notypeclasses refine (tac_f_equal_fn _ _ _ _ _ _ _ _); *)
  (*                   [normalize3|normalize3| *)
  (*                    lazymatch goal with *)
  (*                    | |- ?A = ?B => change_no_check (Normalize true A B) *)
  (*                    end; solve [ refine _ ] ]. *)


  (* progress (refine (tac_f_equal_fn _ _ _ _ _ _ _ _);[ exact: eq_refl..|]). *)
Abort.

  (*   move => l i x. *)
(* (*   (* notypeclasses refine (tac_eq_replace (0 = length l) (0 = length (<[i:=x]> l)) _ _). *) *) *)
(* (* (* ((0 = strings.length (<[i:=x]> l)) = (0 = strings.length l)) *) *) *)
(* (*   (* Set Ltac  Debug. *) *) *)
(*   normalize_goal2. *)

(*   tryif idtac then idtac "a"; idtac "b" else idtac "b"; idtac  "d". *)


Goal ∀ l i (x : Z),
    -1 < length (<[i:=x]> $ <[i:=x]> (<[length (<[i:=x]>l) :=x]> l ++ <[length (<[length (<[length (<[i:=x]>l):=x]>l):=x]>l) :=x]> l)).
  move => ???.
  (* Time normalize_goal. *)
   (* Time notypeclasses refine (tac_normalize_goal _ _ _ _); [normalize_autorewrite|]. *)
  (* Show Proof. *)
  (* Time autorewrite  with test_db. *)
  (* Show Proof. *)
  (* Show Proof. *)
  (* Time normalize_goal4. *)
  (* Show Proof. *)
  (* Time rewrite_strat (topdown (choice length_insert length_app)). *)
  (* nmo *)

  (* normalize_goal3. *)
  (* notypeclasses refine (tac_eq_replace _ _ _ _). 2: shelve. *)
  (* ( *)
  (*                   notypeclasses refine (tac_f_equal_fn _ _ _ _ _ _ _ _); *)
  (*                   [normalize3|normalize3| *)
  (*                    lazymatch goal with *)
  (*                    | |- ?A = ?B => change_no_check (Normalize A B) *)
  (*                    end; solve [ refine _ ] ]). *)
  (*                   exact: eq_refl. *)

  (* normalize3. *)
  (* notypeclasses refine (tac_f_equal_fn2 _ _ _ _ _ _ _ _ _); *)
  (*   [normalize3|normalize3| *)
  (*    lazymatch goal with *)
  (*    | |- ?A = ?B => change_no_check (Normalize A B) *)
  (*    end; solve [ refine _ ] | ]. *)



  (* notypeclasses refine (tac_eq_replace _ _ _ _). *)
  (* notypeclasses refine (tac_f_equal_fn _ _ _ _ _ _ _ _). exact: eq_refl. exact: eq_refl. *)
  (* lazymatch goal with *)
  (* | |- ?A = ?B => change_no_check (Normalize A B) *)
  (* end. *)


  (* (* let x := (1 + 1) in idtac x. *) *)
  (* (* simple notypeclasses refine (let r := _ in (λ Hr : Normalize (0) r, _) _). *) *)
  (* normalize_goal2. *)
  (* Set Printing Implicit. Show Proof.
  (* normalize_goal2. *) *)
  lia.
Qed.


Goal ∀ l i (x : Z), seq 0%nat 50%nat ++ [length (<[length (<[i:=x]> l):=x]> l)] ≠ [].
  intros. simpl.
   (* Time autorewrite with test_db. *)
   (* Time notypeclasses refine (tac_normalize_goal _ _ _ _); [normalize_autorewrite|]. *)
   (* Set Typeclasses Debug. *)
   (* Time normalize_goal. *)
   (* Show Proof. *)
   (* Time normalize_goal2. *)
   (* Time normalize_goal3. *)
   (* Time normalize_goal4. *)
   (* done. *)
   (* Show Proof. *)
(* Time Qed. *)
Abort.
  (* { simpl. Time normalize_goal2. Set Printing Implicit. Show Proof. Time normalize_goal2. admit. } *)

Goal True.
  (* assert True as G. Show Proof. admit. *)
  (* have : ∃ a : nat, a = a. eexists _. Show Proof. *)


  (* notypeclasses refine ((λ a, (λ H : Normalize O a , _ ) _) _). admit. revert H. Show Proof. *)
  (* assert (∃ P, Normalize n *)
  (* constr_eq_strict constr:(S O) (S O). *)
  (* evar (r : (list nat → Prop)).   *)
  (* assert (Normalize (eq (@nil nat)) r) as Hr. unfold r. *)
  (* apply normalize_end. *)
  (* ; [solve [refine _] |]. *)

  (* have : seq 0%nat 0%nat = []. { simpl. Time normalize_goal. Time normalize_goal2. admit. } *)
  (* have : seq 0%nat 10%nat = []. { simpl. Time normalize_goal. Time normalize_goal2. admit. } *)
  (* have : seq 0%nat 50%nat = []. { simpl. Time normalize_goal. Time normalize_goal2. admit. } *)
  (* have : seq 0%nat 100%nat = []. { simpl. Time normalize_goal. Time normalize_goal2. admit. } *)
Abort.

Definition shelve_marker (P : Prop) : Prop := P.

Ltac naive_simpl_go :=
  lazymatch goal with
  | |- _ → _ =>
    lazymatch goal with
    (* relying on the fact that unification variables cannot contain
       dependent variables to distinguish between dependent and non dependent forall *)
    | |- ?P -> ?Q =>
      normalize_and_simpl_impl true
    | |- forall _ : ?P, _ =>
      lazymatch P with
      | (prod _ _) => case
      | unit => case
      | _ => intro
      end
    end
  | |- ?P ∧ ?Q => first [
      progress normalize_goal_and
    | notypeclasses refine (simpl_and_unsafe_and P _ Q _); [solve [refine _] |]; simpl
    | match P with
      | _ ∧ _ => notypeclasses refine (tac_and_assoc _ _ _ _)
      | ∃ _, _ => notypeclasses refine (tac_exist_assoc _ _ _)
      (* TODO: Is this a good idea? *)
      | _ → _ => split
      | _ => split; [fast_done || change (shelve_marker P); shelve | ]
      end
    ]
  | |- @ex ?A ?P => first [
    lazymatch A with
    (* | prod _ _ => apply: tac_exist_prod *)
    (* | sigT _ => apply: tac_exist_sigT *)
    | unit => exists tt
    (* | ?A => let Hevar := create_protected_evar A in exists (protected Hevar) *)
    end |
    change (shelve_marker (@ex A P)); shelve
    ]
  | |- True => exact: I
  | _ => refine (intro_and_True _ _)
  end.

Ltac naive_simpl :=
  unshelve (repeat naive_simpl_go);
  match goal with
  | |- shelve_marker ?P => change P
  | _ => shelve
  end.

Ltac naive_solve := naive_simpl; solve_goal.
