Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.reptype_lemmas.

Local Open Scope logic.

Lemma no_post_exists_unit:
  forall P Q R,
  PROPx P (LOCALx Q (SEPx R)) =
   EX _:unit, PROPx P (LOCALx Q (SEPx R)).
Proof.
intros.
apply pred_ext.
apply exp_right with tt; auto.
apply exp_left; auto.
Qed.

Inductive Stuck : Prop := .

Ltac stuckwith p :=  elimtype Stuck; fold p.

Ltac test_stuck :=
 match goal with
 | |- ?G => unify G Stuck
 end.

Definition not_in_canonical_form := tt.
Definition Error__Funspec (id: ident) (what: unit) (reason: unit) := Stuck.
Definition Cannot_unfold_funspec (fs: ident*funspec) := Stuck.
Definition for_some_undiagnosed_reason (fs: ident*funspec) := tt.
Definition because_of_LOCAL (Q: environ->Prop) := tt.
Definition because_of_SEP (R: environ->mpred) := tt.
Definition because_temp_out_of_scope (i: ident) := tt.
Definition because_Precondition_not_canonical (R: environ->mpred) := tt.
Definition because_Postcondition_not_canonical (R: environ->mpred) := tt.
Definition WITH_clause_should_avoid_using_reptype_otherwise_Coq_is_way_too_slow := tt.

Ltac ccf_PROP id0 P := idtac.

Ltac ccf_LOCAL1 id0 jl i :=
  match jl with
  | (?j,_) :: ?jl' => first [unify i j | ccf_LOCAL1 id0 jl' i]
  | nil => stuckwith (Error__Funspec id0 not_in_canonical_form
                                   (because_temp_out_of_scope i))
  end.

Ltac ccf_LOCAL id0 fsig Q :=
 match Q with
 | nil => idtac
 | temp ?i _ :: ?Q' => ccf_LOCAL1 id0 fsig i;
                                 first [test_stuck |
                                 ccf_LOCAL id0 fsig Q']
 | lvar _ _ _ :: ?Q' =>  ccf_LOCAL id0 fsig Q'
 | ?Q1 :: _ => stuckwith (Error__Funspec id0 not_in_canonical_form
                      (because_of_LOCAL Q1))
 end.

Ltac ccf_SEP id0 R :=
 match R with
 | nil => idtac
 | _ :: ?R' => ccf_SEP id0 R'
 | ?R1 :: _ => stuckwith (Error__Funspec id0 not_in_canonical_form
                     (because_of_SEP R1))
 end.

Ltac ccf2 id0 argsig retsig A Pre Post :=
 try (test_stuck; elimtype False);
 let F := fresh "F" in
 intro F;
 let x := fresh "x" in
 assert (x:A) by (elimtype False; apply F);
 pose (xPre := Pre x); cbv beta in xPre;
 pose (xPost := Post x); cbv beta in xPost;
 repeat (match type of x with (_*_)%type =>
               let y := fresh "x" in destruct x as [x y]
             end);
 revert xPre;
 match goal with
 |- let _ := PROPx ?P (LOCALx ?Q (SEPx ?R)) in _ =>
   ccf_PROP id0 P;
   first [test_stuck |
   ccf_LOCAL id0 argsig Q;
   first [test_stuck |
   ccf_SEP id0 R]]
 | |- let _ := ?PP in _ =>
          stuckwith (Error__Funspec id0 not_in_canonical_form
                     (because_Precondition_not_canonical PP))
 end;
 first [test_stuck |
  elimtype False;
  revert xPost; try rewrite no_post_exists_unit;
  repeat match goal with
  |- let _ := (EX _:_, EX _:_, _) in _ => rewrite exp_uncurry
  end;
  match goal with
  | |- let _ := @exp _ _ ?B ?p in _ =>
    let w := fresh "w" in
    assert (w:B) by (elimtype False; apply F);
    intro xPost; clear xPost;
    pose (xPost := p w); cbv beta in xPost; revert xPost;
    repeat (match type of w with (_*_)%type =>
                  let y := fresh "w" in destruct w as [w y]
                end)
   | |- let _ := ?PP in _ =>
          stuckwith (Error__Funspec id0 not_in_canonical_form
                     (because_Postcondition_not_canonical PP))
   end;
  first [test_stuck |
  match goal with
  |- let _ := PROPx ?P (LOCALx ?Q (SEPx ?R)) in _ =>
   ccf_PROP id0 P;
   first [test_stuck |
   ccf_LOCAL id0 ((ret_temp,  retsig)::nil) Q;
   first [test_stuck |
   ccf_SEP id0 R]]
  end;
  first [test_stuck |
   elimtype False;
   apply F]]].

Ltac check_WITH_reptype id A :=
   match A with context [reptype _] =>
       stuckwith (Error__Funspec id WITH_clause_should_avoid_using_reptype_otherwise_Coq_is_way_too_slow tt)
  end.

Ltac ccf1 fs :=
  match fs with
  | (?id, mk_funspec (?argsig,?retsig) ?A ?Pre ?Post ) =>
    first [ cut False;
               [  try check_WITH_reptype id A;
                 first [test_stuck
                 | ccf2 id argsig retsig A Pre Post]
               | idtac
               ]
            | stuckwith (Error__Funspec id not_in_canonical_form
                                    (for_some_undiagnosed_reason fs))
            ]
  | _ => let fs' := constr:(fs) in
    let fs'' := (eval unfold fs in fs') in
    ccf1 fs''
  | _ => stuckwith (Cannot_unfold_funspec fs)
  end.

Ltac check_canonical_funspec fs :=
    try (test_stuck; elimtype False);
    first [ccf1 fs; [test_stuck | ] | idtac].

(* Change goal to [message arg], without failing *)
Tactic Notation "errormsg" simple_intropattern(message) constr(arg) :=
  let x := fresh in pose proof arg as x; revert x;
  match goal with |- ?type -> _ =>
    intros _; pose (message := fun _ : type => False);
    exfalso; change (message arg); clearbody message
  end.

Ltac check_canonical_call' Delta c :=
match c with
| Scall _ (Evar ?id _) _ =>
  let x := constr:((glob_specs Delta) ! id) in
    let y := (eval simpl in x) in
    match y with
    | Some ?fs => check_canonical_funspec fs
    | None => errormsg No_function_specificiation_corresponds_to_id id
    end
| Ssequence ?c1 _ => check_canonical_call' Delta c1
| _ => let d := eval hnf in c in check_canonical_call' Delta d
end.

Ltac check_canonical_call :=
match goal with |- semax ?Delta _ ?c _ =>
   check_canonical_call' Delta c
end.
