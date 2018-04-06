Require Import VST.floyd.proofauto.
Require Import VST.concurrency.semax_conc.

Module Type threadlib_args.
  Parameter CompSpecs : compspecs.
  Parameter ext_link : string -> ident.
End threadlib_args.

Module threadlib (args : threadlib_args).
Import args.

Local Open Scope logic.

Definition makelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (data_at_ sh tlock v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R).

Definition freelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (R; lock_inv sh v R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R; data_at_ sh tlock v).

Definition acquire_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R; R).

Definition release_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v R; R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R).

Definition voidstar_funtype :=
  Tfunction
    (Tcons (tptr tvoid) Tnil)
    (tptr tvoid)
    cc_default.

Definition spawn_thread_spec (PrePost: (val ->mpred * mpred)) :=
   WITH f : val, b : val
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP ((EX _y : ident, func_ptr'
       (WITH y : val
          PRE [ _y OF tptr tvoid ]
            PROP  ()
            LOCAL (temp _y y)
            SEP   (fst (PrePost y))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (snd (PrePost y))
       )
       f);
     (fst (PrePost b)))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

Definition exit_thread_spec (_ : unit) :=
   WITH u:unit
   PRE [ ]
     PROP ()
     LOCAL ()
     SEP (emp)
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP (FF).

(* We list the specifications that we assume.  In the future,
   identifier for those functions would be strings instead of
   positives. *)

Variable ext_link : string -> ident.

Definition threadlib_specs : list (ident * {x : Type & x -> funspec}) := [
  (ext_link "acquire" , existT _ mpred                  acquire_spec);
  (ext_link "release" , existT _ mpred                  release_spec);
  (ext_link "makelock", existT _ mpred                  makelock_spec);
  (ext_link "freelock", existT _ mpred                  freelock_spec);
  (ext_link "spawn"   , existT _ ((val->mpred * mpred))  spawn_thread_spec)
].

Fixpoint find_in_list {A B} (D:forall x y : A, {x = y} + {x <> y})
  (a : A) (l : list (A * B)) : option B :=
  match l with
    | nil => None
    | (a', b) :: l => if D a a' then Some b else find_in_list D a l
  end.

Definition find_in_threadlib_specs id := find_in_list peq id threadlib_specs.

Lemma semax_acquire:
   forall {cs: compspecs} (Frame : list mpred) (Delta : tycontext)
       (P : list Prop) (Q : list localdef) (bl : list expr) (ResInv : mpred)
       (witness: val*share) argsig
     (Pre Post: val*share -> environ -> mpred) ,
 argsig = [(_lock, tptr tlock)] ->
 Pre witness = (let (v,sh) := witness in
          (PROP (readable_share sh)
       LOCAL (temp _lock v)  SEP (lock_inv sh v ResInv)))  ->
 Post witness = (let (v,sh) := witness in
          (PROP ( )  LOCAL ()  SEP (lock_inv sh v ResInv; ResInv))) ->
@semax cs (Concurrent_Espec unit cs ext_link) Delta
  (tc_exprlist Delta (argtypes [(_lock, tptr tlock)]) bl &&
   (` (Pre witness)  (make_args' (argsig, Tvoid)
                          (eval_exprlist (argtypes argsig) bl)) *
    PROPx P (LOCALx Q (SEPx Frame))))
  (Scall None
     (Evar (ext_link "acquire")
        (Tfunction (type_of_params [(_lock, tptr tlock)]) Tvoid
           cc_default)) bl)
  (normal_ret_assert
     (` (Post witness)
        (make_args [] []) * PROPx P (LOCALx Q (SEPx Frame)))).
Proof.
intros.
rewrite H0,H1; clear H0 H1. subst argsig. clear.
destruct witness as [v sh].
(* rewrite semax.semax_fold_unfold. *)
Abort.


Lemma semax_call_00_helper:  (* This lemma's proof almost identical to semax_call_id00_wow *)
forall (Frame : list mpred) (cs : compspecs) (Delta : tycontext)
  (P : list Prop) (Q : list localdef) (R : list mpred) (bl : list expr)
  (Ppre : list Prop) (Qpre : list localdef) (Qtemp Qpre_temp : PTree.t val)
  (Qvar Qpre_var : PTree.t vardesc)
  (B : Type) (Ppost : B -> list Prop) (Rpre : list mpred)
  (Rpost : B -> list mpred)
  (vl : list val)
  (witness' : mpred)
  (argsig: list (ident * type))
  (A: Type)
  (witness : A)
  (Pre Post : A -> environ -> mpred)
  (PTREE : local2ptree Q = (Qtemp, Qvar, [], []))
  (PTREE' : local2ptree Qpre = (Qpre_temp, Qpre_var, [], []))
  (CHECKVAR : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar)
                    (PTree.elements Qpre_var))
  (FRAME : fold_right sepcon emp R
        |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
  (PPRE : fold_right_and True Ppre)
  (GLBL : (var_types Delta) ! (ext_link "acquire") = None)
  (TC1 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
      |-- tc_exprlist Delta (argtypes argsig) bl)
  (MSUBST : force_list
           (map (msubst_eval_expr Qtemp Qvar)
              (explicit_cast_exprlist (argtypes argsig) bl)) =
         Some vl)
  (CHECKTEMP : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
            |-- !! Forall
                     (check_one_temp_spec
                        (pTree_from_elements
                           (combine (var_names argsig) vl)))
                     (PTree.elements Qpre_temp))
  (PRE1 : Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
  (POST1 : Post witness =
        (EX vret : B, PROPx (Ppost vret) LOCAL ()  (SEPx (Rpost vret)))%assert),

@semax cs (Concurrent_Espec unit cs ext_link) Delta
  (tc_exprlist Delta (argtypes argsig) bl &&
   (` (Pre witness)  (make_args' (argsig, Tvoid)
                          (eval_exprlist (argtypes argsig) bl)) *
    PROPx P (LOCALx Q (SEPx Frame))))
  (Scall None
     (Evar (ext_link "acquire")
        (Tfunction (type_of_params argsig) Tvoid
           cc_default)) bl)
  (normal_ret_assert
     (` (Post witness)
        (make_args [] []) * PROPx P (LOCALx Q (SEPx Frame)))) ->
 @semax  cs (Concurrent_Espec unit cs ext_link)  Delta (PROPx P (LOCALx Q (SEPx R)))
  (Scall None
     (Evar (ext_link "acquire")
        (Tfunction (type_of_params argsig) Tvoid cc_default)) bl)
  (normal_ret_assert
     (EX vret : B,
      PROPx (P ++ Ppost vret) (LOCALx Q (SEPx (Rpost vret ++ Frame))))%assert).
Proof.
intros.
eapply semax_pre_post; [ | | apply H].
*
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- ?D && PROPx ?A ?B |-- ?C =>
  apply derives_trans with (D && PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- insert_prop | ]
 end.
 apply andp_right; [apply andp_left1; auto | ].
 apply andp_right; [| apply andp_left2; auto].
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl;
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
apply derives_extract_PROP; intro LEN.
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
rewrite PROP_combine.
rewrite (andp_comm (local (fold_right _ _ _))).
apply andp_right.
apply andp_right.
apply andp_left2.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
apply andp_left2.
apply andp_left2.
apply andp_derives.
apply derives_refl.
intro rho; unfold SEPx.
 rewrite fold_right_sepcon_app.
 assumption.
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=nil) in MSUBST.
 rewrite PTREE.
 intro rho.
 unfold local, lift1. unfold_lift. simpl.
 apply andp_left2.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 unfold local at 1, lift1.
 simpl.
 apply derives_extract_prop; intro. unfold_lift in H. subst vl.
 unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left1.
 assert (LEN': length (var_names argsig) = length (eval_exprlist (argtypes argsig) bl rho)).
 clear - LEN.
  revert bl LEN; induction argsig as [ | [? ?]]; destruct bl;
    simpl; intros; auto.
 inv LEN.
 forget (argtypes argsig) as tys.
 cut (local (fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil))) rho |--
            `(local (fold_right `and `True (map locald_denote Qpre)))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |].
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 unfold ifvoid.
 go_lowerx. normalize.
 apply exp_right with x.
 normalize.
 apply andp_right.
 apply prop_right.
 rewrite fold_right_and_app_low.
 split; auto.
 rewrite fold_right_sepcon_app. auto.
Qed.

(* Same lemma as [semax_call_id00_wow] but it concerns only the
   functions listed in [threadlib_specs], which, in addition to being
   external, need an additional parameter [witness'] of type, for
   example, [mpred], on which quantifying directly in the WITH clause
   would result in a universe inconsistency. *)



Lemma semax_call_id00_wow_threads:
  forall  {A} {A'} (witness: A) (witness' : A')
     (Frame: list mpred)
     (* Espec *) {cs: compspecs} Delta P Q R id (paramty: typelist) (bl: list expr)
     (argsig: list (ident * type)) (retty: type) cc (Pre Post: A -> environ -> mpred)
     ffunspec
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (NAME: find_in_threadlib_specs id = Some (existT (fun x => x -> funspec) A' ffunspec))
   (FUNSPEC: ffunspec witness' = mk_funspec (argsig, Tvoid) cc A Pre Post)
   (* (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,Tvoid) cc A Pre Post)) *)
   (* (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) cc A Pre Post))) *)
   (RETTY: retty = Tvoid)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |-- (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs (Concurrent_Espec unit cs ext_link) Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty Tvoid cc))
             bl)
    (normal_ret_assert Post2).
Proof.

intros.
subst.
unfold find_in_threadlib_specs, threadlib_specs in NAME.
simpl in NAME.
repeat if_tac in NAME.

* (* acquire *)
  subst id.
  injection NAME.
  intros.
  revert FUNSPEC.
  subst A'.
  apply inj_pair2 in H; subst ffunspec. clear NAME.
  intros.
  unfold acquire_spec in FUNSPEC.
  revert PRE1 POST1.
  inv FUNSPEC.
  intros.
  apply inj_pair2 in H3.
  apply inj_pair2 in H4.
  eapply semax_call_00_helper; try eassumption.
  (* eapply semax_acquire; auto; try assumption. *)
 (*  rewrite <- H3; reflexivity. *)
 (* rewrite <- H4; reflexivity. *)
Abort.

(* We need different tactics for them, if only because we have an
   additional witness, which would conflict with the intropattern
   notation. *)

(* tactics from branch VST.concurrency *)

(*
Ltac forward_call_id00_wow_threadlib witness witness' :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id00_wow_threadlib witness witness' Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity
 | prove_local2ptree | repeat constructor
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta iota;
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    first [reflexivity | extensionality; simpl; reflexivity]
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac fwd_call'_threadlib witness witness' :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 first [
     revert witness;
     match goal with |- let _ := ?A in _ => intro; fwd_call'_threadlib A witness'
     end
   | eapply semax_seq';
     [first [forward_call_id1_wow witness
           | forward_call_id1_x_wow witness
           | forward_call_id1_y_wow witness
           | forward_call_id01_wow witness ]
     | after_forward_call
     ]
  |  eapply semax_seq'; [forward_call_id00_wow_threadlib witness witness'
          | after_forward_call ]
  | rewrite <- seq_assoc; fwd_call'_threadlib witness witness'
  ].

Tactic Notation "forward_call_threadlib" constr(witness) constr(witness') simple_intropattern_list(v) :=
    (* (* we don't need this check (as our specs are canonical),
          and it stack overflows *)
    check_canonical_call; *)
    check_Delta;
    fwd_call'_threadlib witness witness';
  [ ..
  | first
      [ (* body of uniform_intros tactic *)
         (((assert True by (intros v; apply I);
            assert (forall a: unit, True) by (intros v; apply I);
            fail 1)
          || intros v)
        || idtac);
        (* end body of uniform_intros tactic *)
        match goal with
        | |- semax _ _ _ _ => idtac
        | |- unit -> semax _ _ _ _ => intros _
        end;
        repeat (apply semax_extract_PROP; intro);
       abbreviate_semax;
       try fwd_skip
     | complain_intros
     ]
  ].
*)
End threadlib.
