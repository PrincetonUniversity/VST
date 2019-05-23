Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Require Import VST.progs.fupd.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Export Ensembles.

Set Bullet Behavior "Strict Subproofs".

(* Thoughts on invariants and the two-level structure:
   I expect that our version of the operational semantics will keep nonatomic locations as is,
   so that the points-to assertions won't need view parameters (and in fact will be objective?).
   The question then is: do we need the two-level structure in which iGPS-style assertions are
   functions from view to mpred, or can even protocol assertions simply be mpreds? We might be able
   to use something like the external state construction to use ghost state to remember per-thread
   timestamps, so that we don't need to include timestamps in the rmap (or as an extra argument
   to assertions). In this model, there would be no objectivity requirement at all: instead,
   protocol assertions from other threads would be incompatible with the current thread because
   they refer to a different location for their timestamp ghost state.
   On the other hand, if we do need the two-level structure, we should still define invariants
   without objectivity here (as Iris-level invariants), and define iGPS-level invariants elsewhere. *)
(* We will still, of course, have to choose between SC and RA atomics in any given proof/program,
   since there's no soundness proof (or operational model) for a language with both. And invariants
   must still be accessible only via atomics. Does this make the fancy-update style useless,
   since we can't insert it into the definition of semax? Well, iGPS still uses it in the RA atomic
   rules, so maybe it's still useful. *)

Section atomics.

Context {CS : compspecs} {inv_names : invG}.

Section atomicity.

(* up *)
Lemma emp_dup: forall P, P && emp = (P && emp) * (P && emp).
Proof.
  intros.
  apply (predicates_hered.pred_ext _ (P && emp)).
  - intros a [H Hemp].
    exists a, a; split.
    { apply identity_unit'; auto. }
    split; split; auto.
  - intros ? (? & ? & J & [? Hemp1] & [? Hemp2]).
    pose proof (Hemp1 _ _ J); specialize (Hemp2 _ _ (join_comm J)); subst.
    split; auto.
Qed.

(* The logical atomicity of Iris. *)
(* We use the cored predicate to mimic Iris's persistent modality. *)
Definition atomic_shift {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) :=
  EX P : mpred, |> P * ((|> P -* |={Eo,Ei}=> (EX x : A, a x *
    ((a x -* |={Ei,Eo}=> |> P) &&
     ALL y : B, b x y -* |={Ei,Eo}=> Q y))) && cored).

End atomicity.

End atomics.

Definition atomic_spec_type W T := ProdType (ProdType W (ArrowType (ConstType T) Mpred)) (ConstType invG).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> predicates_hered.pred rmap) :=
  forall n ts w x, approx n (a ts w x) =
  approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> B -> predicates_hered.pred rmap) :=
  forall n ts w x y, approx n (b ts w x y) =
  approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x y).

Definition super_non_expansive_la {W} la := forall n ts w rho,
  Forall (fun l => approx n (!! locald_denote (l ts w) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w)) rho)) la.

Definition super_non_expansive_lb {B W} lb := forall n ts w (v : B) rho,
  Forall (fun l => approx n (!! locald_denote (l ts w v) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) v) rho)) lb.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} W args tz la P a (t : T) lb b Ei Eo
  (Hla : super_non_expansive_la la) (HP : super_non_expansive' P) (Ha : super_non_expansive_a(A := A) a)
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
  (fun (ts: list Type) '(w, Q, inv_names) =>
    PROP ()
    (LOCALx (map (fun l => l ts w) la)
    (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Q v)))) _ _.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (x : _ * (T -> mpred) * _) rho =>
    PROP ()
    (LOCALx (map (fun Q0 => Q0 ts x) (map (fun l ts x => let '(x, Q, _) := x in l ts x) la))
     SEP (let '(x, Q, inv_names) := x in
          atomic_shift(inv_names := inv_names) (a ts x) Ei Eo (b ts x) Q * P ts x)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []
    (map (fun l ts x => let '(x, Q, _) := x in l ts x) la) [fun _ => _]);
    repeat constructor; hnf; intros; try destruct x as ((x, Q), ?); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? ((x, Q), ?) ?.
    specialize (Hla n ts x rho); rewrite Forall_forall in Hla; apply (Hla _ Hin).
  - unfold atomic_shift.
    rewrite !approx_sepcon; f_equal; auto.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon, !approx_andp; f_equal; f_equal.
    setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; f_equal.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon, !approx_andp; f_equal; auto.
    f_equal.
    + setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; auto.
    + rewrite !approx_allp by auto; f_equal; extensionality.
      setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; auto.
      rewrite approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((?, ?), ?).
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (w : _ * (T -> mpred) * invG) rho =>
    EX v : T, PROP ()
    (LOCALx (map (fun Q0 => Q0 ts w) (map (fun l ts w => let '(w, Q, _) := w in l ts w v) lb))
     SEP (let '(w, Q, _) := w in Q v)) rho).
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []
    (map (fun l ts w => let '(w, Q, _) := w in l ts w v) lb)
    [fun ts w => let '(w, Q, _) := w in Q v]);
    repeat constructor; hnf; intros; try destruct x0 as ((x0, Q), ?); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? ((x', Q), ?) ?.
    specialize (Hlb n0 ts0 x' v rho0); rewrite Forall_forall in Hlb; apply (Hlb _ Hin).
  - rewrite approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((?, ?), ?).
    apply f_equal; extensionality.
    unfold SEPx; simpl; rewrite map_map; auto.
Qed.

Ltac start_atomic_function :=
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end; unfold atomic_spec;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList ((x, Q), inv_names)
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax; simpl.
