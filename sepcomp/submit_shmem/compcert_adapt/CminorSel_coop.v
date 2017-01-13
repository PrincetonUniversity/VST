Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Maps.
Require Import Switch.

Require Import sepcomp.CminorSel.
Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.

Inductive CMinSel_core: Type :=
  | CMinSel_State:                      (**r execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: Cminor.env),           (**r current local environment *)
      CMinSel_core
  | CMinSel_Callstate:                  (**r invocation of a fundef  *)
      forall (f: fundef)                (**r fundef to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      CMinSel_core
  | CMinSel_Returnstate:
      forall (v: val)                   (**r return value *)
             (k: cont),                 (**r what to do next *)
      CMinSel_core.

Definition ToState (q:CMinSel_core) (m:mem): CminorSel.state :=
  match q with
     CMinSel_State f s k sp e => State f s k sp e m
   | CMinSel_Callstate f args k => Callstate f args k m
   | CMinSel_Returnstate v k => Returnstate v k m
  end.

Definition FromState (c: CminorSel.state) : CMinSel_core * mem :=
  match c with
     State f s k sp e m => (CMinSel_State f s k sp e, m)
   | Callstate f args k m => (CMinSel_Callstate f args k, m)
   | Returnstate v k m => (CMinSel_Returnstate v k, m)
  end.

Definition CMinSel_at_external (c: CMinSel_core) : option (external_function * signature * list val) :=
  match c with
  | CMinSel_State _ _ _ _ _ => None
  | CMinSel_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef => Some (ef, ef_sig ef, args)
                              end
  | CMinSel_Returnstate v k => None
 end.

Definition CMinSel_after_external (vret: option val) (c: CMinSel_core) : option CMinSel_core :=
  match c with
    CMinSel_Callstate fd args k =>
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (CMinSel_Returnstate Vundef k)
                           | Some v => Some (CMinSel_Returnstate v k)
                           end
         end
  | _ => None
  end.

Inductive CMinSel_corestep (ge : genv) : CMinSel_core -> mem ->
                           CMinSel_core -> mem -> Prop:=

  | cminsel_corestep_skip_seq: forall f s k sp e m,
      CMinSel_corestep ge (CMinSel_State f Sskip (Kseq s k) sp e) m
        (CMinSel_State f s k sp e) m
  | cminsel_corestep_skip_block: forall f k sp e m,
      CMinSel_corestep ge (CMinSel_State f Sskip (Kblock k) sp e) m
        (CMinSel_State f Sskip k sp e) m
  | cminsel_corestep_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMinSel_corestep ge (CMinSel_State f Sskip k (Vptr sp Int.zero) e) m
        (CMinSel_Returnstate Vundef k) m'

  | cminsel_corestep_assign: forall f id a k sp e m v,
      eval_expr ge sp e m nil a v ->
      CMinSel_corestep ge (CMinSel_State f (Sassign id a) k sp e) m
        (CMinSel_State f Sskip k sp (PTree.set id v e)) m

  | cminsel_corestep_store: forall f chunk addr al b k sp e m vl v vaddr m',
      eval_exprlist ge sp e m nil al vl ->
      eval_expr ge sp e m nil b v ->
      eval_addressing ge sp addr vl = Some vaddr ->
      Mem.storev chunk m vaddr v = Some m' ->
      CMinSel_corestep ge (CMinSel_State f (Sstore chunk addr al b) k sp e) m
        (CMinSel_State f Sskip k sp e) m'

  | cminsel_corestep_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr_or_symbol ge sp e m nil a vf ->
      eval_exprlist ge sp e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      CMinSel_corestep ge (CMinSel_State f (Scall optid sig a bl) k sp e) m
        (CMinSel_Callstate fd vargs (Kcall optid f sp e k)) m

  | cminsel_corestep_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr_or_symbol ge (Vptr sp Int.zero) e m nil a vf ->
      eval_exprlist ge (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMinSel_corestep ge (CMinSel_State f (Stailcall sig a bl) k (Vptr sp Int.zero) e) m
        (CMinSel_Callstate fd vargs (call_cont k)) m'

(* WE DO NOT TREAT BUILTINS
  | cminsel_corestep_builtin: forall f optid ef al k sp e m vl t v m',
      eval_exprlist ge sp e m nil al vl ->
      external_call ef ge vl m t v m' ->
      CMinSel_corestep ge (CMinSel_State f (Sbuiltin optid ef al) k sp e) m
         (CMinSel_State f Sskip k sp (Cminor.set_optvar optid v e)) m'
*)
  | cminsel_corestep_seq: forall f s1 s2 k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sseq s1 s2) k sp e) m
        (CMinSel_State f s1 (Kseq s2 k) sp e) m

  | cminsel_corestep_ifthenelse: forall f c s1 s2 k sp e m b,
      eval_condexpr ge sp e m nil c b ->
      CMinSel_corestep ge (CMinSel_State f (Sifthenelse c s1 s2) k sp e) m
        (CMinSel_State f (if b then s1 else s2) k sp e) m

  | cminsel_corestep_loop: forall f s k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sloop s) k sp e) m
        (CMinSel_State f s (Kseq (Sloop s) k) sp e) m

  | cminsel_corestep_block: forall f s k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sblock s) k sp e) m
        (CMinSel_State f s (Kblock k) sp e) m

  | cminsel_corestep_exit_seq: forall f n s k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sexit n) (Kseq s k) sp e) m
        (CMinSel_State f (Sexit n) k sp e) m
  | cminsel_corestep_exit_block_0: forall f k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sexit O) (Kblock k) sp e) m
        (CMinSel_State f Sskip k sp e) m
  | cminsel_corestep_exit_block_S: forall f n k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Sexit (S n)) (Kblock k) sp e) m
        (CMinSel_State f (Sexit n) k sp e) m

  | cminsel_corestep_switch: forall f a cases default k sp e m n,
      eval_expr ge sp e m nil a (Vint n) ->
      CMinSel_corestep ge (CMinSel_State f (Sswitch a cases default) k sp e) m
        (CMinSel_State f (Sexit (switch_target n default cases)) k sp e) m

  | cminsel_corestep_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMinSel_corestep ge (CMinSel_State f (Sreturn None) k (Vptr sp Int.zero) e) m
        (CMinSel_Returnstate Vundef (call_cont k)) m'
  | cminsel_corestep_return_1: forall f a k sp e m v m',
      eval_expr ge (Vptr sp Int.zero) e m nil a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMinSel_corestep ge (CMinSel_State f (Sreturn (Some a)) k (Vptr sp Int.zero) e) m
        (CMinSel_Returnstate v (call_cont k)) m'

  | cminsel_corestep_label: forall f lbl s k sp e m,
      CMinSel_corestep ge (CMinSel_State f (Slabel lbl s) k sp e) m
        (CMinSel_State f s k sp e) m

  | cminsel_corestep_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      CMinSel_corestep ge (CMinSel_State f (Sgoto lbl) k sp e) m
        (CMinSel_State f s' k' sp e) m

  | cminsel_corestep_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      Cminor.set_locals f.(fn_vars) (Cminor.set_params vargs f.(fn_params)) = e ->
      CMinSel_corestep ge (CMinSel_Callstate (Internal f) vargs k) m
        (CMinSel_State f f.(fn_body) k (Vptr sp Int.zero) e) m'
(*no external call
  | cminsel_corestep_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k) m
         t (Returnstate vres k m')        *)

  | cminsel_corestep_return: forall v optid f sp e k m,
      CMinSel_corestep ge (CMinSel_Returnstate v (Kcall optid f sp e k)) m
        (CMinSel_State f Sskip k sp (Cminor.set_optvar optid v e)) m.

Lemma CMinSel_corestep_not_at_external:
       forall ge m q m' q', CMinSel_corestep ge q m q' m' -> CMinSel_at_external q = None.
  Proof. intros. inv H; reflexivity. Qed.

Definition CMinSel_halted (q : CMinSel_core): option val :=
    match q with
       CMinSel_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CMinSel_corestep_not_halted : forall ge m q m' q',
       CMinSel_corestep ge q m q' m' -> CMinSel_halted q = None.
  Proof. intros. inv H; try reflexivity. Qed.

Lemma CMinSel_at_external_halted_excl :
       forall q, CMinSel_at_external q = None \/ CMinSel_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CMinSel_after_at_external_excl : forall retv q q',
      CMinSel_after_external retv q = Some q' -> CMinSel_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CMinSel_initial_core (ge:genv) (v: val) (args:list val): option CMinSel_core :=
   match v with
     | Vptr b i =>
          if Int.eq_dec i Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CMinSel_Callstate f args Kstop)
               end
          else None
     | _ => None
    end.

Definition CMinSel_core_sem : CoreSemantics genv CMinSel_core mem.
  eapply @Build_CoreSemantics with (at_external:=CMinSel_at_external)
                  (after_external:=CMinSel_after_external)
                  (corestep:=CMinSel_corestep)
                  (halted:=CMinSel_halted).
    apply CMinSel_initial_core.
    apply CMinSel_corestep_not_at_external.
    apply CMinSel_corestep_not_halted.
    apply CMinSel_at_external_halted_excl.
    apply CMinSel_after_at_external_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma CMinSel_forward : forall g c m c' m' (CS: CMinSel_corestep g c m c' m'),
      mem_forward m m'.
  Proof. intros.
     inv CS; try apply mem_forward_refl.
         eapply free_forward; eassumption.
         (*Storev*)
          destruct vaddr; simpl in H2; inv H2.
          eapply store_forward; eassumption.
         eapply free_forward; eassumption.
         (*builtin*)
          (*eapply external_call_mem_forward; eassumption.*)
         eapply free_forward; eassumption.
         eapply free_forward; eassumption.
         eapply alloc_forward; eassumption.
Qed.

Program Definition cminsel_coop_sem :
  CoopCoreSem genv CMinSel_core.
apply Build_CoopCoreSem with (coopsem := CMinSel_core_sem).
  apply CMinSel_forward.
Defined.
