Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Events.
Require Import Maps.
Require Import Switch.
Require Import Globalenvs.

Require Import sepcomp.Cminor.
Require Import sepcomp.mem_lemmas. (*for mem_forward and wd_mem*)
Require Import sepcomp.core_semantics.

(*Obtained from Cminor.state by deleting the memory components.*)
Inductive CMin_core: Type :=
  | CMin_State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env),                   (**r current local environment *)
      CMin_core
  | CMin_Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                  (**r what to do next  *)
      CMin_core
  | CMin_Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                  (**r what to do next *)
      CMin_core.

Definition ToState (q:CMin_core) (m:mem): Cminor.state :=
  match q with
     CMin_State f s k sp e => State f s k sp e m
   | CMin_Callstate f args k => Callstate f args k m
   | CMin_Returnstate v k => Returnstate v k m
  end.

Definition FromState (c: Cminor.state) : CMin_core * mem :=
  match c with
     State f s k sp e m => (CMin_State f s k sp e, m)
   | Callstate f args k m => (CMin_Callstate f args k, m)
   | Returnstate v k m => (CMin_Returnstate v k, m)
  end.
(*
Definition CMin_init_mem (ge:genv)  (m:mem) d:  Prop:=
   Genv.alloc_variables ge Mem.empty d = Some m.
(*Defined initial memory, by adapting the definition of Genv.init_mem*)
*)

(* initial_core : G -> val -> list val -> option C;*)
Definition CMin_initial_core (ge:Cminor.genv) (v: val) (args:list val): option CMin_core :=
   match v with
        Vptr b i =>
          if Int.eq_dec i  Int.zero
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => Some (CMin_Callstate f args Kstop)
               end
          else None
      | _ => None
   end.

(*
Parameter CMin_MainIdent:ident.

Definition CMin_make_initial_core (ge:genv) (v: val) (args:list val): option CMin_core :=
   match Genv.find_symbol ge CMin_MainIdent with
        None => None
      | Some b => match Genv.find_funct_ptr ge b with
                    None => None
                  | Some f => match funsig f with
                                           {| sig_args := sargs; sig_res := sres |} =>
                                                   match sargs, sres with
                                                      nil, Some Tint => Some (CMin_Callstate f nil Kstop) (*args = nil???*)
                                                   | _ , _ => None
                                                   end
                                       end
                  end
   end.
*)
(*Original Cminor_semantics has this for initial states:
Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).*)

Definition CMin_at_external (c: CMin_core) : option (external_function * signature * list val) :=
  match c with
  | CMin_State f s k sp e => None
  | CMin_Callstate fd args k => match fd with
                                  Internal f => None
                                | External ef => Some (ef, ef_sig ef, args)
                              end
  | CMin_Returnstate v k => None
 end.

Definition CMin_after_external (vret: option val) (c: CMin_core) : option CMin_core :=
  match c with
    CMin_Callstate fd args k =>
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (CMin_Returnstate Vundef k)
                           | Some v => Some (CMin_Returnstate v k)
                           end
         end
  | _ => None
  end.

Inductive CMin_corestep (ge : genv) : CMin_core -> mem -> CMin_core -> mem -> Prop:=
  | cmin_corestep_skip_seq: forall f s k sp e m,
      CMin_corestep ge (CMin_State f Sskip (Kseq s k) sp e) m
       (CMin_State f s k sp e) m
  | cmin_corestep_skip_block: forall f k sp e m,
      CMin_corestep ge (CMin_State f Sskip (Kblock k) sp e) m
       (CMin_State f Sskip k sp e) m
  | cmin_corestep_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMin_corestep ge (CMin_State f Sskip k (Vptr sp Int.zero) e) m
       (CMin_Returnstate Vundef k) m'

  | cmin_corestep_assign: forall f id a k sp e m v,
      eval_expr ge sp e m a v ->
      CMin_corestep ge (CMin_State f (Sassign id a) k sp e) m
       (CMin_State f Sskip k sp (PTree.set id v e)) m

  | cmin_corestep_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr ge sp e m addr vaddr ->
      eval_expr ge sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      CMin_corestep ge (CMin_State f (Sstore chunk addr a) k sp e) m
       (CMin_State f Sskip k sp e) m'

  | cmin_corestep_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      CMin_corestep ge (CMin_State f (Scall optid sig a bl) k sp e) m
       (CMin_Callstate fd vargs (Kcall optid f sp e k)) m

  | cmin_corestep_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr ge (Vptr sp Int.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMin_corestep ge (CMin_State f (Stailcall sig a bl) k (Vptr sp Int.zero) e) m
       (CMin_Callstate fd vargs (call_cont k)) m'

(* WE DO NOT TREAT BUILTINS *)
(*  | cmin_corestep_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist ge sp e m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      CMin_corestep ge (CMin_State f (Sbuiltin optid ef bl) k sp e) m
         (CMin_State f Sskip k sp (set_optvar optid vres e)) m'*)

  | cmin_corestep_seq: forall f s1 s2 k sp e m,
      CMin_corestep ge (CMin_State f (Sseq s1 s2) k sp e) m
       (CMin_State f s1 (Kseq s2 k) sp e) m

  | cmin_corestep_ifthenelse: forall f a s1 s2 k sp e m v b,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      CMin_corestep ge (CMin_State f (Sifthenelse a s1 s2) k sp e) m
       (CMin_State f (if b then s1 else s2) k sp e) m

  | cmin_corestep_loop: forall f s k sp e m,
      CMin_corestep ge (CMin_State f (Sloop s) k sp e) m
       (CMin_State f s (Kseq (Sloop s) k) sp e) m

  | cmin_corestep_block: forall f s k sp e m,
      CMin_corestep ge (CMin_State f (Sblock s) k sp e) m
       (CMin_State f s (Kblock k) sp e) m

  | cmin_corestep_exit_seq: forall f n s k sp e m,
      CMin_corestep ge (CMin_State f (Sexit n) (Kseq s k) sp e) m
       (CMin_State f (Sexit n) k sp e) m
  | cmin_corestep_exit_block_0: forall f k sp e m,
      CMin_corestep ge (CMin_State f (Sexit O) (Kblock k) sp e) m
       (CMin_State f Sskip k sp e) m
  | cmin_corestep_exit_block_S: forall f n k sp e m,
      CMin_corestep ge (CMin_State f (Sexit (S n)) (Kblock k) sp e) m
       (CMin_State f (Sexit n) k sp e) m

  | cmin_corestep_switch: forall f a cases default k sp e m n,
      eval_expr ge sp e m a (Vint n) ->
      CMin_corestep ge (CMin_State f (Sswitch a cases default) k sp e) m
       (CMin_State f (Sexit (switch_target n default cases)) k sp e) m

  | cmin_corestep_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMin_corestep ge (CMin_State f (Sreturn None) k (Vptr sp Int.zero) e) m
       (CMin_Returnstate Vundef (call_cont k)) m'
  | cmin_corestep_return_1: forall f a k sp e m v m',
      eval_expr ge (Vptr sp Int.zero) e m a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      CMin_corestep ge (CMin_State f (Sreturn (Some a)) k (Vptr sp Int.zero) e) m
       (CMin_Returnstate v (call_cont k)) m'

  | cmin_corestep_label: forall f lbl s k sp e m,
      CMin_corestep ge (CMin_State f (Slabel lbl s) k sp e) m
       (CMin_State f s k sp e) m

  | cmin_corestep_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      CMin_corestep ge (CMin_State f (Sgoto lbl) k sp e) m
       (CMin_State f s' k' sp e) m

  | cmin_corestep_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      CMin_corestep ge (CMin_Callstate (Internal f) vargs k) m
       (CMin_State f f.(fn_body) k (Vptr sp Int.zero) e) m'
(*no external call
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      sCMin_coretep (CMin_Callstate (External ef) vargs k) m
         t (CMin_Returnstate vres k m') *)

  | cmin_corestep_return: forall v optid f sp e k m,
      CMin_corestep ge (CMin_Returnstate v (Kcall optid f sp e k)) m
       (CMin_State f Sskip k sp (set_optvar optid v e)) m.

Lemma CMin_corestep_not_at_external:
       forall ge m q m' q', CMin_corestep ge q m q' m' -> CMin_at_external q = None.
  Proof. intros. inv H; reflexivity. Qed.

(*LENB: Cminor.v requires v to be Vint i -should we keep this condition?*)
Definition CMin_halted (q : CMin_core): option val :=
    match q with
       CMin_Returnstate v Kstop => Some v
     | _ => None
    end.

Lemma CMin_corestep_not_halted : forall ge m q m' q',
       CMin_corestep ge q m q' m' -> CMin_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.

Lemma CMin_at_external_halted_excl :
       forall q, CMin_at_external q = None \/ CMin_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CMin_after_at_external_excl : forall retv q q',
      CMin_after_external retv q = Some q' -> CMin_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CMin_core_sem : CoreSemantics genv CMin_core mem.
  eapply @Build_CoreSemantics with (at_external:=CMin_at_external)
                  (after_external:=CMin_after_external) (corestep:=CMin_corestep)
                  (halted:=CMin_halted).
    apply CMin_initial_core.
    apply CMin_corestep_not_at_external.
    apply CMin_corestep_not_halted.
    apply CMin_at_external_halted_excl.
    apply CMin_after_at_external_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma CMin_forward : forall g c m c' m' (CS: CMin_corestep g c m c' m'),
      mem_lemmas.mem_forward m m'.
  Proof. intros.
     inv CS; try apply mem_forward_refl.
         eapply free_forward; eassumption.
         (*Storev*)
          destruct vaddr; simpl in H1; inv H1.
          eapply store_forward; eassumption.
         eapply free_forward; eassumption.
         (*builtin*)
          (*eapply external_call_mem_forward; eassumption.*)
         eapply free_forward; eassumption.
         eapply free_forward; eassumption.
         eapply alloc_forward; eassumption.
Qed.

Program Definition cmin_coop_sem :
  CoopCoreSem Cminor.genv CMin_core.
apply Build_CoopCoreSem with (coopsem := CMin_core_sem).
  apply CMin_forward.
Defined.