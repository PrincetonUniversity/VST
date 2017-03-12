Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import veric.base.
Require Import veric.Clight_lemmas.


Inductive cont': Type :=
  | Kseq: statement -> cont'       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kloop1: statement -> statement -> cont'
  | Kloop2: statement -> statement  -> cont'
  | Kswitch: cont'       (**r catches [break] statements arising out of [switch] *)
  | Kcall: forall (l: option ident),                  (**r where to store result *)
           function ->                      (**r called (not calling!) function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           cont'.

Definition cont := list cont'.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s :: k => call_cont k
  | Kloop1 _ _ :: k => call_cont k
  | Kloop2 _ _ :: k => call_cont k
  | Kswitch :: k => call_cont k
  | _ => k
  end.

Fixpoint current_function (k: cont) : option function :=
 match k with
  | Kseq s :: k => current_function k
  | Kloop1 _ _ :: k => current_function k
  | Kloop2 _ _:: k =>current_function k
  | Kswitch :: k => current_function k
  | Kcall _ f _ _ :: _ => Some f
  | _ => None
  end.

Fixpoint continue_cont (k: cont) : cont :=
  match k with
  | Kseq s :: k' => continue_cont k'
  | Kloop1 s1 s2 :: k' => Kseq s2 :: Kloop2 s1 s2 :: k'
  | Kswitch :: k' => continue_cont k'
  | _ => nil (* stuck *)
  end.

Lemma call_cont_nonnil: forall k f, current_function k = Some f -> call_cont k <> nil.
  Proof. intros k.
     induction k; simpl; intros. inv H.
     destruct a; eauto. discriminate.
  Qed.

Fixpoint precontinue_cont (k: cont) : cont :=
  match k with
  | Kseq s :: k' => precontinue_cont k'
  | Kloop1 _ _ :: _ => k
  | Kswitch :: k' => precontinue_cont k'
  | _ => nil (* stuck *)
  end.

Fixpoint break_cont (k: cont) : cont :=
  match k with
  | Kseq s :: k' => break_cont k'
  | Kloop1 _ _ :: k' => k'
  | Kloop2 _ _ :: _ => nil  (* stuck *)
  | Kswitch :: k' => k'
  | _ =>  nil (* stuck *)
  end.

Inductive corestate :=
 | State: forall (ve: env) (te: temp_env) (k: cont), corestate
 | ExtCall: forall (ef: external_function) (sig: signature) (args: list val)
                   (lid: option ident) (ve: env) (te: temp_env) (k: cont),
                corestate.

Fixpoint strip_skip (k: cont) : cont :=
 match k with Kseq Sskip :: k' => strip_skip k' | _ => k end.

Definition cl_at_external (c: corestate) : option (external_function * signature *list val) :=
  match c with
  | State _ _ k => None
  | ExtCall ef sig args lid ve te k => Some (ef, sig, args)
 end.

Definition cl_after_external (vret: option val) (c: corestate) : option corestate :=
  match vret, c with
  | Some v, ExtCall ef sig args (Some id) ve te k => Some (State ve (PTree.set id v te) k)
  | None, ExtCall ef sig args None ve te k => Some (State ve te k)
  | _, _ => None
  end.

(** Find the statement and manufacture the continuation
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option cont :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 :: k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 a3 =>
      match find_label lbl s1 (Kseq Scontinue :: Kloop1 s1 a3 :: k) with
      | Some sk => Some sk
      | None => find_label lbl a3 (Kloop2 s1 a3 :: k)
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch :: k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(Kseq s' :: k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option cont :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') :: k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.


(** Transition relation *)

Inductive cl_step (ge: Clight.genv): forall (q: corestate) (m: mem) (q': corestate) (m': mem), Prop :=

  | step_assign: forall ve te k m a1 a2 loc ofs v2 v m',
     type_is_volatile (typeof a1) = false ->
      Clight.eval_lvalue ge ve te m a1 loc ofs ->
      Clight.eval_expr ge ve te m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      Clight.assign_loc (typeof a1) m loc ofs v m' ->
      cl_step ge (State ve te (Kseq (Sassign a1 a2):: k)) m (State ve te k) m'

  | step_set:   forall ve te k m id a v,
      Clight.eval_expr ge ve te m a v ->
      cl_step ge (State ve te (Kseq (Sset id a) :: k)) m (State ve (PTree.set id v te) k) m

  | step_call_internal:   forall ve te k m optid a al tyargs tyres vf vargs f m1 ve' le',
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction tyargs tyres ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_temps)) ->
      forall (NRV: list_norepet (var_names f.(fn_vars))),
      Clight.alloc_variables empty_env m (f.(fn_vars)) ve' m1 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some
le' ->
      cl_step ge (State ve te (Kseq (Scall optid a al) :: k)) m
                   (State ve' le' (Kseq f.(fn_body) :: Kseq (Sreturn None) :: Kcall optid f ve te :: k)) m1

  | step_call_external:   forall ve te k m optid a al tyargs tyres vf vargs ef,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (External ef tyargs tyres) ->
      cl_step ge (State ve te (Kseq (Scall optid a al) :: k)) m (ExtCall ef (signature_of_type tyargs tyres) vargs optid ve te k) m

  | step_seq: forall ve te k m s1 s2 st' m',
          cl_step ge (State ve te (Kseq s1 :: Kseq s2 :: k)) m st' m' ->
          cl_step ge (State ve te (Kseq (Ssequence s1 s2) :: k)) m st' m'

  | step_skip: forall ve te k m st' m',
          cl_step ge (State ve te k) m st' m' ->
          cl_step ge (State ve te (Kseq Sskip :: k)) m st' m'

  | step_continue: forall ve te k m st' m',
           cl_step ge (State ve te (continue_cont k)) m st' m' ->
           cl_step ge (State ve te (Kseq Scontinue :: k)) m st' m'

  | step_break: forall ve te k m st' m',
                   cl_step ge (State ve te (break_cont k)) m st' m' ->
                   cl_step ge (State ve te (Kseq Sbreak :: k)) m st' m'

  | step_ifthenelse:  forall ve te k m a s1 s2 v1 b,
      Clight.eval_expr ge ve te m a v1 ->
      Cop.bool_val v1 (typeof a) = Some b ->
      cl_step ge (State ve te (Kseq (Sifthenelse a s1 s2) :: k)) m (State ve te  (Kseq (if b then s1 else s2) :: k)) m

  | step_for: forall ve te k m s1 s2,
      cl_step ge (State ve te (Kseq (Sloop s1 s2) :: k)) m
              (State ve te (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: k)) m

  | step_loop2: forall ve te k m a3 s,
      cl_step ge (State ve te (Kloop2 s a3 :: k)) m
             (State ve te (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: k)) m

  | step_return: forall f ve te optexp optid k m v' m' ve' te' te'' k',
      call_cont k = Kcall optid f ve' te' :: k' ->
      Mem.free_list m (Clight.blocks_of_env ve) = Some m' ->
      match optexp with None => True
                                  | Some a => exists v, Clight.eval_expr ge ve te m a v /\ Cop.sem_cast v (typeof a) f.(fn_return) = Some v'
                            end ->
      match optid with None => f.(fn_return) = Tvoid /\ te''=te'
                                | Some id => optexp <> None /\ te'' = PTree.set id v' te'
      end ->
      cl_step ge (State ve te (Kseq (Sreturn optexp) :: k)) m (State ve' te'' k') m'

  | step_switch: forall ve te k m a sl n,
      Clight.eval_expr ge ve te m a (Vint n) ->
      cl_step ge (State ve te (Kseq (Sswitch a sl) :: k)) m
              (State ve te (Kseq (seq_of_labeled_statement (select_switch n sl)) :: Kswitch :: k)) m

  | step_label: forall ve te k m lbl s st' m',
       cl_step ge (State ve te (Kseq s :: k)) m st' m' ->
       cl_step ge (State ve te (Kseq (Slabel lbl s) :: k)) m st' m'

  | step_goto: forall f ve te k m lbl k'
                     (* make sure to take a step here, so that every loop ticks the clock *)
      (CUR: current_function k = Some f),
      find_label lbl f.(fn_body) (Kseq (Sreturn None) :: (call_cont k)) = Some k' ->
      cl_step ge (State ve te (Kseq (Sgoto lbl) :: k)) m (State ve te k') m.

Definition vret2v (vret: list val) : val :=
  match vret with v::nil => v | _ => Vundef end.

Definition exit_syscall_number : ident := 1%positive.

Definition cl_halted (c: corestate) : option val := None.

Definition empty_function : function := mkfunction Tvoid nil nil nil Sskip.

Fixpoint temp_bindings (i: positive) (vl: list val) :=
 match vl with
 | nil => PTree.empty val
 | v::vl' => PTree.set i v (temp_bindings (i+1)%positive vl')
 end.

Definition Tint32s := Tint I32 Signed noattr.
Definition true_expr : Clight.expr := Clight.Econst_int Int.one Tint32s.

Fixpoint typed_params (i: positive) (n: nat) : list (ident * type) :=
 match n with
 | O => nil
 | S n' => (i, Tint32s) :: typed_params (i+1)%positive n'
 end.

Definition cl_initial_core (ge: genv) (v: val) (args: list val) : option corestate :=
  let tl := typed_params 2%positive (length args)
   in Some (State empty_env (temp_bindings 1%positive (v::args))
                  (Kseq (Scall None
                                  (Etempvar 1%positive (Tfunction (type_of_params tl) Tvoid))
                                  (map (fun x => Etempvar (fst x) (snd x)) tl)) ::
                     Kseq (Sloop Sskip Sskip) :: nil)).

Lemma cl_corestep_not_at_external:
  forall ge m q m' q', cl_step ge q m q' m' -> cl_at_external q = None.
Proof.
  intros.
  destruct q; simpl; auto. inv H.
Qed.

Lemma cl_corestep_not_halted :
  forall ge m q m' q', cl_step ge q m q' m' -> cl_halted q = None.
Proof.
  intros.
  simpl; auto.
Qed.

Lemma cl_after_at_external_excl :
  forall retv q q', cl_after_external retv q = Some q' -> cl_at_external q' = None.
Proof.
intros until q'; intros H.
unfold cl_after_external in H.
destruct retv; destruct q; try congruence.
destruct lid; try congruence; inv H; auto.
destruct lid; try congruence; inv H; auto.
Qed.

Program Definition cl_core_sem :
  CoreSemantics (Genv.t fundef type) corestate mem :=
  @Build_CoreSemantics _ _ _
    (*deprecated cl_init_mem*)
    cl_initial_core
    cl_at_external
    cl_after_external
    cl_halted
    cl_step
    cl_corestep_not_at_external
    cl_corestep_not_halted _
    cl_after_at_external_excl.

Lemma cl_corestep_fun: forall ge m q m1 q1 m2 q2,
    cl_step ge q m q1 m1 ->
    cl_step ge q m q2 m2 ->
    (q1,m1)=(q2,m2).
Proof.
intros.
rename H0 into STEP;
revert q2 m2 STEP; induction H; intros; inv STEP; simpl; auto; repeat fun_tac; auto.
f_equal; eapply assign_loc_fun; eauto.
inversion2 H H13. repeat fun_tac; auto.
destruct optexp. destruct H1 as [v [? ?]]. destruct H12 as [v2 [? ?]].
repeat fun_tac.
inversion2 H H7.
 inversion2 H3 H5.
destruct optid. destruct H2,H13. subst. auto. destruct H13,H2; subst; auto.
 inversion2 H H7.
 destruct optid. destruct H2; congruence. destruct H2,H13. subst. auto.
inv H; auto.
Qed.

(* NO LONGER NEEDED? *)
(* Lemma free_list_allowed_core_mod : forall m1 l m2, *)
(*   Mem.free_list m1 l = Some m2 -> *)
(*   allowed_core_modification m1 m2. *)
(* Proof. *)
(*   intros m1 l m2; revert m1; induction l; simpl; intros. *)
(*   inv H;   eauto with allowed_mod. *)
(*   destruct a; destruct p; invSome; eauto with allowed_mod. *)
(* Qed. *)

(* Hint Resolve free_list_allowed_core_mod : allowed_mod. *)

(* Lemma storebytes_allowed_core_modification: forall l m m' b z  *)
(*   (H: Mem.storebytes m b z l = Some m'), allowed_core_modification m m'. *)
(* Proof.  *)
(* intros. *)
(* split; intros. *)
(* intros k K1. split; intros.   *)
(* eapply Mem.storebytes_valid_block_1; eassumption. *)
(* eapply Mem.perm_storebytes_2; eassumption. *)
(* split; intros.  left. eapply Mem.perm_storebytes_1; eassumption. *)
(* split; intros. eapply Mem.perm_storebytes_2; eassumption.  *)
(* destruct (zle n 0). *)
(* assert (Y:= Mem.loadbytes_empty m b0 ofs' n z0).  *)
(*   rewrite Y in H0. inv H0. *)
(* left.  apply Mem.loadbytes_empty. assumption.  *)
(* assert (NGEZ: n >= 0).  apply Zle_ge.  apply Zgt_lt in z0.   *)
(*   apply ZOrderedType.Z_as_OT.le_lteq. left; assumption. *)
(* destruct (eq_block b0 b); subst. *)
(* Focus 2. left. rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _  H b0 ofs' n);  *)
(*   try assumption.   *)
(* left; assumption. *)
(* destruct (zle (ofs' + n)  z). *)
(* (*<=*) left. rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ H); try assumption.  *)
(*   right. left. assumption. *)
(* (*>*)  destruct (zle (z +Z_of_nat (length l)) ofs'). *)
(* (*<=*)  left. rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ H); try assumption.  *)
(*   right. right. assumption. *)
(* (*>*)  destruct (zle z ofs').  *)
(* (*<=*) assert (ZZ:= Mem.storebytes_range_perm _ _ _ _ _ H). *)
(* right. exists ofs'. split. split.  apply Zle_refl.   *)
(*   assert (qq:= Zplus_le_lt_compat ofs' ofs' 0 n). rewrite Zplus_0_r in qq. apply qq.   *)
(*   apply Zle_refl. apply Zgt_lt. apply z0. *)
(* apply ZZ. split; try assumption. apply Zgt_lt. assumption. *)
(* (*>*)  destruct (zlt 0 (Z_of_nat (length l))); simpl in *. *)
(* right. exists z. split. omega. *)
(* eapply (Mem.storebytes_range_perm _ _ _ _ _ H). split. apply Zle_refl. omega. *)
(* destruct l; simpl in *. (*case l= nil still unproven*) *)
(* rewrite Zpos_P_of_succ_nat in z4. exfalso. clear - z4.  *)
(*   remember (length l) as xx. clear Heqxx l.  destruct (intro_Z xx).  *)
(*   destruct H. rewrite H in z4.  clear H. omega.  *)
(* Qed. *)

(* Hint Resolve  storebytes_allowed_core_modification: allowed_mod. *)

(* Lemma cl_allowed_modifications : forall ge c m c' m', *)
(*   cl_step ge c m c' m' -> allowed_core_modification m m'. *)
(* Proof. *)
(*   intros. *)
(*   induction H; eauto with allowed_mod. *)
(*   inv H3; eauto with allowed_mod. *)
(*   (*eapply storebytes_allowed_core_modification; eauto.  *)
(*    LENB: storebytes_allowed_core_modification is now in allowed_mod hint database*) *)
(*   apply allowed_core_modification_trans with m1. *)
(*     clear - H5. *)
(*     (*forget (fn_params f ++ fn_vars f) as l.*) *)
(*     induction H5; eauto with allowed_mod. *)
(*     forget (fn_params f) as l. *)
(*     clear - H6; induction H6; eauto with allowed_mod. *)
(* Qed. *)

(* Definition cl_core_sem' :  *)
(*   CompcertCoreSem (Genv.t fundef type) corestate (list (ident*globdef fundef type)) := *)
(*   Build_CompcertCoreSem _ _ _ cl_core_sem cl_corestep_fun cl_allowed_modifications. *)
