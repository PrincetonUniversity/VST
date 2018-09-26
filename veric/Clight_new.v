Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require compcert.common.Globalenvs.

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
  | Kloop2 _ _ :: k' => k'
  | Kswitch :: k' => k'
  | _ =>  nil (* stuck *)
  end.

Inductive corestate :=
 | State: forall (ve: env) (te: temp_env) (k: cont), corestate
 | ExtCall: forall (ef: external_function) (args: list val)
                   (lid: option ident) (ve: env) (te: temp_env) (k: cont),
                corestate.

Fixpoint strip_skip (k: cont) : cont :=
 match k with Kseq Sskip :: k' => strip_skip k' | _ => k end.

Definition cl_at_external (c: corestate) : option (external_function * list val) :=
  match c with
  | State _ _ k => None
  | ExtCall ef args lid ve te k => Some (ef, args)
 end.

Definition cl_after_external (vret: option val) (c: corestate) : option corestate :=
  match vret, c with
  | Some v, ExtCall ef args (Some id) ve te k => Some (State ve (PTree.set id v te) k)
  | None, ExtCall ef args (Some id) ve te k => Some (State ve (PTree.set id Vundef te) k)
  | Some v, ExtCall ef args None ve te k => Some (State ve te k)
  | None, ExtCall ef args None ve te k => Some (State ve te k)
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
  | LSnil => None
  | LScons _ s sl' =>
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
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      Clight.assign_loc ge (typeof a1) m loc ofs v m' ->
      cl_step ge (State ve te (Kseq (Sassign a1 a2):: k)) m (State ve te k) m'

  | step_set:   forall ve te k m id a v,
      Clight.eval_expr ge ve te m a v ->
      cl_step ge (State ve te (Kseq (Sset id a) :: k)) m (State ve (PTree.set id v te) k) m

  | step_call_internal:   forall ve te k m optid a al tyargs tyres cc vf vargs f m1 ve' le',
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cc ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction tyargs tyres cc ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_temps)) ->
      forall (NRV: list_norepet (var_names f.(fn_vars))),
      Clight.alloc_variables ge empty_env m (f.(fn_vars)) ve' m1 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some
le' ->
      cl_step ge (State ve te (Kseq (Scall optid a al) :: k)) m
                   (State ve' le' (Kseq f.(fn_body) :: Kseq (Sreturn None) :: Kcall optid f ve te :: k)) m1

  | step_call_external:   forall ve te k m optid a al tyargs tyres cc vf vargs ef,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cc ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (External ef tyargs tyres cc) ->
      cl_step ge (State ve te (Kseq (Scall optid a al) :: k)) m (ExtCall ef vargs optid ve te k) m

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
      Cop.bool_val v1 (typeof a) m = Some b ->
      cl_step ge (State ve te (Kseq (Sifthenelse a s1 s2) :: k)) m (State ve te  (Kseq (if b then s1 else s2) :: k)) m

  | step_for: forall ve te k m s1 s2,
      cl_step ge (State ve te (Kseq (Sloop s1 s2) :: k)) m
              (State ve te (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: k)) m

  | step_loop2: forall ve te k m a3 s,
      cl_step ge (State ve te (Kloop2 s a3 :: k)) m
             (State ve te (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: k)) m

  | step_return: forall f ve te optexp optid k m v' m' ve' te' te'' k',
      call_cont k = Kcall optid f ve' te' :: k' ->
      Mem.free_list m (Clight.blocks_of_env ge ve) = Some m' ->
      match optexp with None => v' = Vundef
                                  | Some a => exists v, Clight.eval_expr ge ve te m a v
                                     /\ Cop.sem_cast v (typeof a) f.(fn_return) m = Some v'
                            end ->
      match optid with None => True /\ te''=te'
                                | Some id => True /\ te'' = PTree.set id v' te'
      end ->
      cl_step ge (State ve te (Kseq (Sreturn optexp) :: k)) m (State ve' te'' k') m'

  | step_switch: forall ve te k m a sl v n,
      Clight.eval_expr ge ve te m a v ->
      Cop.sem_switch_arg v (typeof a) = Some n ->
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

(* Definition exit_syscall_number : ident := 1%positive. *)

Definition cl_halted (c: corestate) : option val := None.

Definition empty_function : function := mkfunction Tvoid cc_default nil nil nil Sskip.

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

Fixpoint params_of_types (i: positive) (l : list type) : list (ident * type) :=
  match l with
  | nil => nil
  | t :: l => (i, t) :: params_of_types (i+1)%positive l
  end.

Fixpoint typelist2list (tl: typelist) : list type :=
  match tl with
  | Tcons t r => t::typelist2list r
  | Tnil => nil
  end.

Definition params_of_fundef (f: fundef) : list type :=
  match f with
  | Internal {| fn_params := fn_params |} => map snd fn_params
  | External _ t _ _ => typelist2list t
  end.

Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons  ty1 tyl).

Definition cl_initial_core (ge: genv) (v: val) (args: list val) (q: corestate) : Prop :=
  match v with
    Vptr b i =>
    if Ptrofs.eq_dec i Ptrofs.zero then
      match Genv.find_funct_ptr ge b with
        Some f =>
        match type_of_fundef f with Tfunction targs _ c =>
        c = cc_default /\
        val_casted_list args targs /\
        Val.has_type_list args (Ctypes.typlist_of_typelist targs) /\
        q = State empty_env (temp_bindings 1%positive (v::args))
                    (Kseq (Scall None
                                 (Etempvar 1%positive (type_of_fundef f))
                                 (map (fun x => Etempvar (fst x) (snd x))
                                      (params_of_types 2%positive
                                                       (params_of_fundef f)))) ::
                          Kseq (Sloop Sskip Sskip) :: nil)
        | _ => False end
      | _ => False end
    else False
  | _ => False
end.

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

Definition arg_well_formed args m0:=
  Val.inject_list (Mem.flat_inj (Mem.nextblock m0)) args args.

Program Definition cl_core_sem  (ge: genv):
  @CoreSemantics corestate mem :=
  @Build_CoreSemantics _ _
    (*deprecated cl_init_mem*)
    (fun _ m c m' v args => cl_initial_core ge v args c /\ arg_well_formed args m /\ m' = m)
    (fun c _ => cl_at_external c)
    (fun ret c _ => cl_after_external ret c)
    (fun c _ =>  False (*cl_halted c <> None*))
    (cl_step ge)
    _
    (cl_corestep_not_at_external ge).

Lemma cl_corestep_fun: forall ge m q m1 q1 m2 q2,
    cl_step ge q m q1 m1 ->
    cl_step ge q m q2 m2 ->
    (q1,m1)=(q2,m2).
Proof.
intros.
rename H0 into STEP;
revert q2 m2 STEP; induction H; intros; inv STEP; simpl; auto; repeat fun_tac; auto.
inversion2 H H13.
 repeat fun_tac; auto.
destruct optexp. destruct H1 as [v [? ?]]. destruct H12 as [v2 [? ?]].
repeat fun_tac.
inversion2 H H7.
 inversion2 H3 H5.
destruct optid. destruct H2,H13. subst. auto. destruct H13,H2; subst; auto.
 inversion2 H H7.
 destruct optid. destruct H2,H13; congruence. destruct H2,H13. subst. auto.
Qed.
