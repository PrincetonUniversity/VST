(* Clight SEmantics for Machines*)

(*
  We define event semantics for 
  - Clight_new: the core semantics defined by VST
  - Clightcore: the core semantics derived from 
    CompCert's Clight
*)

Require Import compcert.common.Memory.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

Require Import List. Import ListNotations.

(* The concurrent machinery*)
Require Import VST.concurrency.common.core_semantics.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop. 
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_sim.

Set Bullet Behavior "Strict Subproofs".

Lemma extcall_malloc_sem_inv: forall g v m t res m2 (E:Events.extcall_malloc_sem g v m t res m2),
  exists m1 b (sz : ptrofs), v=[Vptrofs sz] /\ t= Events.E0 /\ res=Vptr b Ptrofs.zero /\
                           Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m1, b) /\
                           Mem.store Mptr m1 b (- size_chunk Mptr) (Vptrofs sz) = Some m2. 
Proof. intros.  inv E. exists m', b, sz. intuition. Qed.

Inductive deref_locT (ty : type) (m : mem) (b : block) (ofs : ptrofs) : val -> list mem_event -> Prop :=
    deref_locT_value : forall (chunk : memory_chunk) bytes,
                      access_mode ty = By_value chunk ->
                      (align_chunk chunk | (Ptrofs.unsigned ofs)) ->
                      Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk chunk) = Some bytes ->
(*                      Mem.load chunk m b (Ptrofs.unsigned ofs) = Some (decode_val chunk bytes) ->*)
                      deref_locT ty m b ofs (decode_val chunk bytes) (Read b (Ptrofs.unsigned ofs) (size_chunk chunk) bytes :: nil)
  | deref_locT_reference : access_mode ty = By_reference -> deref_locT ty m b ofs (Vptr b ofs) nil
  | deref_locT_copy : access_mode ty = By_copy -> deref_locT ty m b ofs (Vptr b ofs) nil.

Lemma deref_locT_ax1 a m loc ofs v T (D:deref_locT (typeof a) m loc ofs v T):
      deref_loc (typeof a) m loc ofs v.
Proof. 
  inv D.
  + eapply deref_loc_value; eauto. eapply Mem.loadbytes_load; eauto.
  + apply deref_loc_reference; trivial.
  + apply deref_loc_copy; trivial.
Qed.

Lemma deref_locT_ax2 a m loc ofs v (D:deref_loc (typeof a) m loc ofs v):
      exists T, deref_locT (typeof a) m loc ofs v T.
Proof. 
  inv D.
  + exploit Mem.load_valid_access; eauto. intros [_ ALGN].
    exploit Mem.load_loadbytes; eauto. intros [bytes [LD V]]; subst v.
    eexists; eapply deref_locT_value; eauto. 
  + eexists; apply deref_locT_reference; trivial.
  + eexists; apply deref_locT_copy; trivial.
Qed.

Lemma deref_locT_fun a m loc ofs v1 T1 (D1:deref_locT (typeof a) m loc ofs v1 T1)
      v2 T2 (D2:deref_locT (typeof a) m loc ofs v2 T2): (v1,T1)=(v2,T2). 
Proof. inv D1; inv D2; try congruence. Qed.

Lemma deref_locT_elim  a m b ofs v T (D:deref_locT (typeof a) m b ofs v T):
       ev_elim m T m /\
       (forall mm mm' (E:ev_elim mm T mm'),
           mm'=mm /\ deref_locT (typeof a) mm b ofs v T).
Proof.
  inv D; simpl.
  { intuition. subst. eapply deref_locT_value; trivial. }
  { intuition. subst. eapply deref_locT_reference; trivial. }
  { intuition. subst. eapply deref_locT_copy; trivial. }
Qed. 

Inductive alloc_variablesT (g: genv): PTree.t (block * type) -> mem -> list (ident * type) ->
                                      PTree.t (block * type) -> mem -> (list mem_event) -> Prop :=
    alloc_variablesT_nil : forall e m, alloc_variablesT g e m nil e m nil
  | alloc_variablesT_cons :
      forall e m id ty vars m1 b1 m2 e2 T,
        Mem.alloc m 0 (@sizeof g ty) = (m1, b1) ->
        alloc_variablesT g (PTree.set id (b1, ty) e) m1 vars e2 m2 T ->
        alloc_variablesT g e m ((id, ty) :: vars) e2 m2 (Alloc b1 0 (@sizeof g ty) :: T).

Lemma alloc_variablesT_ax1 g: forall e m l e' m' T (A:alloc_variablesT g e m l e' m' T),
    alloc_variables g e m l e' m'.
Proof. intros. induction A. constructor. econstructor; eauto. Qed. 

Lemma alloc_variablesT_ax2 g: forall e m l e' m' (A:alloc_variables g e m l e' m'),
    exists T, alloc_variablesT g e m l e' m' T.
Proof. intros. induction A. exists nil. constructor.
       destruct IHA. eexists. econstructor; eauto.
Qed. 
    
Lemma alloc_variablesT_fun g: forall e m l e' m' T' (A:alloc_variablesT g e m l e' m' T')
                                     e2 m2 T2 (A2:alloc_variablesT g e m l e2 m2 T2),
     (e',m',T') = (e2,m2,T2).
Proof. intros until T'. intros A; induction A; intros.
       + inv A2. trivial.
       + inv A2. rewrite H8 in H; inv H. apply IHA in H9; inv H9. trivial.
Qed. 
   
Lemma alloc_variablesT_elim g:
  forall e m l e' m' T (A:alloc_variablesT g e m l e' m' T),
       ev_elim m T m' /\
       (forall mm mm' (E:ev_elim mm T mm'),
           (*exists e',*) alloc_variablesT g e mm l e' mm' T).
Proof.
  intros. induction A; simpl.
  { split; [ trivial | intros; subst]. econstructor. }
  { destruct IHA; split.
    { eexists; split; [ eassumption | trivial]. }
    { intros. destruct E as [mm'' [AA EE]].
      specialize (H1 _ _ EE). econstructor; eassumption. } }
Qed.

Section EXPR_T.
(** Extends Clight.eval_expr etc with event traces. *)

Variable g: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_exprT: expr -> val -> list mem_event-> Prop :=
  | evalT_Econst_int:   forall i ty,
      eval_exprT (Econst_int i ty) (Vint i) nil
  | evalT_Econst_float:   forall f ty,
      eval_exprT (Econst_float f ty) (Vfloat f) nil
  | evalT_Econst_single:   forall f ty,
      eval_exprT (Econst_single f ty) (Vsingle f) nil
  | evalT_Econst_long:   forall i ty,
      eval_exprT (Econst_long i ty) (Vlong i) nil
  | evalT_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_exprT (Etempvar id ty) v nil
  | evalT_Eaddrof: forall a ty loc ofs T,
      eval_lvalueT a loc ofs T ->
      eval_exprT (Eaddrof a ty) (Vptr loc ofs) T
  | evalT_Eunop:  forall op a ty v1 v T,
      eval_exprT a v1 T ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      (*unops at most check weak_valid_ptr, so don't create a trace event*)
      eval_exprT (Eunop op a ty) v T
  | evalT_Ebinop: forall op a1 a2 ty v1 v2 v T1 T2,
      eval_exprT a1 v1 T1 ->
      eval_exprT a2 v2 T2 ->
      sem_binary_operation g op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      (*binops at most check weak_valid_ptr or cast, so don't create a trace event*)
      eval_exprT (Ebinop op a1 a2 ty) v (T1++T2)
  | evalT_Ecast:   forall a ty v1 v T,
      eval_exprT a v1 T ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_exprT (Ecast a ty) v T
  | evalT_Esizeof: forall ty1 ty,
      eval_exprT (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (@sizeof g ty1))) nil
  | evalT_Ealignof: forall ty1 ty,
      eval_exprT (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (@alignof g ty1))) nil
  | evalT_Elvalue: forall a loc ofs v T1 T2 T,
      eval_lvalueT a loc ofs T1 ->
      deref_locT (typeof a) m loc ofs v T2 -> T=(T1 ++ T2) ->
      eval_exprT a v T

with eval_lvalueT: expr -> block -> ptrofs -> list mem_event-> Prop :=
  | evalT_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalueT (Evar id ty) l Ptrofs.zero nil
  | evalT_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol g id = Some l ->
      eval_lvalueT (Evar id ty) l Ptrofs.zero nil
  | evalT_Ederef: forall a ty l ofs T,
      eval_exprT a (Vptr l ofs) T ->
      eval_lvalueT (Ederef a ty) l ofs T
 | evalT_Efield_struct:   forall a i ty l ofs id co att delta T,
      eval_exprT a (Vptr l ofs) T ->
      typeof a = Tstruct id att ->
      g.(genv_cenv)!id = Some co ->
      field_offset g i (co_members co) = Errors.OK delta ->
      eval_lvalueT (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) T
 | evalT_Efield_union:   forall a i ty l ofs id co att T,
      eval_exprT a (Vptr l ofs) T ->
      typeof a = Tunion id att ->
      g.(genv_cenv)!id = Some co ->
      eval_lvalueT (Efield a i ty) l ofs T.

Scheme eval_exprT_ind2 := Minimality for eval_exprT Sort Prop
  with eval_lvalueT_ind2 := Minimality for eval_lvalueT Sort Prop.
Combined Scheme eval_exprT_lvalue_ind from eval_exprT_ind2, eval_lvalueT_ind2.

Inductive eval_exprTlist: list expr -> typelist -> list val -> list mem_event-> Prop :=
  | eval_ETnil:
      eval_exprTlist nil Tnil nil nil
  | eval_ETcons:   forall a bl ty tyl v1 v2 vl T1 T2,
      eval_exprT a v1 T1 ->
      sem_cast v1 (typeof a) ty m = Some v2 ->
      eval_exprTlist bl tyl vl T2 ->
      eval_exprTlist (a :: bl) (Tcons ty tyl) (v2 :: vl) (T1++T2).

Lemma eval_exprT_ax1: forall a v T, eval_exprT a v T -> eval_expr g e le m a v
with eval_lvalueT_ax1: forall a b z T, eval_lvalueT a b z T -> eval_lvalue g e le m a b z.           
Proof.
  + induction 1; econstructor; eauto. eapply deref_locT_ax1; eauto.
  + induction 1; try solve [econstructor; eauto].
Qed.

Lemma eval_exprT_ax2: forall a v, eval_expr g e le m a v -> exists T, eval_exprT a v T
with eval_lvalueT_ax2: forall a b z, eval_lvalue g e le m a b z -> exists T, eval_lvalueT a b z T.
Proof.
  + induction 1; try solve [eexists; econstructor; eauto].
  - apply eval_lvalueT_ax2 in H; destruct H. eexists; eapply evalT_Eaddrof; eauto.
  - destruct IHeval_expr. eexists; eapply evalT_Eunop; eauto.
  - destruct IHeval_expr1. destruct IHeval_expr2. eexists; eapply evalT_Ebinop; eauto.
  - destruct IHeval_expr. eexists; eapply evalT_Ecast; eauto.
  - apply eval_lvalueT_ax2 in H; destruct H.
    apply deref_locT_ax2 in H0. destruct H0. eexists; eapply evalT_Elvalue; eauto.
  + induction 1; try solve [eexists; econstructor; eauto].
  - apply eval_exprT_ax2 in H; destruct H as [T H]. eexists; eapply evalT_Ederef; eauto.
  - apply eval_exprT_ax2 in H; destruct H as [T H]. eexists; eapply evalT_Efield_struct; eauto.
  - apply eval_exprT_ax2 in H; destruct H as [T H]. eexists; eapply evalT_Efield_union; eauto.
Qed.

  Lemma eval_exprT_lvalueT_fun:
    (forall a v1 T1 v2 T2, eval_exprT a v1 T1 -> eval_exprT a v2 T2 -> (v1,T1)=(v2,T2)) /\
    (forall a b1 b2 i1 i2 T1 T2, eval_lvalueT a b1 i1 T1 -> eval_lvalueT a b2 i2 T2 ->
                               (b1,i1,T1)=(b2,i2,T2)).
Proof.
 destruct (eval_exprT_lvalue_ind
   (fun a v T =>  forall v' T', eval_exprT a v' T' -> (v,T)=(v',T'))
   (fun a b i T => forall b' i' T', eval_lvalueT a b' i' T' -> (b,i,T)=(b',i',T')));
   simpl; intros.
 
 { inv H. trivial. inv H0. }
 { inv H. trivial. inv H0. }
 { inv H. trivial. inv H0. }
 { inv H. trivial. inv H0. }
 { inv H. inv H0. congruence. inv H. }
 { inv H1. { apply H0 in H6; congruence. }
           { inv H2. } }
 { inv H2. { apply H0 in H8; congruence. } 
           { inv H3. } }
 { inv H4. { apply H0 in H11; inv H11. apply H2 in H12; congruence. }
           { inv H5. } }
 { inv H2. { apply H0 in H5; congruence. } 
           { inv H3.  } }
 { inv H. trivial. inv H0. }
 { inv H. trivial. inv H0. }
 { inv H. { inv H3. apply H0 in H; inv H. exploit deref_locT_fun. apply H1. apply H2. intros X; inv X; trivial. }
          { inv H3. apply H0 in H; inv H. exploit deref_locT_fun. apply H1. apply H2. intros X; inv X; trivial. }
          { inv H3. apply H0 in H; inv H. exploit deref_locT_fun. apply H1. apply H2. intros X; inv X; trivial. }
          { inv H3. apply H0 in H; inv H. exploit deref_locT_fun. apply H1. apply H2. intros X; inv X; trivial. }
          { inv H3. apply H0 in H; inv H. exploit deref_locT_fun. apply H1. apply H2. intros X; inv X; trivial. } }
 { inv H0; congruence. }
 { inv H1; congruence. }
 { inv H1. apply H0 in H7; congruence. }
 { inv H4. { apply H0 in H8; congruence. }
           { congruence. } }
 { inv H3. { congruence. }
           { apply H0 in H7; congruence. } }

 split; intros. apply (H _ _ _ H1 _ _ H2). apply (H0 _ _ _ _ H1 _ _ _ H2).
Qed.

Lemma eval_exprT_fun a v1 T1 v2 T2: eval_exprT a v1 T1 -> eval_exprT a v2 T2 -> (v1,T1)=(v2,T2).
Proof. apply eval_exprT_lvalueT_fun. Qed.

Lemma eval_lvalueT_fun a b1 b2 i1 i2 T1 T2: eval_lvalueT a b1 i1 T1 -> eval_lvalueT a b2 i2 T2 ->
                               (b1,i1,T1)=(b2,i2,T2).
Proof. apply eval_exprT_lvalueT_fun. Qed.

Lemma eval_exprTlist_ax1: forall es ts vs T (E:eval_exprTlist es ts vs T),
      eval_exprlist g e le m es ts vs.
Proof.
  intros; induction E; simpl; intros. econstructor.
  apply eval_exprT_ax1 in H. econstructor; eauto.
Qed.

Lemma eval_exprTlist_ax2: forall es ts vs (E:eval_exprlist g e le m es ts vs),
      exists T, eval_exprTlist es ts vs T.
Proof.
  intros; induction E; simpl; intros. eexists; econstructor.
  apply eval_exprT_ax2 in H. destruct H as [T1 H]. destruct IHE as [T2 K].
  eexists. econstructor; eauto.
Qed.

Lemma eval_exprTlist_fun: forall es ts vs1 T1 (E1:eval_exprTlist es ts vs1 T1)
                          vs2 T2 (E2:eval_exprTlist es ts vs2 T2), (vs1,T1)=(vs2,T2).
Proof.
  intros es ts vs1 T1 E; induction E; simpl; intros; inv E2; trivial.
  exploit eval_exprT_fun. apply H. apply H5. intros X; inv X. rewrite H8 in H0; inv H0.
  apply IHE in H9; congruence. 
Qed.

End EXPR_T.


Lemma eval_exprT_elim g e le:
  forall m a v T (E:eval_exprT g e le m a v T), ev_elim m T m
  with eval_lvalueT_elim g e le:
         forall m a b z T (E:eval_lvalueT g e le m a b z T),
           ev_elim m T m.
Proof.
  + clear eval_exprT_elim; induction 1; try solve [econstructor]; eauto.
    { eapply ev_elim_app; eassumption. }
    { subst. specialize (eval_lvalueT_elim _ _ _ _ _ _ _ _ H). 
      exploit deref_locT_elim; eauto. intros [E2 EE2].
      eapply ev_elim_app; eauto. }
  + clear eval_lvalueT_elim; induction 1; try solve [econstructor]; eauto.
Qed.

Lemma eval_exprTlist_elim g e le : forall m es ts vs T
                                  (E:eval_exprTlist g e le m es ts vs T),
    ev_elim m T m.
Proof.
  induction 1; try solve [constructor].
  exploit eval_exprT_elim. apply H. intros E1. 
    eapply ev_elim_app; eassumption.
Qed.

Inductive assign_locT (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs)
  : val -> mem -> list mem_event -> Prop :=
    assign_locT_value : forall (v : val) (chunk : memory_chunk) (m' : mem),
                       access_mode ty = By_value chunk ->
                       Mem.storev chunk m (Vptr b ofs) v = Some m' ->
                       assign_locT ce ty m b ofs v m' (Write b (Ptrofs.unsigned ofs) (encode_val chunk v) ::nil)
  | assign_locT_copy : forall (b' : block) (ofs' : ptrofs) (bytes : list memval) (m' : mem),
                      access_mode ty = By_copy ->
                      (sizeof ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
                      (sizeof ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
                      b' <> b \/
                      Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
                      Ptrofs.unsigned ofs' + sizeof ty <= Ptrofs.unsigned ofs \/
                      Ptrofs.unsigned ofs + sizeof ty <= Ptrofs.unsigned ofs' ->
                      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ty) = Some bytes ->
                      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
                      assign_locT ce ty m b ofs (Vptr b' ofs') m'
                                  (Read b' (Ptrofs.unsigned ofs') (sizeof ty) bytes ::
                                   Write b (Ptrofs.unsigned ofs) bytes :: nil).

Lemma assign_locT_ax1 ce ty m b ofs v m' T (A:assign_locT ce ty m b ofs v m' T):
    assign_loc ce ty m b ofs v m'. 
Proof.
  destruct A; [eapply assign_loc_value; eauto | eapply assign_loc_copy; eauto].
Qed.

Lemma assign_locT_ax2 ce ty m b ofs v m' (A:assign_loc ce ty m b ofs v m'):
    exists T, assign_locT ce ty m b ofs v m' T. 
Proof.
  destruct A; eexists; [eapply assign_locT_value; eauto | eapply assign_locT_copy; eauto].
Qed.

Lemma assign_locT_fun ce ty m b ofs v m1 T1
      (A1:assign_locT ce ty m b ofs v m1 T1) m2 T2 (A2:assign_locT ce ty m b ofs v m2 T2):
      (m1,T1)=(m2,T2).
Proof. inv A1; inv A2; congruence. Qed.

Lemma assign_locT_elim ce ty m b ofs v m1 T (A:assign_locT ce ty m b ofs v m1 T):
  ev_elim m T m1 /\
  forall mm mm1 (E: ev_elim mm T mm1),
    assign_locT ce ty mm b ofs v mm1 T.
Proof.
  inv A; simpl.
  { exploit Mem.store_valid_access_3; eauto. intros [_ A].
    apply Mem.store_storebytes in H0.
    split. { exists m1; split; trivial. }
    intros. destruct E as [? [? ?]]; subst. econstructor; eauto.
    apply Mem.storebytes_store; eassumption. }
  { split. { split; [trivial | exists m1; split; trivial]. }
    intros. destruct E as [LD [? [? ?]]]; subst.
    constructor; eassumption. }
Qed. 

Section CLN_SEM.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := corestate.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
  (* We might want to define this properly or
     factor the machines so we don't need events here. *)
  
(** Transition relation *)
Inductive cl_evstep (ge: Clight.genv): forall (q: corestate) (m: mem) (T:list mem_event) (q': corestate) (m': mem), Prop :=

  | evstep_assign: forall ve te k m a1 a2 loc ofs v2 v m' T1 T2 T3,
     type_is_volatile (typeof a1) = false ->
      eval_lvalueT ge ve te m a1 loc ofs T1 ->
      eval_exprT ge ve te m a2 v2 T2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_locT ge (typeof a1) m loc ofs v m' T3 ->
      cl_evstep ge (State ve te (Kseq (Sassign a1 a2):: k)) m (T1++T2++T3) (State ve te k) m'

  | evstep_set:   forall ve te k m id a v T,
      eval_exprT ge ve te m a v T ->
      cl_evstep ge (State ve te (Kseq (Sset id a) :: k)) m T (State ve (PTree.set id v te) k) m

  | evstep_call_internal:   forall ve te k m optid a al tyargs tyres cc vf vargs f m1 ve' le' T1 T2 T3,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cc ->
      eval_exprT ge ve te m a vf T1 ->
      eval_exprTlist ge ve te m al tyargs vargs T2 ->
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction tyargs tyres cc ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_temps)) ->
      forall (NRV: list_norepet (var_names f.(fn_vars))),
      alloc_variablesT ge empty_env m (f.(fn_vars)) ve' m1 T3 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some
le' ->
      cl_evstep ge (State ve te (Kseq (Scall optid a al) :: k)) m (T1++T2++T3)
                   (State ve' le' (Kseq f.(fn_body) :: Kseq (Sreturn None) :: Kcall optid f ve te :: k)) m1

  | evstep_call_external:   forall ve te k m optid a al tyargs tyres cc vf vargs ef T1 T2,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cc ->
      eval_exprT ge ve te m a vf T1 ->
      eval_exprTlist ge ve te m al tyargs vargs T2 ->
      Genv.find_funct ge vf = Some (External ef tyargs tyres cc) ->
      cl_evstep ge (State ve te (Kseq (Scall optid a al) :: k)) m (T1++T2) (ExtCall ef vargs optid ve te k) m

  | evstep_seq: forall ve te k m s1 s2 st' m' T,
          cl_evstep ge (State ve te (Kseq s1 :: Kseq s2 :: k)) m T st' m' ->
          cl_evstep ge (State ve te (Kseq (Ssequence s1 s2) :: k)) m T st' m'

  | evstep_skip: forall ve te k m st' m' T,
          cl_evstep ge (State ve te k) m T st' m' ->
          cl_evstep ge (State ve te (Kseq Sskip :: k)) m T st' m'

  | evstep_continue: forall ve te k m st' m' T,
           cl_evstep ge (State ve te (continue_cont k)) m T st' m' ->
           cl_evstep ge (State ve te (Kseq Scontinue :: k)) m T st' m'

  | evstep_break: forall ve te k m st' m' T,
                   cl_evstep ge (State ve te (break_cont k)) m T st' m' ->
                   cl_evstep ge (State ve te (Kseq Sbreak :: k)) m T st' m'

  | evstep_ifthenelse:  forall ve te k m a s1 s2 v1 b T,
      eval_exprT ge ve te m a v1 T ->
      Cop.bool_val v1 (typeof a) m = Some b ->
      cl_evstep ge (State ve te (Kseq (Sifthenelse a s1 s2) :: k)) m T (State ve te  (Kseq (if b then s1 else s2) :: k)) m

  | evstep_for: forall ve te k m s1 s2,
      cl_evstep ge (State ve te (Kseq (Sloop s1 s2) :: k)) m nil
              (State ve te (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: k)) m

  | evstep_loop2: forall ve te k m a3 s,
      cl_evstep ge (State ve te (Kloop2 s a3 :: k)) m nil
             (State ve te (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: k)) m

  | evstep_return: forall f ve te optexp optid k m v' m' ve' te' te'' k' T,
      call_cont k = Kcall optid f ve' te' :: k' ->
      Mem.free_list m (Clight.blocks_of_env ge ve) = Some m' ->
      match optexp with None => v' = Vundef /\ T=nil
                      | Some a => exists v, eval_exprT ge ve te m a v T
                                     /\ Cop.sem_cast v (typeof a) f.(fn_return) m = Some v'
                            end ->
      match optid with None => True /\ te''=te'
                     | Some id => True /\ te'' = PTree.set id v' te'
      end ->
      cl_evstep ge (State ve te (Kseq (Sreturn optexp) :: k)) m
                   (T ++ (Free (Clight.blocks_of_env ge ve)::nil))
                   (State ve' te'' k') m'

  | evstep_switch: forall ve te k m a sl v n T,
      eval_exprT ge ve te m a v T ->
      Cop.sem_switch_arg v (typeof a) = Some n ->
      cl_evstep ge (State ve te (Kseq (Sswitch a sl) :: k)) m T
              (State ve te (Kseq (seq_of_labeled_statement (select_switch n sl)) :: Kswitch :: k)) m

  | evstep_label: forall ve te k m lbl s st' m' T,
       cl_evstep ge (State ve te (Kseq s :: k)) m T st' m' ->
       cl_evstep ge (State ve te (Kseq (Slabel lbl s) :: k)) m T st' m'

  | evstep_goto: forall f ve te k m lbl k'
                     (* make sure to take a step here, so that every loop ticks the clock *)
      (CUR: current_function k = Some f),
      find_label lbl f.(fn_body) (Kseq (Sreturn None) :: (call_cont k)) = Some k' ->
      cl_evstep ge (State ve te (Kseq (Sgoto lbl) :: k)) m nil (State ve te k') m.

  Lemma CLN_evstep_ax1 ge : forall c m T c' m' (H: cl_evstep ge c m T c' m' ),
    corestep (CLN_memsem ge) c m c' m'.
  Proof.
    induction 1; try solve [econstructor; eassumption].
    { apply eval_lvalueT_ax1 in H0. apply eval_exprT_ax1 in H1.
      apply assign_locT_ax1 in H3. econstructor; eauto. }
    { apply eval_exprT_ax1 in H. econstructor; eauto. }
    { apply eval_exprT_ax1 in H0.
      apply eval_exprTlist_ax1 in H1.
      apply alloc_variablesT_ax1 in H5. econstructor; eauto. }
    { apply eval_exprT_ax1 in H0.
      apply eval_exprTlist_ax1 in H1. econstructor; eauto. }
    { apply eval_exprT_ax1 in H. econstructor; eauto. }
    { destruct optexp.
      + destruct H1 as [v [E C]]. apply eval_exprT_ax1 in E.
        econstructor; eauto.
      + destruct H1; subst. econstructor; eauto. }
    { apply eval_exprT_ax1 in H. econstructor; eauto. }
  Qed.   
  
  Lemma CLN_evstep_ax2 ge : forall c m c' m' (H:corestep (CLN_memsem ge) c m c' m'),
      exists T : list mem_event, cl_evstep ge c m T c' m'.
  Proof.
    induction 1; try solve [ destruct IHcl_step as [T HT]; eexists; econstructor; eauto]; try solve [eexists; econstructor; eauto]. 
    { apply eval_lvalueT_ax2 in H0. destruct H0 as [T1 A1].
      apply eval_exprT_ax2 in H1. destruct H1 as [T2 A2].
      apply assign_locT_ax2 in H3. destruct H3 as [T3 A3].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T H].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H0. destruct H0 as [T1 K1].
      apply eval_exprTlist_ax2 in H1. destruct H1 as [T2 K2].
      apply alloc_variablesT_ax2 in H5. destruct H5 as [T3 K3].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H0. destruct H0 as [T1 K1].
      apply eval_exprTlist_ax2 in H1. destruct H1 as [T2 K2].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T KT].
      eexists; econstructor; eauto. }
    { destruct optexp.
      + destruct H1 as [v [E C]].
        apply eval_exprT_ax2 in E. destruct E as [T HT].
        eexists. econstructor; eauto.
      + subst. eexists. econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T K].
      eexists; econstructor; eauto. }
Qed.

  Lemma CLN_evstep_fun ge : forall c m T' c' m' T'' c'' m''
                                   (K: cl_evstep ge c m T' c' m') (K': cl_evstep ge c m T'' c'' m''), T' = T''.
  Proof. intros. generalize dependent m''. generalize dependent c''. generalize dependent T''.
         induction K; simpl; intros; try solve [ inv K'; eauto ].
  { inv K'. exploit eval_exprT_fun. apply H15. apply H1. intros X; inv X.
    exploit eval_lvalueT_fun. apply H14. apply H0. intros X; inv X.
    rewrite H16 in H2; inv H2.
    exploit assign_locT_fun. apply H17. apply H3. intros X; inv X; trivial. }
  { inv K'. exploit eval_exprT_fun. apply H9. apply H. intros X; inv X. trivial. }
  { inv K'.
    + rewrite H13 in H; inv H.
      exploit eval_exprT_fun. apply H14. apply H0. intros X; inv X.
      exploit eval_exprTlist_fun. apply H15. apply H1. intros X; inv X.
      rewrite H20 in H2; inv H2.
      rewrite H24 in H6; inv H6.
      exploit alloc_variablesT_fun. apply H23. apply H5.
      intros X; inv X; trivial.
    + rewrite H17 in H; inv H.
      exploit eval_exprT_fun. apply H18. apply H0. intros X; inv X.
      congruence. }
  { inv K'.
    + rewrite H9 in H; inv H.
      exploit eval_exprT_fun. apply H10. apply H0. intros X; inv X.
      congruence.
    + rewrite H13 in H; inv H.
      exploit eval_exprT_fun. apply H14. apply H0. intros X; inv X.
      exploit eval_exprTlist_fun. apply H15. apply H1. intros X; inv X.
      congruence. }
  { inv K'.
    exploit eval_exprT_fun. apply H11. apply H. intros X; inv X. trivial. }
  { inv K'. destruct optexp.
    + destruct H1 as [u [E C]]. destruct H13 as [u' [E' C']].
      exploit eval_exprT_fun. apply E'. apply E. intros X; inv X. trivial.
    + destruct H1; destruct H13; subst. trivial. }
  { inv K'.
    exploit eval_exprT_fun. apply H10. apply H. intros X; inv X. trivial. }
  Qed.

  Lemma CLN_evstep_elim ge : forall c m T c' m' (K: cl_evstep ge c m T c' m'),
        ev_elim m T m'.
  Proof.
    induction 1; try solve [constructor];
      try solve [ apply eval_exprT_elim in H; trivial]; trivial.
    { eapply assign_locT_elim in H3. destruct H3 as [EV3 _ ].
      eapply eval_lvalueT_elim in H0.
      eapply eval_exprT_elim in H1.
      eapply ev_elim_app; eauto. eapply ev_elim_app; eauto. }
    { apply eval_exprT_elim in H0.
      apply eval_exprTlist_elim in H1.
      apply alloc_variablesT_elim in H5; destruct H5 as [? _].
      eapply ev_elim_app; eauto. eapply ev_elim_app; eauto. }
    { apply eval_exprT_elim in H0.
      apply eval_exprTlist_elim in H1.
      eapply ev_elim_app; eauto. }
    { destruct optexp.
      + destruct H1 as [? [? ?]]. apply eval_exprT_elim in H1.
        eapply ev_elim_app; [ eassumption | simpl].
        exists m'; split; trivial.
      + destruct H1; subst; simpl. exists m'; split; trivial. }
  Qed.
  
  (** *Event semantics for Clight_new*)
   (* This should be a version of CLN_memsem annotated with memory events.*)
  
  Program Definition CLN_evsem ge : @EvSem C := {| msem := CLN_memsem ge; ev_step := cl_evstep ge |}.
  Next Obligation. apply CLN_evstep_ax1. Qed.
  Next Obligation. apply CLN_evstep_ax2. Qed.
  Next Obligation. apply CLN_evstep_fun. Qed.
  Next Obligation. apply CLN_evstep_elim. Qed.  

  Lemma CLN_msem : forall ge, msem (CLN_evsem ge) = CLN_memsem ge.
  Proof. auto. Qed.
End CLN_SEM.

  Lemma CLN_step_decay: forall g c m tr c' m',
      event_semantics.ev_step (CLN_evsem g) c m tr c' m' ->
      decay m m'.
Proof.
intros.
pose proof (msem_decay (CLN_memsem g) c m c' m').
apply H0. clear H0.
simpl in *.
apply CLN_evstep_ax1 in H.
auto.
Qed.

  Lemma at_external_SEM_eq:
     forall ge c m, semantics.at_external (CLN_evsem ge) c m =
      match c with
      | State _ _ _ => None
      | ExtCall ef args _ _ _ _ => Some (ef, args)
      end.
  Proof. auto. Qed.

  Instance Clight_newSem ge : Semantics :=
    { semG := G; semC := C; semSem := CLN_evsem ge; the_ge := ge }.

  Inductive builtin_event: external_function -> mem -> list val -> list mem_event -> Prop :=
  BE_malloc: forall m n m'' b m'
         (ALLOC: Mem.alloc m (-size_chunk Mptr) (Ptrofs.unsigned n) = (m'', b))
         (ALGN : (align_chunk Mptr | (-size_chunk Mptr)))
         (ST: Mem.storebytes m'' b (-size_chunk Mptr) (encode_val Mptr (Vptrofs n)) = Some m'),
         builtin_event EF_malloc m [Vptrofs n]
               [Alloc b (-size_chunk Mptr) (Ptrofs.unsigned n);
                Write b (-size_chunk Mptr) (encode_val Mptr (Vptrofs n))]
| BE_free: forall m b lo bytes sz m'
        (POS: Ptrofs.unsigned sz > 0)
        (LB : Mem.loadbytes m b (Ptrofs.unsigned lo - size_chunk Mptr) (size_chunk Mptr) = Some bytes)
        (FR: Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m')
        (ALGN : (align_chunk Mptr | Ptrofs.unsigned lo - size_chunk Mptr))
        (SZ : Vptrofs sz = decode_val Mptr bytes),
        builtin_event EF_free m [Vptr b lo]
              [Read b (Ptrofs.unsigned lo - size_chunk Mptr) (size_chunk Mptr) bytes;
               Free [(b,Ptrofs.unsigned lo - size_chunk Mptr, Ptrofs.unsigned lo + Ptrofs.unsigned sz)]]
| BE_memcpy: forall m al bsrc bdst sz bytes osrc odst m'
        (AL: al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
        (POS : sz >= 0)
        (DIV : (al | sz))
        (OSRC : sz > 0 -> (al | Ptrofs.unsigned osrc))
        (ODST: sz > 0 -> (al | Ptrofs.unsigned odst))
        (RNG: bsrc <> bdst \/
                Ptrofs.unsigned osrc = Ptrofs.unsigned odst \/
                Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc)
        (LB: Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m'),
        builtin_event (EF_memcpy sz al) m [Vptr bdst odst; Vptr bsrc osrc]
              [Read bsrc (Ptrofs.unsigned osrc) sz bytes;
               Write bdst (Ptrofs.unsigned odst) bytes]
(*| BE_EFexternal: forall name sg m vargs,
(*        I64Helpers.is_I64_helperS name sg ->*)
         builtin_event (EF_external name sg) m vargs []
| BE_EFbuiltin: forall name sg m vargs, (*is_I64_builtinS name sg ->*)
         builtin_event (EF_builtin name sg) m vargs []*)
| BE_other: forall ef m vargs,
  match ef with EF_malloc | EF_free | EF_memcpy _ _ => False | _ => True end ->
  builtin_event ef m vargs [].

Lemma Vptrofs_inj : forall o1 o2, Vptrofs o1 = Vptrofs o2 ->
  Ptrofs.unsigned o1 = Ptrofs.unsigned o2.
Proof.
  unfold Vptrofs; intros.
  pose proof (Ptrofs.unsigned_range o1); pose proof (Ptrofs.unsigned_range o2).
  destruct Archi.ptr64 eqn: H64.
  - assert (Int64.unsigned (Ptrofs.to_int64 o1) = Int64.unsigned (Ptrofs.to_int64 o2)) by congruence.
    unfold Ptrofs.to_int64 in *.
    rewrite Ptrofs.modulus_eq64 in * by auto.
    rewrite !Int64.unsigned_repr in * by (unfold Int64.max_unsigned; omega); auto.
  - assert (Int.unsigned (Ptrofs.to_int o1) = Int.unsigned (Ptrofs.to_int o2)) by congruence.
    unfold Ptrofs.to_int in *.
    rewrite Ptrofs.modulus_eq32 in * by auto.
    rewrite !Int.unsigned_repr in * by (unfold Int.max_unsigned; omega); auto.
Qed.

Lemma builtin_event_determ ef m vargs T1 (BE1: builtin_event ef m vargs T1) T2 (BE2: builtin_event ef m vargs T2): T1=T2.
inversion BE1; inv BE2; try discriminate; try contradiction; simpl in *; trivial.
+ assert (Vptrofs n0 = Vptrofs n) as H by congruence.
  rewrite H; rewrite (Vptrofs_inj _ _ H) in *.
  rewrite ALLOC0 in ALLOC; inv ALLOC; trivial.
+ inv H5.
  rewrite LB0 in LB; inv LB. rewrite <- SZ in SZ0. rewrite (Vptrofs_inj _ _ SZ0); trivial.
+ inv H3; inv H5.
  rewrite LB0 in LB; inv LB; trivial.
Qed.

Section CLC_SEM.
  Variable g: Clight.genv.
    
  Section CLC_step.
    Variable function_entryT: function -> list val -> mem -> env -> temp_env -> mem -> list mem_event -> Prop.

    Inductive clc_evstep: state -> mem -> list mem_event -> state -> mem -> Prop :=
  | clc_evstep_assign: forall f a1 a2 k e le m loc ofs v2 v m' T1 T2 T3 mx,
      eval_lvalueT g e le m a1 loc ofs T1 ->
      eval_exprT g e le m a2 v2 T2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_locT g (typeof a1) m loc ofs v m' T3 ->
      clc_evstep (Clight.State f (Sassign a1 a2) k e le mx) m (T1++T2++T3)
                 (Clight.State f Sskip k e le m') m'

  | clc_evstep_set: forall f id a k e le m v T mx,
      eval_exprT g e le m a v T ->
      clc_evstep (Clight.State f (Sset id a) k e le mx) m
        T (Clight.State f Sskip k e (PTree.set id v le) m) m

  | clc_evstep_call: forall f optid a al k e le m tyargs tyres cconv vf vargs fd T1 T2 mx,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_exprT g e le m a vf T1 ->
      eval_exprTlist g e le m al tyargs vargs T2 ->
      Genv.find_funct g vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      clc_evstep (Clight.State f (Scall optid a al) k e le mx) m 
        (T1++T2) (Clight.Callstate fd vargs (Clight.Kcall optid f e le k) m) m

  | clc_evstep_builtin: forall f optid ef tyargs al k e le m vargs t vres m' T1 T2 mx,
      eval_exprTlist g e le m al tyargs vargs T1 ->
      builtin_event ef m vargs T2 ->
      Events.external_call ef g vargs m t vres m' ->
      clc_evstep (Clight.State f (Sbuiltin optid ef tyargs al) k e le mx) m
                 (T1++T2) (Clight.State f Sskip k e (set_opttemp optid vres le) m') m'
    
  | clc_evstep_seq:  forall f s1 s2 k e le m mx,
      clc_evstep (Clight.State f (Ssequence s1 s2) k e le mx) m
        nil (Clight.State f s1 (Clight.Kseq s2 k) e le m) m
  | clc_evstep_skip_seq: forall f s k e le m mx,
      (*~ is_call_cont k ->*)
      clc_evstep (Clight.State f Sskip (Clight.Kseq s k) e le mx) m
        nil (Clight.State f s k e le m) m
  | clc_evstep_continue_seq: forall f s k e le m mx,
      clc_evstep (Clight.State f Scontinue (Clight.Kseq s k) e le mx) m
        nil (Clight.State f Scontinue k e le m) m
  | clc_evstep_break_seq: forall f s k e le m mx,
      clc_evstep (Clight.State f Sbreak (Clight.Kseq s k) e le mx) m
        nil (Clight.State f Sbreak k e le m) m

  | clc_evstep_ifthenelse:  forall f a s1 s2 k e le m v1 b T mx,
      eval_exprT g e le m a v1 T ->
      bool_val v1 (typeof a) m = Some b ->
      clc_evstep (Clight.State f (Sifthenelse a s1 s2) k e le mx) m
        T (Clight.State f (if b then s1 else s2) k e le m) m

  | clc_evstep_loop: forall f s1 s2 k e le m mx,
      clc_evstep (Clight.State f (Sloop s1 s2) k e le mx) m
        nil (Clight.State f s1 (Clight.Kloop1 s1 s2 k) e le m) m
  | clc_evstep_skip_or_continue_loop1:  forall f s1 s2 k e le m x mx,
      x = Sskip \/ x = Scontinue ->
      clc_evstep (Clight.State f x (Clight.Kloop1 s1 s2 k) e le mx) m
        nil (Clight.State f s2 (Clight.Kloop2 s1 s2 k) e le m) m
  | clc_evstep_break_loop1:  forall f s1 s2 k e le m mx,
      clc_evstep (Clight.State f Sbreak (Clight.Kloop1 s1 s2 k) e le mx) m
        nil (Clight.State f Sskip k e le m) m
  | clc_evstep_skip_loop2: forall f s1 s2 k e le m mx,
      clc_evstep (Clight.State f Sskip (Clight.Kloop2 s1 s2 k) e le mx) m
        nil (Clight.State f (Sloop s1 s2) k e le m) m
  | clc_evstep_break_loop2: forall f s1 s2 k e le m mx,
      clc_evstep (Clight.State f Sbreak (Clight.Kloop2 s1 s2 k) e le mx) m
                 nil (Clight.State f Sskip k e le m) m
                 
  | clc_evstep_return_0: forall f k e le m m' mx,
      Mem.free_list m (blocks_of_env g e) = Some m' ->
      clc_evstep (Clight.State f (Sreturn None) k e le mx) m
        (Free (blocks_of_env g e)::nil) (Returnstate Vundef (Clight.call_cont k) m') m'
  | clc_evstep_return_1: forall f a k e le m v v' m' T mx,
      eval_exprT g e le m a v T ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env g e) = Some m' ->
      clc_evstep (Clight.State f (Sreturn (Some a)) k e le mx) m
        (T++Free (blocks_of_env g e)::nil) (Returnstate v' (Clight.call_cont k) m') m'
  | clc_evstep_skip_call: forall f k e le m m' mx,
      is_call_cont k ->
      Mem.free_list m (blocks_of_env g e) = Some m' ->
      clc_evstep (Clight.State f Sskip k e le mx) m
        (Free (blocks_of_env g e)::nil) (Returnstate Vundef k m') m'

  | clc_evstep_switch: forall f a sl k e le m v n T mx,
      eval_exprT g e le m a v T ->
      sem_switch_arg v (typeof a) = Some n ->
      clc_evstep (Clight.State f (Sswitch a sl) k e le mx) m
        T (Clight.State f (seq_of_labeled_statement (select_switch n sl)) (Clight.Kswitch k) e le m) m
  | clc_evstep_skip_break_switch: forall f x k e le m mx,
      x = Sskip \/ x = Sbreak ->
      clc_evstep (Clight.State f x (Clight.Kswitch k) e le mx) m
        nil (Clight.State f Sskip k e le m) m
  | clc_evstep_continue_switch: forall f k e le m mx,
      clc_evstep (Clight.State f Scontinue (Clight.Kswitch k) e le mx) m
        nil (Clight.State f Scontinue k e le m) m

  | clc_evstep_label: forall f lbl s k e le m mx,
      clc_evstep (Clight.State f (Slabel lbl s) k e le mx) m
        nil (Clight.State f s k e le m) m

  | clc_evstep_goto: forall f lbl k e le m s' k' mx,
      Clight.find_label lbl f.(fn_body) (Clight.call_cont k) = Some (s', k') ->
      clc_evstep (Clight.State f (Sgoto lbl) k e le mx) m
        nil (Clight.State f s' k' e le m) m

  | clc_evstep_internal_function: forall f vargs k m e le m1 T mx,
      function_entryT f vargs m e le m1 T ->
      clc_evstep (Clight.Callstate (Internal f) vargs k mx) m
        T (Clight.State f f.(fn_body) k e le m1) m1
(*
  | clc_evstep_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      clc_evstep (Clight.Callstate (External ef targs tres cconv) vargs k m)
         t (Clight.Returnstate vres k m')*)

  | clc_evstep_returnstate: forall v optid f e le k m mx,
      clc_evstep (Clight.Returnstate v (Clight.Kcall optid f e le k) mx) m
        nil (Clight.State f Sskip k e (set_opttemp optid v le) m) m.

  Lemma clc_ax1 
        (HFe: forall f vargs m e le m1 T,
            function_entryT f vargs m e le m1 T -> function_entry2 g f vargs m e le m1):
    forall c m T c' m', clc_evstep c m T c' m' ->
        Clight.at_external (set_mem c m) = None /\
        m' = get_mem c' /\
        exists t, step g (function_entry2 g) (set_mem c m) t c'.
  Proof.
    induction 1; simpl; split; trivial; split; trivial; intros;
     try solve [ apply eval_exprT_ax1 in H; eexists; econstructor; eauto ];
     try solve [ eexists; econstructor; eauto ].
    { apply eval_lvalueT_ax1 in H. apply eval_exprT_ax1 in H0.
      apply assign_locT_ax1 in H2. eexists; econstructor; eauto. }
    { apply eval_exprT_ax1 in H0. apply eval_exprTlist_ax1 in H1.
      eexists; econstructor; eauto. }
    { apply eval_exprTlist_ax1 in H. 
      eexists; econstructor; eauto. }
  Qed.
  
  Lemma clc_ax2
        (Hfe: forall f vargs m e le m1, function_entry2 g f vargs m e le m1 ->
            exists T, function_entryT f vargs m e le m1 T):
        forall d t c' 
                        (H: step g (function_entry2 g) d t c')
                        c m (HD : d = set_mem c m)
                        (AE : Clight.at_external d = None),
      exists T : list mem_event, clc_evstep c m T c' (get_mem c').
  Proof.
    induction 1; simpl; intros; destruct c; inv HD; simpl in *;
      try solve [eexists; econstructor; eauto]; try solve [congruence].
    { apply eval_lvalueT_ax2 in H; destruct H as [T1 K1].
      apply eval_exprT_ax2 in H0; destruct H0 as [T2 A2].
      apply assign_locT_ax2 in H2; destruct H2 as [T3 A3].
      eexists. econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T H].
      eexists. eapply clc_evstep_set; eauto. }
    { apply eval_exprT_ax2 in H0. destruct H0 as [T1 K1].
      apply eval_exprTlist_ax2 in H1. destruct H1 as [T2 K2].
      eexists; eapply clc_evstep_call; eauto. }
    { apply eval_exprTlist_ax2 in H. destruct H as [T1 K1].
      assert (BE: exists T2, builtin_event ef m0 vargs T2).
      { destruct ef; try solve [ exists nil; econstructor; eauto].
        { (*EF_malloc*) inv H0. exploit Mem.store_valid_access_3; eauto. intros [_ ALGN].
          apply Mem.store_storebytes in H1.
          eexists. eapply BE_malloc; eauto. }
        { (*EF_free*) inv H0. exploit Mem.load_valid_access; eauto. intros [_ ALGN].
          exploit Mem.load_loadbytes; eauto. intros [bytes [LD X]].
          eexists. eapply BE_free; eauto. }
        { (*EF_memcpy*) inv H0.
          eexists. eapply BE_memcpy; eauto. } } 
      destruct BE as [T2 BE].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T HT].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T HT].
      eexists; econstructor; eauto. }
    { apply eval_exprT_ax2 in H. destruct H as [T HT].
      eexists; econstructor; eauto. }
    { apply Hfe in H; destruct H as [T HT].
      eexists. econstructor; eauto. }
  Qed.

  Lemma clc_fun (HFe: forall f vargs m e1 le1 m1 T1 (FE1:function_entryT f vargs m e1 le1 m1 T1)
                             e2 le2 m2 T2 (FE2:function_entryT f vargs m e2 le2 m2 T2), T1=T2):
    forall c m T1 c1 m1 T2 c2 m2 (EX1: clc_evstep c m T1 c1 m1)
           (EX2:clc_evstep c m T2 c2 m2), T1 = T2.
  Proof.
    induction 1; simpl; intros; try solve [inv EX2; split; reflexivity].
    { inv EX2. exploit eval_lvalueT_fun. apply H14. apply H. intros X; inv X.
      exploit eval_exprT_fun. apply H15. apply H0. intros X; inv X.
      rewrite H16 in H1; inv H1.
      exploit assign_locT_fun. apply H17. apply H2. intros X; inv X. trivial.
      destruct H13; subst; congruence.
      destruct H13; subst; congruence. }
    { inv EX2. exploit eval_exprT_fun. apply H11. apply H. intros X; inv X. trivial.
      destruct H10; subst; congruence.
      destruct H10; subst; congruence. } 
    { inv EX2.
      { rewrite H16 in H; inv H.
        exploit eval_exprT_fun. apply H17. apply H0. intros X; inv X.
        exploit eval_exprTlist_fun. apply H18. apply H1. intros X; inv X. trivial. }
      destruct H14; subst; congruence.
      destruct H14; subst; congruence. }
    { inv EX2.
      { exploit eval_exprTlist_fun. apply H15. apply H. intros X; inv X.
        exploit builtin_event_determ. apply H16. apply H0. congruence. }
      destruct H12; congruence. 
      destruct H12; congruence. }
    { inv EX2. trivial. contradiction. }
    { inv EX2. 
      exploit eval_exprT_fun. apply H13. apply H. congruence.
      destruct H11; congruence. destruct H11; congruence. }
    { destruct H; subst; inv EX2; trivial. contradiction. }
    { inv EX2; trivial. contradiction. }
    { inv EX2. destruct H10; congruence. congruence. destruct H10; congruence. }
    { inv EX2. destruct H12; congruence.  
      exploit eval_exprT_fun. apply H12. apply H. congruence.
      destruct H12; congruence. }
    { inv EX2; try solve [ contradiction ]; trivial. }
    { inv EX2. destruct H11; congruence.
      exploit eval_exprT_fun. apply H12. apply H. congruence.
      destruct H11; congruence. }
    { destruct H; subst; inv EX2; try solve [contradiction]; trivial. }
    { inv EX2. eauto. }
  Qed.

  Lemma extcall_ev_elim: forall ef g vargs m t vres m' ev
    (Hext: Events.external_call ef g vargs m t vres m')
    (Hev: builtin_event ef m vargs ev)
    (Hef: match ef with EF_malloc | EF_free | EF_memcpy _ _ => False | _ => True end),
    ev_elim m ev m'.
  Proof.
  Admitted.

  Lemma clc_ev_elim (FE: forall f vargs m e le m1 T (E:function_entryT f vargs m e le m1 T), ev_elim m T m1):
    forall c m T c' m' (E: clc_evstep c m T c' m'), ev_elim m T m'.
  Proof.
    induction 1; try solve [constructor];
      try solve [ apply eval_exprT_elim in H; trivial]; trivial.
    - eapply assign_locT_elim in H2. destruct H2 as [EV3 _ ].
      eapply eval_lvalueT_elim in H.
      eapply eval_exprT_elim in H0.
      eapply ev_elim_app; eauto. eapply ev_elim_app; eauto.
    - apply eval_exprT_elim in H0.
      apply eval_exprTlist_elim in H1.
      eapply ev_elim_app; eauto.
    - apply eval_exprTlist_elim in H. eapply ev_elim_app; eauto. clear H.
      inv H0.
      { exploit extcall_malloc_sem_inv. apply H1. clear H1. intros [m1 [bb [sz [X [Ht [Hres [A STORE]]]]]]]; subst.
        assert (HV: Vptrofs n = Vptrofs sz).
        { clear -X. remember (Vptrofs n). remember  (Vptrofs sz).  clear Heqv Heqv0. inv X; trivial. }
        rewrite (Vptrofs_inj _ _ HV) in *. rewrite HV in *. clear X.
        rewrite A in ALLOC. inv ALLOC. apply Mem.store_storebytes in STORE.
        rewrite ST in STORE. inv STORE.
        econstructor; split. eassumption. econstructor; split. eassumption. reflexivity. }
      {  inv H1. apply Mem.load_loadbytes in H2. destruct H2 as [bytes1 [LD V]]; subst.
         rewrite LD in LB; inv LB. rewrite <- SZ in V. rewrite (Vptrofs_inj _ _ V) in *. clear V SZ.
         rewrite FR in H8; inv H8.
         econstructor. eassumption. econstructor. split. { simpl. rewrite FR. reflexivity. } reflexivity. }
      { inv H1. rewrite H14 in LB; inv LB. rewrite ST in H15; inv H15.
        econstructor. eassumption. econstructor; split. eassumption. reflexivity. }
      eapply extcall_ev_elim; eauto; constructor; auto.
    - do 2 eexists; eauto; constructor.
    - apply eval_exprT_elim in H.
      eapply ev_elim_app; eauto.
      do 2 eexists; eauto; constructor.
    - do 2 eexists; eauto; constructor.
    - eauto.
  Qed.

End CLC_step.

  Inductive function_entryT2 (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) (T:list mem_event): Prop :=
  | function_entry2_intro:
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variablesT g empty_env m f.(fn_vars) e m' T ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      function_entryT2 f vargs m e le m' T. 

  Lemma Hfe2_ax1 f vargs m e le m1 T (FE: function_entryT2 f vargs m e le m1 T):
    function_entry2 g f vargs m e le m1.
  Proof. inv FE. apply alloc_variablesT_ax1 in H2. econstructor; eauto. Qed.

  Lemma Hfe2_ax2 f vargs m e le m1 (FE: function_entry2 g f vargs m e le m1):
    exists T, function_entryT2 f vargs m e le m1 T.
  Proof. inv FE. apply alloc_variablesT_ax2 in H2. destruct H2 as [T HT].
         eexists; econstructor; eauto.
  Qed.

  Lemma Hfe2_fun f vargs m e1 le1 m1 T1 (FE1: function_entryT2 f vargs m e1 le1 m1 T1)
        e2 le2 m2 T2 (FE2: function_entryT2 f vargs m e2 le2 m2 T2): (e1,m1,T1)=(e2,m2,T2).
  Proof. inv FE1. inv FE2.
         exploit alloc_variablesT_fun. apply H7. apply H2. congruence.
  Qed.
  
  Lemma Hfe2_ev_elim f vargs m e le m1 T (FE: function_entryT2 f vargs m e le m1 T): ev_elim m T m1.
  Proof. inv FE. eapply alloc_variablesT_elim. eassumption. Qed. 

  Program Definition CLC_evsem : @EvSem state := {| msem := CLC_memsem g; ev_step := clc_evstep function_entryT2 |}.
  Next Obligation. simpl. intros. unfold part_semantics2; simpl.
                   apply clc_ax1 in H. destruct H as [AE [? [t Ht]]]; subst.
                   econstructor; simpl; trivial. apply Ht. apply Hfe2_ax1. Qed.
  Next Obligation. simpl. unfold part_semantics2; simpl. intros.
                   inv H; simpl in *. unfold step2 in H0. simpl in *.
                   eapply clc_ax2; eauto. apply Hfe2_ax2. Qed.
  Next Obligation. simpl. unfold part_semantics2; simpl. intros.
                   eapply clc_fun; try eassumption. intros.
                   exploit Hfe2_fun. apply FE2. apply FE1. congruence. Qed.
  Next Obligation. simpl; intros. eapply clc_ev_elim; eauto. apply Hfe2_ev_elim. Qed.

  Lemma CLC_msem : msem CLC_evsem = CLC_memsem g.
  Proof. auto. Qed.

  Lemma CLC_step_decay: forall c m tr c' m',
      event_semantics.ev_step (CLC_evsem) c m tr c' m' ->
      decay m m'.
Proof.
intros.
apply (msem_decay (CLC_memsem g) c m c' m').
simpl in *.
apply clc_ax1 in H.
destruct H as [? [? [t ?]]]; subst.
exploit (coreify (part_semantics2 g)); eauto.
intros.
inv H0.
constructor; auto.
eapply alloc_variablesT_ax1; eauto.
Qed.

  Instance ClightSem : Semantics :=
    { semG := G; semC := state; semSem := CLC_evsem; the_ge := g }.
End CLC_SEM.

  (* extending Clight_sim to event semantics *)
Inductive ev_star ge: state -> mem -> _ -> state -> mem -> Prop :=
  | ev_star_refl: forall s m,
      ev_star ge s m nil s m
  | ev_star_step: forall s1 m1 ev1 s2 m2 ev2 s3 m3,
      ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_star ge s2 m2 ev2 s3 m3 ->
      ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.

Lemma ev_star_one:
  forall ge s1 m1 ev s2 m2, ev_step (CLC_evsem ge) s1 m1 ev s2 m2 -> ev_star ge s1 m1 ev s2 m2.
Proof.
  intros. rewrite <- (app_nil_r ev). eapply ev_star_step; eauto. apply ev_star_refl.
Qed.

Lemma ev_star_two:
  forall ge s1 m1 ev1 s2 m2 ev2 s3 m3,
  ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_step (CLC_evsem ge) s2 m2 ev2 s3 m3 ->
  ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. eapply ev_star_step; eauto. apply ev_star_one; auto.
Qed.

Lemma ev_star_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_star ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_star ge s2 m2 ev2 s3 m3 -> ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  induction 1; intros; auto.
  rewrite <- app_assoc.
  eapply ev_star_step; eauto.
Qed.


Inductive ev_plus ge: state -> mem -> _ -> state -> mem -> Prop :=
  | ev_plus_left: forall s1 m1 ev1 s2 m2 ev2 s3 m3,
      ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_star ge s2 m2 ev2 s3 m3 ->
      ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.

Lemma ev_plus_one:
  forall ge s1 m1 ev s2 m2, ev_step (CLC_evsem ge) s1 m1 ev s2 m2 -> ev_plus ge s1 m1 ev s2 m2.
Proof.
  intros. rewrite <- (app_nil_r ev). eapply ev_plus_left; eauto. apply ev_star_refl.
Qed.

Lemma ev_plus_two:
  forall ge s1 m1 ev1 s2 m2 ev2 s3 m3,
  ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_step (CLC_evsem ge) s2 m2 ev2 s3 m3 ->
  ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. eapply ev_plus_left; eauto. apply ev_star_one; auto.
Qed.

Lemma ev_plus_star: forall ge s1 m1 ev s2 m2, ev_plus ge s1 m1 ev s2 m2 -> ev_star ge s1 m1 ev s2 m2.
Proof.
  intros. inv H. eapply ev_star_step; eauto.
Qed.

Lemma ev_plus_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_plus ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_plus ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros.
  inv H.
  rewrite <- app_assoc.
  eapply ev_plus_left. eauto.
  eapply ev_star_trans; eauto.
  apply ev_plus_star. auto.
Qed.

Lemma ev_star_plus_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_star ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_plus ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. inv H. auto.
  rewrite <- app_assoc.
  eapply ev_plus_left; eauto.
  eapply ev_star_trans; eauto. apply ev_plus_star; auto.
Qed.

Lemma ev_plus_star_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_plus ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_star ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros.
  inv H.
  rewrite <- app_assoc.
  eapply ev_plus_left; eauto. eapply ev_star_trans; eauto.
Qed.

Lemma exec_skipsT:
 forall ge {s0 k s k'}
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (CC.Kseq s k')))
   f ve te m mm,
   match s0 with Sskip => False | Scontinue => False | Sloop _ _ => False
            | Sifthenelse _ _ _ => False | Sreturn _ => False
            | _ => True end ->
   exists k2 mm', strip_skip' (CC.Kseq s k') = CC.Kseq s0 k2 /\
     ev_star ge (CC.State f s k' ve te mm) m nil (CC.State f s0 k2 ve te mm') m.
Proof.
 intros.
 remember (CC.Kseq s k') as k0.
 revert k s k' mm H1 Heqk0; induction k0; intros; inv Heqk0.
 assert ({s1=Sskip}+{s1<>Sskip}) by (destruct s1; try (left; congruence); right; congruence).
 destruct H0.
{ subst s1.
  destruct k'; try solve [inv H1].
  { specialize (IHk0 _ s k' m H1 (eq_refl _)).
    destruct IHk0 as [k2 [m2 [? ?]]].
    exists k2, m2. split; simpl; auto.
    replace nil with ((@nil mem_event)++nil) by reflexivity.
    econstructor 2. constructor. apply H2. }
  { inv H1; contradiction. }
  simpl in *. inv H1. contradiction. }
{ replace (strip_skip' (CC.Kseq s1 k')) with (CC.Kseq s1 k')  in *
     by (destruct s1; try congruence; auto).
  inv H1.
  exists k', mm; split; auto.
  constructor 1. }
Qed.

Lemma strip_evstep:
  forall ge ve te k m T st' m',
     cl_evstep ge (State ve te (strip_skip k)) m T st' m' <->
    cl_evstep ge (State ve te k) m T st' m'.
Proof.
intros.
 induction k; intros; split; simpl; intros; try destruct IHk; auto.
 destruct a; try destruct s; auto.
  constructor; auto.
 destruct a; try destruct s; auto.
 inv H. auto.
Qed.

Lemma ev_strip_skip'_loop1:
  forall ge f ve te m a3 s k1 k mm, CC.Kloop1 a3 s k1 = strip_skip' k ->
  exists mm', ev_star ge (CC.State f Sskip k ve te mm) m nil (CC.State f Sskip (CC.Kloop1 a3 s k1) ve te mm') m.
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. replace nil with (@nil mem_event++nil) by reflexivity. destruct (IHk m H) as [mm' ?]; exists mm'. eapply ev_star_trans; try eassumption; apply ev_star_one;
   constructor; eauto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. exists mm; constructor 1. simpl in H. inv H. exists mm; constructor 1.
Qed.

Lemma evstrip_skip'_loop2:
  forall ge f ve te m a3 s k1 k mm, CC.Kloop2 a3 s k1 = strip_skip' k ->
  exists mm', ev_star ge (CC.State f Sskip k ve te mm) m nil (CC.State f Sskip (CC.Kloop2 a3 s k1) ve te mm') m.
Proof.
 induction k; intros; try solve [inv H].
 { destruct (dec_skip s0).
   { subst. replace nil with (@nil mem_event++nil) by reflexivity.
     destruct (IHk m H) as [mm' ?]; exists mm'.
     eapply ev_star_trans; eauto.
     replace nil with (@nil mem_event++nil) by reflexivity. apply ev_star_one.
     constructor. }
   { rewrite strip_skip'_not in * by auto.
     rewrite <- H. exists mm; constructor 1. } }
 simpl in H. inv H. exists mm; constructor 1.
Qed.

Lemma evstrip_skip'_call:
  forall ge f ve te m lid f' ve' te' k1 k mm, CC.Kcall lid f' ve' te' k1 = strip_skip' k ->
  exists mm', ev_star ge (CC.State f Sskip k ve te mm) m nil (CC.State f Sskip (CC.Kcall lid f' ve' te' k1) ve te mm') m.
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s). subst. replace nil with (@nil mem_event++nil) by reflexivity. destruct (IHk m H) as [mm' ?]; exists mm'. eapply ev_star_trans; eauto. apply ev_star_one.
 constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. exists mm; constructor 1. simpl in H. inv H. exists mm; constructor 1.
Qed.

Lemma evexec_skips':
  forall ge f s k' s0 k0' ve te m mm,
        strip_skip' (CC.Kseq s k') = CC.Kseq s0 k0' ->
        exists mm', ev_star ge (CC.State f s k' ve te mm) m nil (CC.State f s0 k0' ve te mm') m.
Proof.
 intros.
 destruct (dec_skip s). subst. simpl in *.
 revert mm; induction k'; try solve [inv H].
 destruct (dec_skip s).
 { subst. simpl in *.
   replace nil with (@nil mem_event ++ nil) by reflexivity.
   destruct (IHk' H m) as [mm' ?]; exists mm'.
   econstructor 2; eauto. constructor. }
 { rewrite strip_skip'_not in * by auto.
   inv H. replace nil with (@nil mem_event ++ nil) by reflexivity.
   intro; exists m.
   econstructor 2; eauto. constructor. constructor 1. }
 { rewrite strip_skip'_not in H by auto. inv H. exists mm; constructor 1. }
Qed.

Lemma evstep_continue_strip:
  forall ge f k ve te m,
           ev_star ge (CC.State f Scontinue k ve te m) m nil
               (CC.State f Scontinue (strip_skip' k) ve te m) m.
Proof.
intros.
induction k; simpl; try (constructor 1).
destruct (dec_skip s).
{ subst. replace nil with (@nil mem_event ++ nil) by reflexivity.
  eapply ev_star_trans.
  apply ev_star_one. simpl. apply clc_evstep_continue_seq.
  auto. }
destruct s; try congruence; constructor 1.
Qed.

Lemma break_evstrip:
 forall ge f ve te m k mm,
     exists mm', ev_star ge (CC.State f Sbreak k ve te mm) m nil (CC.State f Sbreak (strip_skip' k) ve te mm') m.
Proof.
  induction k; try solve [eexists; constructor 1]. intros.
  destruct (dec_skip s).
  { subst. replace nil with (@nil mem_event ++ nil) by reflexivity.
    destruct (IHk m) as [mm' ?]; exists mm'.
    econstructor 2. constructor. eauto. } 
  { rewrite strip_skip'_not; auto. exists mm; constructor 1. }
Qed.

Lemma Clight_new_ev_sim : forall ge c1 m ev c1' m',
    event_semantics.ev_step (@semSem (Clight_newSem ge)) c1 m ev c1' m' ->
    forall c2, match_states c1 (fst (CC'.CC_state_to_CC_core c2)) ->
    exists c2', ev_plus ge c2 m ev c2' m' /\
      match_states c1' (fst (CC'.CC_state_to_CC_core c2')).
  Proof.
    (* based on Clight_sim.Clightnew_Clight_sim_eq_noOrder_SSplusConclusion *)
intros. simpl in H. revert c2 H0. induction H; intros.

{ (* step_assign *)
  destruct c2; simpl in *; inv H4. rename k0 into k'.
  simpl strip_skip in H6.
  destruct (exec_skipsT ge H6 f e le m m0) as [k2 [m2 [K2 STAR]]]; simpl; auto.
  exists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k2 e le) m').
  rewrite CC'.CC_core_CC_state_1; simpl. split.
  + replace (T1++T2++T3) with (nil ++ (T1++T2++T3)) by reflexivity.
    eapply ev_star_plus_trans; try eassumption;
      apply ev_plus_one; econstructor; eauto.
  + constructor. apply CUR. rewrite  K2 in H6. inv H6. assumption. }

{ (* step_set *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  destruct (exec_skipsT ge H2 f e le m m0) as [k2 [m2 [K2 STAR]]]; simpl; auto.
  exists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k2 e (PTree.set id v le)) m).
  rewrite CC'.CC_core_CC_state_1; simpl. split. 
  + replace T with (nil ++ T) by reflexivity.
    eapply ev_star_plus_trans; try eassumption;
      apply ev_plus_one; econstructor; eauto.
  + rewrite K2 in H2; inv H2; constructor; auto. }

{ (* step_call_internal *)
  destruct c2; simpl in *; inv H7. rename k0 into k'. 
  destruct (exec_skipsT ge H9 f0 e le m m0) as [k2 [m2 [K2 STAR]]]; simpl; auto.
  rewrite K2 in H9; inv H9. simpl in CUR.
  exists (CC_core_to_CC_state (CC'.CC_core_State f (fn_body f) (CC.Kcall optid f0 e le k2) ve' le') m1).
  rewrite CC'.CC_core_CC_state_1; simpl. split. 
  + replace (T1++T2++T3) with (nil ++ (T1++T2++T3)) by reflexivity.
    eapply ev_star_plus_trans; try eassumption.
    replace (T1++T2++T3) with ((T1++T2)++T3) by (rewrite app_assoc; trivial).
    eapply ev_plus_two. simpl. econstructor; try eassumption.
    econstructor; eauto.
    apply list_norepet_app in H4. destruct H4 as [? [? ?]].
    econstructor; auto.
  + constructor.
    simpl; auto.
    apply match_cont_strip. simpl. constructor; auto. }

{ (* step_call_external *)
  destruct c2; simpl in *; inv H3. rename k0 into k'. 
  destruct (exec_skipsT ge H5 f e le m m0) as [k2 [m2 [K2 STAR]]]; simpl; auto.
  rewrite K2 in H5; inv H5. simpl in CUR.
  exists (CC_core_to_CC_state (CC'.CC_core_Callstate
                                 (External ef tyargs tyres cc) vargs (CC.Kcall optid f e le k2)) m).
  rewrite CC'.CC_core_CC_state_1; simpl. split. 
  + replace (T1++T2) with (nil ++ (T1++T2)) by reflexivity.
    eapply ev_star_plus_trans; try eassumption;
      apply ev_plus_one; econstructor; eauto.
  + econstructor; eauto. }

{ (* step_seq *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  destruct (exec_skipsT ge H2 f e le m m0) as [k2 [m2 [K2 STAR]]]; simpl; auto.
  rewrite K2 in H2; inv H2. 
  destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f s1 (CC.Kseq s2 k2) e le) m))
    as [st2 [? ?]]; clear  IHcl_evstep.
  + repeat constructor; auto.
    apply match_cont_strip.  apply match_cont_strip.  auto.
  + exists st2; split; auto.
    replace T with (nil ++ (nil++T)) by reflexivity.
    eapply ev_star_plus_trans; try eassumption.
      eapply ev_plus_trans. apply ev_plus_one. constructor. eassumption. }

{ (* step_skip *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  simpl strip_skip in H2.
  remember (strip_skip k) as k0.
  destruct k0.
  elimtype False; clear - H Heqk0.
  revert H; induction k; intros. inv H.
  forget (a::k) as k';  clear - Heqk0 H.
  remember (State e le k') as s.
  revert e le k' Heqs Heqk0; induction H; intros; inv Heqs; simpl in *; try congruence.
  eapply IHcl_evstep. reflexivity. auto.
  remember (strip_skip' (CC.Kseq s k')) as k0'.
  destruct k0'; inv H2;
    try solve [rewrite <- strip_evstep in H; rewrite <- Heqk0 in H; inv H].
  +
    assert (s0<>Sskip).
    clear- Heqk0; intro; subst.
    revert Heqk0; induction k; simpl; intros. inv Heqk0. destruct a; try solve [inv Heqk0]; auto. destruct s; inv Heqk0; auto.
    destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f s k' e le) m0))
      as [st2 [? ?]]; clear  IHcl_evstep.
    constructor; auto. rewrite <- Heqk0. rewrite <- Heqk0'.
    constructor 2; auto. simpl in H2.
    exists st2; split; auto.
  +
    destruct s; inv Heqk0'.
    edestruct (ev_strip_skip'_loop1) as [m2 STAR]; eauto.
    destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f Sskip (CC.Kloop1 s0 s1 k0') e le) m2))
      as [st2 [? ?]]; clear  IHcl_evstep.
    constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
    exists st2; split; auto.
    simpl in H0. inv H0. rename ev1 into T1; rename ev2 into T2.
    eapply ev_plus_star_trans; try apply H5.
    clear - STAR H4.
    replace T1 with (nil++T1) by reflexivity.
    eapply ev_star_plus_trans; [ | apply ev_plus_one; eauto ].
    apply STAR.
  +
    destruct s; inv Heqk0'.
    edestruct evstrip_skip'_loop2 as [m2 STAR]; eauto.
    destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f Sskip (CC.Kloop2 s0 s1 k0') e le) m2))
      as [st2 [? ?]]; clear IHcl_evstep.
    econstructor; eauto. rewrite <- Heqk0. constructor. auto.
    exists st2; split; auto.
    replace T with (nil++T) by reflexivity.
    eapply ev_star_plus_trans; try apply H0.
    apply STAR.
  +
    destruct s; inv Heqk0'.
    destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f Sskip (CC.Kcall o f0 e0 t k0') e le) m0))
      as [st2 [? ?]]; clear IHcl_evstep.
    constructor; auto. rewrite <- Heqk0. constructor; auto.
    exists st2; split; auto.
    inv H0.
    eapply ev_plus_star_trans; [ | apply H5].
    inv H4.
    replace ([Free (blocks_of_env ge e)]) with (nil ++ [Free (blocks_of_env ge e)]) by reflexivity.
    edestruct evstrip_skip'_call as [m2' STAR]; eauto.
    eapply ev_star_plus_trans; [apply STAR | ].
    apply ev_plus_one. constructor; auto. }
    
{ (* step_continue *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  simpl strip_skip in H2; inv H2.
  +
    change (CC.Kseq Scontinue k'0 = strip_skip' (CC.Kseq s k')) in H4.
    symmetry in H4.
    rewrite continue_cont_skip in *.
    simpl in CUR.
    rewrite <- current_function_strip in CUR.
    forget (strip_skip k) as k0. clear k. rename k0 into k.
    generalize (continue_cont_is k); case_eq (continue_cont k); intros; try contradiction.
    rewrite H0 in H; inv H.
    destruct c; try contradiction. destruct l; try contradiction. destruct c; try contradiction.
    subst s0.
    assert (exists m2, ev_star ge (CC.State f s k' e le m0) m nil
                 (CC.State f Scontinue k'0 e le m2) m) as [m2 X1].
    { clear - H4.
      destruct (dec_skip s). subst. simpl in H4.
      edestruct evexec_skips' with (s := Sskip) as [m2 STAR]; eauto.
      rewrite strip_skip'_not in H4 by auto. inv H4. eexists; constructor. }
    assert (exists m3, ev_star ge (CC.State f Scontinue k'0 e le m2) m nil
                 (CC.State f Scontinue (strip_skip' k'0) e le m3) m) as [m3 X2].
    { clear.
      revert m2; induction k'0; try solve [eexists; constructor 1].
      destruct (dec_skip s).
      { subst. simpl in *.
        destruct (IHk'0 m).
        replace nil with (@nil mem_event ++ nil) by reflexivity. eexists; econstructor 2.
        constructor. apply H. }
      rewrite strip_skip'_not; auto. eexists; constructor 1. }
    generalize (ev_star_trans ge X1 X2); clear X1 X2; intro.
    clear H4.
    forget (strip_skip' k'0) as k0'; clear k'0.
    assert (precontinue_cont k = Kloop1 s1 s2 :: l).
    revert H0; clear; induction k; simpl; try congruence.  destruct a; try congruence; auto.
    assert (K1': exists k1' m4,
               ev_star ge (CC.State f Scontinue k0' e le m3) m nil
                    (CC.State f Scontinue k1' e le m4) m /\
               match_cont (Kseq Scontinue :: Kloop1 s1 s2 :: l) k1'). {
      clear - H1 H0.
      revert m3 H0; induction H1; simpl; intros; try congruence.
      { destruct (IHmatch_cont m) as [k1' [? [? ?]]].
        rewrite <- continue_cont_skip; auto.
        do 2 eexists. split; [ | eassumption].
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        eapply ev_star_trans; try apply H.
        clear.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        eapply ev_star_trans. apply ev_star_one.
        simpl. apply clc_evstep_continue_seq.
        apply evstep_continue_strip. }
      { inv H0.
        do 2 econstructor; split. constructor 1.  constructor.  auto. }
      { edestruct IHmatch_cont as [k1' [? [? ?]]].
        rewrite <- continue_cont_skip; auto.
        do 2 econstructor. split; [ | eassumption].
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        eapply ev_star_trans; try apply H.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        eapply ev_star_trans.
        + apply ev_star_one. simpl.
         apply clc_evstep_continue_switch.
        + apply evstep_continue_strip. }
    }
    destruct K1' as [k1' [? [STAR1 K1]]].
    generalize (ev_star_trans ge H2 STAR1); clear H2 STAR1; intro STAR.
    rewrite H0 in *.
    assert (CUR': match current_function l with
                  | Some f' => f' = f
                  | None => True
                  end). {
      clear - CUR H0. revert CUR H0; induction k; simpl; intros.
      inv H0.
      destruct a; try discriminate; auto.
      apply IHk. auto. auto. inv H0. auto.
      apply IHk; auto.
    }
    clear H1 CUR k H0 H3.
    inv K1. inv H3. simpl in *.
    destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f s2 (CC.Kloop2 s1 s2 k'0) e le) m))
                      as [st2 [? ?]]; clear IHcl_evstep.
    constructor; auto. apply match_cont_strip. constructor. auto.
    exists st2; split; auto.
    replace T with (nil++T) by reflexivity.
    eapply ev_star_plus_trans; [apply STAR | ].
    replace T with (nil++T) by reflexivity.
    eapply ev_star_plus_trans; [ | apply H0].
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    apply ev_star_one. constructor. auto.
 +
   change (CC.Kloop1 s0 e3 k'0 = strip_skip' (CC.Kseq s k')) in H1.
   destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
   subst s.
   simpl in H.
   simpl in H1.
   simpl in *.
   assert (exists m2, ev_star ge (CC.State f Sskip k' e le m0) m nil
                (CC.State f Sskip (CC.Kloop1 s0 e3 k'0) e le m2) m) as [m2 STAR].
   { rewrite H1; clear.
     revert m0; induction k'; intros; try solve [eexists; constructor 1].
     destruct (dec_skip s).
     { subst. simpl in *.
       replace nil with (@nil mem_event ++ nil) by reflexivity.
       destruct (IHk' m). eexists; econstructor 2; eauto.
       constructor. }
     { rewrite strip_skip'_not; auto. eexists; constructor 1. } }
   forget (CC.State f Sskip k' e le m0) as st1.
   clear k' H1.
   assert (PLUS: ev_plus ge st1 m nil (CC.State f e3 (CC.Kloop2 s0 e3 k'0) e le m) m).
   {
     replace nil with (@nil mem_event ++ nil) by reflexivity.
     eapply ev_star_plus_trans; try apply STAR.
     replace nil with (@nil mem_event ++ nil) by reflexivity.
     econstructor. econstructor. auto. constructor 1. }
   clear STAR.
   destruct (IHcl_evstep (CC_core_to_CC_state(CC'.CC_core_State f e3 (CC.Kloop2  s0 e3 k'0) e le) m))
     as [st2 [? ?]]; clear  IHcl_evstep.
   { constructor; auto. apply match_cont_strip; constructor; auto. }
   { exists st2; split; auto.
     replace T with (nil ++ T) by reflexivity. simpl in H0.
     eapply ev_plus_trans; eauto. } }

{ (* step_break *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  simpl strip_skip in H2; inv H2.
  change (CC.Kseq Sbreak k'0 = strip_skip' (CC.Kseq s k')) in H4.
  symmetry in H4.
  rewrite <- break_cont_skip in *.
  simpl in CUR.
  rewrite <- current_function_strip in CUR.
  forget (strip_skip k) as k0. clear k. rename k0 into k.
  simpl.
  destruct (evexec_skips' ge f s k' Sbreak k'0 e le m m0 H4) as [m1 ?].
  forget (CC.State f s k' e le m0) as st1.
  clear k' H4.
  edestruct (break_evstrip ge f e le m k'0 m1) as [m2 ?].
  pose proof (ev_star_trans ge H0 H2); clear H0 H2.
  forget (strip_skip' k'0) as k0'; clear k'0.
  assert (X:exists k1',
             ev_plus ge (CC.State f Sbreak k0' e le m2) m nil
                  (CC.State f Sskip k1' e le m) m
             /\ match_cont (strip_skip (break_cont k)) (strip_skip' k1')). {
    clear - H H1. rename H1 into H2.
    revert m2 H; induction H2; intros; try solve [inv H].
    { rewrite break_cont_skip in *. simpl in H.
      edestruct break_evstrip as [m1 ?].
      destruct (IHmatch_cont m1 H) as [k1' [? ?]]; clear IHmatch_cont. simpl.
      exists k1'; split; auto.
      replace nil with (@nil mem_event ++ nil) by reflexivity.
      eapply ev_star_plus_trans, H1.
      replace nil with (@nil mem_event ++ nil) by reflexivity.
      econstructor 2; eauto. constructor. }
      
    { simpl  in *.
      replace nil with (@nil mem_event ++ nil) by reflexivity.
      exists k'; split. econstructor.
      simpl. eapply clc_evstep_break_loop1. constructor 1. auto. }


    { simpl in *. 
      replace nil with (@nil mem_event ++ nil) by reflexivity.
      exists k'; split. econstructor. simpl. eapply clc_evstep_break_loop2. auto.
      constructor 1; auto.
      auto. }

    { simpl in *. 
      replace nil with (@nil mem_event ++ nil) by reflexivity.
      exists k'; split. econstructor. simpl. eapply clc_evstep_skip_break_switch. auto.
      constructor 1; auto.
      auto. }
  }
  
  destruct X as [k1' [? ?]].
  destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f Sskip k1' e le) m))
    as [st2 [? ?]]; clear IHcl_evstep.
  { constructor; auto.
    clear - H CUR.
    revert CUR; induction  k; intros. apply I.
    destruct a; simpl in *; auto. apply IHk; auto. }
  { exists st2; split; auto.
    simpl in H4.
    replace T with (nil ++ T) by reflexivity. 
    eapply ev_star_plus_trans; [ | eassumption].
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    eapply ev_star_trans; [eassumption | ]. 
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    apply ev_plus_star; eassumption. } }

{ (* step_ifthenelse *)
  destruct c2; simpl in *; inv H1. rename k0 into k'. 
  simpl strip_skip in H3; inv H3.
  change (CC.Kseq (Sifthenelse a s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H5.
  assert (exists m2, ev_star ge (CC.State f s k' e le m0) m nil (CC.State f (Sifthenelse a s1 s2) k'0 e le m2) m)
    as [m2 STAR]. {
     clear - H5.
     revert m0 H5; induction k'; intros; try solve [ destruct s; inv H5; eexists; constructor 1].
     destruct (dec_skip s).
     { subst s.
       destruct (dec_skip s0).
       { subst s0. simpl in *.
         replace nil with (@nil mem_event ++ nil) by reflexivity.
         destruct (IHk' m); auto.
         eexists; eapply ev_star_trans; eauto.
         replace nil with (@nil mem_event ++ nil) by reflexivity. apply ev_star_one.
         constructor. }
       { change (strip_skip' (CC.Kseq Sskip (CC.Kseq s0 k'))) with
               (strip_skip' (CC.Kseq s0 k')) in H5.
         rewrite strip_skip'_not in H5 by auto.
         inv H5.
         replace nil with (@nil mem_event ++ nil) by reflexivity. eexists; apply ev_star_one.
         constructor. } }
     { rewrite strip_skip'_not in * by auto.
       inv H5. eexists; constructor 1. }
  }
  exists (CC_core_to_CC_state (CC'.CC_core_State f (if b then s1 else s2) k'0 e le) m); split; auto.
  { 
    replace T with (nil ++ T) by reflexivity. eapply ev_star_plus_trans; try apply STAR.
    replace nil with (@nil mem_event ++ nil) by reflexivity. 
    apply ev_plus_one. econstructor; eauto. }
  { constructor; auto.
    apply match_cont_strip; auto. } }

{ (* step_loop *)
  destruct c2; simpl in *; inv H0. rename k0 into k'.
  inv H1. inv H3.
  change (CC.Kseq (Sloop s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H1.
  destruct (evexec_skips' ge f _ _ _ _ e le m m0 (@eq_sym _ _ _ H1)).
  exists (CC_core_to_CC_state (CC'.CC_core_State f s1 (CC.Kloop1 s1 s2 k'0) e le) m); split.
  { replace nil with (@nil mem_event ++ nil) by reflexivity.
    eapply ev_star_plus_trans; try apply H.
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    apply ev_plus_one. simpl. eapply clc_evstep_loop; eauto. }
  { constructor; auto. apply match_cont_strip; constructor; auto. } }

{ (* step_loop2 *)
  destruct c2; simpl in *; inv H0. rename k0 into k'.
  inv H1.
  destruct s0; inv H4.
  destruct (evstrip_skip'_loop2 ge f e le m _ _ _ _ m0 H1).
  exists (CC_core_to_CC_state (CC'.CC_core_State f s (CC.Kloop1 s a3 k'0) e le) m); split.
  + replace nil with (@nil mem_event ++ nil) by reflexivity.
    eapply ev_star_plus_trans; try apply H.
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    econstructor. simpl. eapply clc_evstep_skip_loop2; eauto.
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    apply ev_star_one. simpl. eapply clc_evstep_loop; eauto.
  + constructor; auto. apply match_cont_strip. constructor. auto. }

{ (* step_return *)
  destruct c2; simpl in *; inv H3. rename k0 into k'0.
  remember (strip_skip' (CC.Kseq s k'0)) as k3. simpl in CUR, H5.
  inv H5.
  { (*first case*)
    destruct (evexec_skips' ge f0 _ _ _ _ e le m m0 (@eq_sym _ _ _ H4)) as [? H99].
    assert (f0=f).
    { simpl in CUR; clear - CUR H.
      revert H CUR; induction k; intros. inv H. simpl in *. destruct a; auto. inv CUR; auto. inv H; auto.
    }
    subst f.
    generalize (match_cont_call_strip k k'1); intro.
    spec H3; [congruence |]. spec H3; [auto |].
    generalize H3; rewrite H; intro.
    inv H5.
    +  elimtype False; clear - H10.
       revert H10; induction k'1; simpl; intros; congruence.
    + destruct optexp;  [destruct H1 as [v [? ?]] | ]; (destruct optid; destruct H2 as [H2 H2'];
               try solve [contradiction H2; auto]; subst te'' ).
    -   eexists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k'2 ve' (PTree.set i v' te')) m').
        split.
        { replace (T ++ [Free (blocks_of_env ge e)]) with ((T ++ [Free (blocks_of_env ge e)]) ++ nil) by (rewrite app_nil_r; trivial).
          apply (ev_star_plus_trans ge H99). (*with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m).  apply H99. *)
          eapply (@ev_plus_trans ge) with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
          eapply ev_plus_one. simpl. eapply clc_evstep_return_1; eauto. 
          eapply ev_plus_one. simpl. rewrite <- H13.
          eapply clc_evstep_returnstate. }
        constructor; auto.
    -   eexists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k'2 ve' te') m').
        split.
        { replace (T ++ [Free (blocks_of_env ge e)]) with ((T ++ [Free (blocks_of_env ge e)]) ++ nil) by (rewrite app_nil_r; trivial).
          eapply (ev_star_plus_trans ge H99). (* with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m). apply H99. *)
          eapply (@ev_plus_trans ge) with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
          eapply ev_plus_one. simpl. econstructor; eauto.
          eapply ev_plus_one. simpl. rewrite <- H13. eapply clc_evstep_returnstate. }
        constructor; auto.
    -   destruct H1; subst.
        eexists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k'2 ve' (CC.set_opttemp (Some i) Vundef te')) m').
        split.
        { eapply (ev_star_plus_trans ge H99).  (*with (s2:=CC.State f0 (Sreturn None) k'1 ve te m).  apply H99. *)
          replace [Free (blocks_of_env ge e)] with (([Free (blocks_of_env ge e)] ++ nil) ++ nil)
            by (rewrite app_nil_r; trivial).  
          eapply (@ev_plus_trans ge) with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
          eapply ev_plus_one. simpl. econstructor; eauto.
          eapply ev_plus_one. simpl. rewrite <- H13.
          apply clc_evstep_returnstate. } 
        simpl. constructor 1. auto. simpl.  auto.
    - destruct H1; subst.
      eexists (CC_core_to_CC_state (CC'.CC_core_State f Sskip k'2 ve' te') m').
      split.
      { eapply (ev_star_plus_trans ge H99).
        replace [Free (blocks_of_env ge e)] with (([Free (blocks_of_env ge e)] ++ nil) ++ nil)
          by (rewrite app_nil_r; trivial). 
        eapply (@ev_plus_trans) with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
        eapply ev_plus_one. simpl. econstructor; eauto.
        eapply ev_plus_one. simpl. rewrite <- H13.
        apply clc_evstep_returnstate. }
      simpl. constructor 1. auto. simpl.  auto. }
  { (*second case*)
    destruct H1; subst. destruct optid; destruct H2 as [_ H2]; subst te''.
    { simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR. 
      destruct s; inv H4.
      assert (exists m2, ev_star ge (CC.State f Sskip k'0 e le m0) m nil
                            (CC.State f Sskip (CC.Kcall (Some i) f1 ve' te' k'1) e le m2) m) as [m2 STAR].
      { clear - H1.
        revert m0 H1; induction k'0; intros; try solve [inv H1].
        destruct (dec_skip s). subst s. simpl in H1.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        destruct (IHk'0 m); auto.
        eexists; eapply ev_star_trans; eauto.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        apply ev_star_one. simpl. constructor; auto.
        rewrite strip_skip'_not in H1 by auto. rewrite <- H1. eexists; constructor 1.
        simpl in H1. inv H1. eexists; constructor 1. }
      eexists; split.
      { eapply ev_star_plus_trans. apply STAR.
        replace [Free (blocks_of_env ge e)] with ([Free (blocks_of_env ge e)] ++ nil)
          by (rewrite app_nil_r; trivial).
        eapply ev_plus_two.
        + simpl. eapply clc_evstep_skip_call; simpl; eauto.
        + simpl. apply clc_evstep_returnstate. }
      econstructor; eauto. }
    { simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
      destruct s; inv H4.
      assert (exists m2, ev_star ge (CC.State f Sskip k'0 e le m0) m nil
                            (CC.State f Sskip (CC.Kcall None f1 ve' te' k'1) e le m2) m) as [m2 STAR].
      { clear - H1.
        revert m0 H1; induction k'0; intros; try solve [inv H1].
        destruct (dec_skip s). subst s. simpl in H1.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        destruct (IHk'0 m); auto.
        eexists; eapply ev_star_trans; eauto.
        replace nil with (@nil mem_event ++ nil) by reflexivity.
        apply ev_star_one. simpl. constructor; auto.
        rewrite strip_skip'_not in H1 by auto. rewrite <- H1. eexists; constructor 1.
        simpl in H1. inv H1. eexists; constructor 1. }
      eexists; split.
      { eapply ev_star_plus_trans. apply STAR.
        replace [Free (blocks_of_env ge e)] with ([Free (blocks_of_env ge e)] ++ nil)
          by (rewrite app_nil_r; trivial).
        eapply ev_plus_two.
        + simpl. eapply clc_evstep_skip_call; simpl; eauto.
        + simpl.  apply clc_evstep_returnstate. }
      econstructor; eauto. } } }

{ (* step_switch *)
  destruct c2; simpl in *; inv H1. rename k0 into k'.
  simpl strip_skip in H3.
  remember (CC.Kseq s k') as k0'.
  inv H3.
  exists  (CC'.CC_core_to_CC_state (CC'.CC_core_State f (seq_of_labeled_statement (select_switch n sl)) 
              (Clight.Kswitch k'0) e le) m); split.
  { destruct (evexec_skips' ge f _ _ _ _ e le m m0 (@eq_sym _ _ _ H5)) as [? H99].
    replace T with (nil++T) by reflexivity. eapply ev_star_plus_trans; try apply H99.
    eapply ev_plus_one. simpl. econstructor; eassumption. }
  { simpl. constructor; auto. apply match_cont_strip. constructor; auto. } }
  
{ (* step_label *)
  destruct c2; simpl in *; inv H0. rename k0 into k'. 
  remember (CC.Kseq s0 k') as k0'. inv H2.
  destruct (IHcl_evstep (CC_core_to_CC_state (CC'.CC_core_State f s k'0 e le) m)) as [st2 [? ?]]; clear IHcl_evstep.
  { constructor; auto. apply match_cont_strip. auto. }
  exists st2; split; auto. simpl in H0.
  replace T with (nil++T) by reflexivity.
  eapply ev_star_plus_trans; try eassumption.
  replace nil with (@nil mem_event ++ nil) by reflexivity.
  destruct (evexec_skips' ge f _ _ _ _ e le m m0 (@eq_sym _ _ _ H4)).
  eapply ev_star_trans; eauto.
  apply ev_star_one. constructor. } 

{ (* step_goto *)
  destruct c2; simpl in *; inv H0. 
  remember (CC.Kseq s k0) as k0'. inv H2.
  generalize (match_cont_call_strip k k'0(*k'1*)); intro.
  spec H0.
  { clear - CUR. apply (call_cont_nonnil _ _ CUR). }
  specialize (H0 H1).
  rewrite <- strip_call' in H0.
  change (Kseq (Sreturn None) :: call_cont k) with (strip_skip (Kseq (Sreturn None) :: call_cont k)) in H0.
  destruct (match_find_label _ _ _ _ _ H0 H) as [s2 [k2' [? ?]]].
  exists (CC'.CC_core_to_CC_state (CC'.CC_core_State f s2 k2' e le) m); split.
  { simpl in CUR0. inversion2 CUR CUR0.
    destruct (evexec_skips' ge f _ _ _ _ e le m m0 (@eq_sym _ _ _ H4)) as [? H99].
    replace nil with (@nil mem_event ++ nil) by reflexivity.
    eapply ev_star_plus_trans; try apply H99.
    apply ev_plus_one. constructor; auto. }
  constructor; auto.
  clear - CUR H. forget (fn_body f) as s.
  rewrite <- current_function_call_cont in CUR.
  change (current_function (Kseq (Sreturn None) :: call_cont k) = Some f) in CUR.
  forget (Kseq (Sreturn None) :: call_cont k) as k0. clear - CUR H.
  rewrite (current_function_find_label _ _ _ _ _ CUR H). auto.
  apply match_cont_strip1. auto. }
Qed.

