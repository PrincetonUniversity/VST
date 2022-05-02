(* adapted from concurrency/common/ClightSemanticsForMachines.v *)

(* Event semantics for ClightCore *)

Require Import compcert.common.Memory.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

Require Import List. Import ListNotations.
Import compcert.lib.Maps.

Import Ctypes. 
Require Import compcert.cfrontend.Clight.
Import Cop.
Arguments sizeof {env} !t / .

(*Semantics*)
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.

Lemma extcall_malloc_sem_inv: forall g v m t res m2 (E:Events.extcall_malloc_sem g v m t res m2),
  exists m1 b (sz : ptrofs), v=[Vptrofs sz] /\ t= Events.E0 /\ res=Vptr b Ptrofs.zero /\
                           Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m1, b) /\
                           Mem.store Mptr m1 b (- size_chunk Mptr) (Vptrofs sz) = Some m2. 
Proof. intros.  inv E. exists m', b, sz. intuition. Qed.

Inductive load_bitfieldT: type -> intsize -> signedness -> Z -> Z -> mem -> block -> ptrofs -> val -> list memval -> Prop :=
  | load_bitfield_intro: forall sz sg1 attr sg pos width m b ofs c bytes,
      0 <= pos -> 0 < width <= bitsize_intsize sz -> pos + width <= bitsize_carrier sz ->
      sg1 = (if zlt width (bitsize_intsize sz) then Signed else sg) ->
      (align_chunk (chunk_for_carrier sz) | (Ptrofs.unsigned ofs)) ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) = Some bytes ->
      decode_val (chunk_for_carrier sz) bytes = Vint c ->
      load_bitfieldT (Tint sz sg1 attr) sz sg pos width m b ofs
                    (Vint (bitfield_extract sz sg pos width c)) bytes.

Inductive deref_locT (ty : type) (m : mem) (b : block) (ofs : ptrofs) : bitfield -> val -> list mem_event -> Prop :=
    deref_locT_value : forall (chunk : memory_chunk) bytes,
                      access_mode ty = By_value chunk ->
                      (align_chunk chunk | (Ptrofs.unsigned ofs)) ->
                      Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk chunk) = Some bytes ->
(*                      Mem.load chunk m b (Ptrofs.unsigned ofs) = Some (decode_val chunk bytes) ->*)
                      deref_locT ty m b ofs Full (decode_val chunk bytes) (Read b (Ptrofs.unsigned ofs) (size_chunk chunk) bytes :: nil)
  | deref_locT_reference : access_mode ty = By_reference -> deref_locT ty m b ofs Full (Vptr b ofs) nil
  | deref_locT_copy : access_mode ty = By_copy -> deref_locT ty m b ofs Full (Vptr b ofs) nil
  | deref_locT_bitfield : forall (sz : intsize) 
                           (sg : signedness) (pos width : Z) 
                           (v : val) bytes,
                         load_bitfieldT ty sz sg pos width m 
                           b ofs v bytes ->
                         deref_locT ty m b ofs (Bits sz sg pos width) v (Read b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) bytes :: nil)
.

Lemma deref_locT_ax1 a m loc ofs v bf T (D:deref_locT (typeof a) m loc ofs bf v T):
      deref_loc (typeof a) m loc ofs bf v.
Proof. 
  inv D.
  + eapply deref_loc_value; eauto. eapply Mem.loadbytes_load; eauto.
  + apply deref_loc_reference; trivial.
  + apply deref_loc_copy; trivial.
  + inv H; apply deref_loc_bitfield; constructor; auto.
    rewrite <- H7; apply Mem.loadbytes_load; auto.
Qed.

Lemma deref_locT_ax2 a m loc ofs bf v (D:deref_loc (typeof a) m loc ofs bf v):
      exists T, deref_locT (typeof a) m loc ofs bf v T.
Proof. 
  inv D.
  + exploit Mem.load_valid_access; eauto. intros [_ ALGN].
    exploit Mem.load_loadbytes; eauto. intros [bytes [LD V]]; subst v.
    eexists; eapply deref_locT_value; eauto. 
  + eexists; apply deref_locT_reference; trivial.
  + eexists; apply deref_locT_copy; trivial.
  + inv H.
    exploit Mem.load_valid_access; eauto. intros [_ ALGN].
    exploit Mem.load_loadbytes; eauto. intros [bytes [LD V]].
    eexists; apply deref_locT_bitfield; constructor; eauto.
Qed.

Lemma deref_locT_fun a m loc ofs bf v1 T1 (D1:deref_locT (typeof a) m loc ofs bf v1 T1)
      v2 T2 (D2:deref_locT (typeof a) m loc ofs bf v2 T2): (v1,T1)=(v2,T2). 
Proof. inv D1; inv D2; try congruence.
  inv H; inv H6; congruence. Qed.

Lemma deref_locT_elim  a m b ofs bf v T (D:deref_locT (typeof a) m b ofs bf v T):
       ev_elim m T m /\
       (forall mm mm' (E:ev_elim mm T mm'),
           mm'=mm /\ deref_locT (typeof a) mm b ofs bf v T).
Proof.
  inv D; simpl.
  - intuition. subst. eapply deref_locT_value; trivial.
  - intuition. subst. eapply deref_locT_reference; trivial.
  - intuition. subst. eapply deref_locT_copy; trivial.
  - inv H. intuition. subst. apply deref_locT_bitfield; constructor; auto.
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
      eval_lvalueT a loc ofs Full T ->
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
  | evalT_Elvalue: forall a loc ofs bf v T1 T2 T,
      eval_lvalueT a loc ofs bf T1 ->
      deref_locT (typeof a) m loc ofs bf v T2 -> T=(T1 ++ T2) ->
      eval_exprT a v T

with eval_lvalueT: expr -> block -> ptrofs -> bitfield -> list mem_event-> Prop :=
  | evalT_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalueT (Evar id ty) l Ptrofs.zero Full nil
  | evalT_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol g id = Some l ->
      eval_lvalueT (Evar id ty) l Ptrofs.zero Full nil
  | evalT_Ederef: forall a ty l ofs T,
      eval_exprT a (Vptr l ofs) T ->
      eval_lvalueT (Ederef a ty) l ofs Full T
 | evalT_Efield_struct:   forall a i ty l ofs id co att delta bf T,
      eval_exprT a (Vptr l ofs) T ->
      typeof a = Tstruct id att ->
      g.(genv_cenv)!id = Some co ->
      field_offset g i (co_members co) = Errors.OK (delta, bf) ->
      eval_lvalueT (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf T
 | evalT_Efield_union:   forall a i ty l ofs id co att delta bf T,
      eval_exprT a (Vptr l ofs) T ->
      typeof a = Tunion id att ->
      g.(genv_cenv)!id = Some co ->
      union_field_offset g i (co_members co) = Errors.OK (delta, bf) ->
      eval_lvalueT (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf T.

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
with eval_lvalueT_ax1: forall a b z bf T, eval_lvalueT a b z bf T -> eval_lvalue g e le m a b z bf.
Proof.
  + induction 1; econstructor; eauto. eapply deref_locT_ax1; eauto.
  + induction 1; try solve [econstructor; eauto].
Qed.

Lemma eval_exprT_ax2: forall a v, eval_expr g e le m a v -> exists T, eval_exprT a v T
with eval_lvalueT_ax2: forall a b z bf, eval_lvalue g e le m a b z bf -> exists T, eval_lvalueT a b z bf T.
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
    (forall a b1 b2 i1 i2 bf1 bf2 T1 T2, eval_lvalueT a b1 i1 bf1 T1 -> eval_lvalueT a b2 i2 bf2 T2 ->
                               (b1,i1,bf1,T1)=(b2,i2,bf2,T2)).
Proof.
 destruct (eval_exprT_lvalue_ind
   (fun a v T =>  forall v' T', eval_exprT a v' T' -> (v,T)=(v',T'))
   (fun a b i bf T => forall b' i' bf' T', eval_lvalueT a b' i' bf' T' -> (b,i,bf,T)=(b',i',bf',T')));
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
 { inv H1. apply H0 in H8; congruence. }
 { inv H4. { apply H0 in H8; congruence. }
           { congruence. } }
 { inv H4. { congruence. }
           { apply H0 in H8; congruence. } }

 split; intros. apply (H _ _ _ H1 _ _ H2). apply (H0 _ _ _ _ _ H1 _ _ _ _ H2).
Qed.

Lemma eval_exprT_fun a v1 T1 v2 T2: eval_exprT a v1 T1 -> eval_exprT a v2 T2 -> (v1,T1)=(v2,T2).
Proof. apply eval_exprT_lvalueT_fun. Qed.

Lemma eval_lvalueT_fun a b1 b2 i1 i2 bf1 bf2 T1 T2: eval_lvalueT a b1 i1 bf1 T1 -> eval_lvalueT a b2 i2 bf2 T2 ->
                               (b1,i1,bf1,T1)=(b2,i2,bf2,T2).
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
         forall m a b z bf T (E:eval_lvalueT g e le m a b z bf T),
           ev_elim m T m.
Proof.
  + clear eval_exprT_elim; induction 1; try solve [econstructor]; eauto.
    { eapply ev_elim_app; eassumption. }
    { subst. specialize (eval_lvalueT_elim _ _ _ _ _ _ _ _ _ H). 
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

Inductive store_bitfieldT: type -> intsize -> signedness -> Z -> Z -> mem -> block -> ptrofs -> val -> mem -> val -> list memval -> int -> int -> Prop :=
  | store_bitfield_intro: forall sz sg1 attr sg pos width m b ofs c n m' bytes,
      0 <= pos -> 0 < width <= bitsize_intsize sz -> pos + width <= bitsize_carrier sz ->
      sg1 = (if zlt width (bitsize_intsize sz) then Signed else sg) ->
      (align_chunk (chunk_for_carrier sz) | (Ptrofs.unsigned ofs)) ->
      Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) = Some bytes ->
      decode_val (chunk_for_carrier sz) bytes = Vint c ->
      Mem.store (chunk_for_carrier sz) m b (Ptrofs.unsigned ofs)
                 (Vint (Int.bitfield_insert (first_bit sz pos width) width c n)) = Some m' ->
      store_bitfieldT (Tint sz sg1 attr) sz sg pos width m b ofs (Vint n)
                     m' (Vint (bitfield_normalize sz sg width n)) bytes c n.

Inductive assign_locT (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs)
  : bitfield -> val -> mem -> list mem_event -> Prop :=
    assign_locT_value : forall (v : val) (chunk : memory_chunk) (m' : mem),
                       access_mode ty = By_value chunk ->
                       Mem.storev chunk m (Vptr b ofs) v = Some m' ->
                       assign_locT ce ty m b ofs Full v m' (Write b (Ptrofs.unsigned ofs) (encode_val chunk v) ::nil)
  | assign_locT_copy : forall (b' : block) (ofs' : ptrofs) (bytes : list memval) (m' : mem),
                      access_mode ty = By_copy ->
                      (@sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
                      (@sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
                      b' <> b \/
                      Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
                      Ptrofs.unsigned ofs' + @sizeof ce ty <= Ptrofs.unsigned ofs \/
                      Ptrofs.unsigned ofs + @sizeof ce ty <= Ptrofs.unsigned ofs' ->
                      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (@sizeof ce ty) = Some bytes ->
                      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
                      assign_locT ce ty m b ofs Full (Vptr b' ofs') m'
                                  (Read b' (Ptrofs.unsigned ofs') (@sizeof ce ty) bytes ::
                                   Write b (Ptrofs.unsigned ofs) bytes :: nil)
  | assign_locT_bitfield : forall (sz : intsize) 
                            (sg : signedness) (pos width : Z) 
                            (v : val) (m' : mem) 
                            (v' : val) bytes c n,
                          store_bitfieldT ty sz sg pos width m
                            b ofs v m' v' bytes c n ->
                          assign_locT ce ty m b ofs
                            (Bits sz sg pos width) v m'
                                  (Read b (Ptrofs.unsigned ofs) (size_chunk (chunk_for_carrier sz)) bytes ::
                                   Write b (Ptrofs.unsigned ofs) (encode_val (chunk_for_carrier sz)
                                     (Vint (Int.bitfield_insert (first_bit sz pos width) width c n))) :: nil).

Lemma assign_locT_ax1 ce ty m b ofs bf v m' T (A:assign_locT ce ty m b ofs bf v m' T):
    assign_loc ce ty m b ofs bf v m'.
Proof.
  destruct A; [eapply assign_loc_value; eauto | eapply assign_loc_copy; eauto | eapply assign_loc_bitfield; eauto].
  inv H; econstructor; eauto.
  rewrite <- H6; apply Mem.loadbytes_load; auto.
Qed.

Lemma assign_locT_ax2 ce ty m b ofs bf v m' (A:assign_loc ce ty m b ofs bf v m'):
    exists T, assign_locT ce ty m b ofs bf v m' T.
Proof.
  inv A; [eexists; eapply assign_locT_value; eauto | eexists; eapply assign_locT_copy; eauto|].
  inv H.
  exploit Mem.load_valid_access; eauto. intros [_ ALGN].
  eapply Mem.load_loadbytes in H4 as (? & ? & ?).
  eexists; econstructor; econstructor; eauto.
Qed.

Lemma assign_locT_fun ce ty m b ofs bf v m1 T1
      (A1:assign_locT ce ty m b ofs bf v m1 T1) m2 T2 (A2:assign_locT ce ty m b ofs bf v m2 T2):
      (m1,T1)=(m2,T2).
Proof. inv A1; inv A2; try congruence.
  inv H; inv H7; congruence. Qed.

Lemma assign_locT_elim ce ty m b ofs bf v m1 T (A:assign_locT ce ty m b ofs bf v m1 T):
  ev_elim m T m1 /\
  forall mm mm1 (E: ev_elim mm T mm1),
    assign_locT ce ty mm b ofs bf v mm1 T.
Proof.
  inv A; simpl.
  - exploit Mem.store_valid_access_3; eauto. intros [_ A].
    apply Mem.store_storebytes in H0.
    split. { exists m1; split; trivial. }
    intros. destruct E as [? [? ?]]; subst. econstructor; eauto.
    apply Mem.storebytes_store; eassumption.
  - split. { split; [trivial | exists m1; split; trivial]. }
    intros. destruct E as [LD [? [? ?]]]; subst.
    constructor; eassumption.
  - inv H.
    apply Mem.store_storebytes in H7.
    split. { split; [trivial | exists m1; split; trivial]. }
    intros. destruct E as [LD [? [? ?]]]; subst.
    econstructor; constructor; eauto.
    apply Mem.storebytes_store; auto.
Qed. 

Section CLC_SEM.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := CC_core.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
(** Transition relation *)

Inductive cl_evstep (ge: Clight.genv): forall (q: CC_core) (m: mem) (T:list mem_event) (q': CC_core) (m': mem), Prop :=

  | evstep_assign:   forall f a1 a2 k e le m loc ofs bf v2 v m' T1 T2 T3,
(*     type_is_volatile (typeof a1) = false ->*)
      eval_lvalueT ge e le m a1 loc ofs bf T1 ->
      eval_exprT ge e le m a2 v2 T2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_locT ge (typeof a1) m loc ofs bf v m' T3 ->
      cl_evstep ge (State f (Sassign a1 a2) k e le) m (T1++T2++T3) 
                  (State f Sskip k e le) m'

  | evstep_set:   forall f id a k e le m v T,
      eval_exprT ge e le m a v T ->
      cl_evstep ge (State f (Sset id a) k e le) m T
              (State f Sskip k e (PTree.set id v le)) m

  | evstep_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd T1 T2,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_exprT ge e le m a vf T1 ->
      eval_exprTlist ge e le m al tyargs vargs T2 ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      cl_evstep ge (State f (Scall optid a al) k e le) m (T1++T2)
                  (Callstate fd vargs (Kcall optid f e le k)) m

  | evstep_builtin : forall (f : function)
                     (optid : option ident) (ef : external_function)
                     (tyargs : typelist) (al : list expr) 
                     (k : cont) (e : env) (le : temp_env) 
                     (m : mem) (vargs : list val) 
                     (t : Events.trace) (vres : val) 
                     (m' : mem) T (EFI : ef_inline ef = true) (EFC : Events.external_call ef ge vargs m t vres m'),
                   ef_deterministic ef = true ->
                   eval_exprTlist ge e le m al tyargs vargs T ->
                   cl_evstep ge
                     (State f (Sbuiltin optid ef tyargs al) k e le) m
                     (T ++ proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC))
                     (State f Sskip k e (set_opttemp optid vres le)) m'

  | evstep_seq:  forall f s1 s2 k e le m,
      cl_evstep ge (State f (Ssequence s1 s2) k e le) m nil
                 (State f s1 (Kseq s2 k) e le) m

  | evstep_skip_seq: forall f s k e le m,
      cl_evstep ge (State f Sskip (Kseq s k) e le) m nil
              (State f s k e le) m

  | evstep_continue_seq: forall f s k e le m,
      cl_evstep ge (State f Scontinue (Kseq s k) e le) m nil
             (State f Scontinue k e le) m

  | evstep_break_seq: forall f s k e le m,
      cl_evstep ge (State f Sbreak (Kseq s k) e le) m nil
            (State f Sbreak k e le) m

  | evstep_ifthenelse:  forall f a s1 s2 k e le m v1 b T,
      eval_exprT ge e le m a v1 T ->
      bool_val v1 (typeof a) m = Some b ->
      cl_evstep ge (State f (Sifthenelse a s1 s2) k e le) m T
            (State f (if b then s1 else s2) k e le) m

  | evstep_loop: forall f s1 s2 k e le m,
      cl_evstep ge (State f (Sloop s1 s2) k e le) m nil
            (State f s1 (Kloop1 s1 s2 k) e le) m

  | evstep_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      cl_evstep ge (State f x (Kloop1 s1 s2 k) e le) m nil
            (State f s2 (Kloop2 s1 s2 k) e le) m

  | evstep_break_loop1:  forall f s1 s2 k e le m,
      cl_evstep ge (State f Sbreak (Kloop1 s1 s2 k) e le) m nil
             (State f Sskip k e le) m

  | evstep_skip_loop2: forall f s1 s2 k e le m,
      cl_evstep ge (State f Sskip (Kloop2 s1 s2 k) e le) m nil
             (State f (Sloop s1 s2) k e le) m

  | evstep_break_loop2: forall f s1 s2 k e le m,
      cl_evstep ge (State f Sbreak (Kloop2 s1 s2 k) e le) m nil
            (State f Sskip k e le) m

  | evstep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      cl_evstep ge (State f (Sreturn None) k e le) m
            (Free (Clight.blocks_of_env ge e)::nil)
            (Returnstate Vundef (call_cont k)) m'

  | evstep_return_1: forall f a k e le m v v' m' T,
      eval_exprT ge e le m a v T ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      cl_evstep ge (State f (Sreturn (Some a)) k e le) m
            (T ++ Free (Clight.blocks_of_env ge e)::nil)
           (Returnstate v' (call_cont k)) m'

  | evstep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      cl_evstep ge (State f Sskip k e le) m
              (Free (Clight.blocks_of_env ge e)::nil)
              (Returnstate Vundef k) m'

  | evstep_switch: forall f a sl k e le m v n T,
      eval_exprT ge e le m a v T ->
      sem_switch_arg v (typeof a) = Some n ->
      cl_evstep ge (State f (Sswitch a sl) k e le) m T
            (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m

  | evstep_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      cl_evstep ge (State f x (Kswitch k) e le) m nil
             (State f Sskip k e le) m
  | evstep_continue_switch: forall f k e le m,
      cl_evstep ge (State f Scontinue (Kswitch k) e le) m nil
             (State f Scontinue k e le) m

  | evstep_label: forall f lbl s k e le m,
      cl_evstep ge (State f (Slabel lbl s) k e le) m nil
             (State f s k e le) m

  | evstep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      cl_evstep ge (State f (Sgoto lbl) k e le) m nil
             (State f s' k' e le) m

  | evstep_internal_function: forall f vargs k m e le m1 T,
       list_norepet (var_names (fn_params f)) ->
       list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)) ->
      forall (NRV: list_norepet (var_names f.(fn_vars))),
      alloc_variablesT ge empty_env m (f.(fn_vars)) e m1 T ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some
le ->
      cl_evstep ge (Callstate (Internal f) vargs k) m T
            (State f f.(fn_body) k e le) m1

  | evstep_external_function: forall ef targs tres cconv vargs k m t vres m' T
          (EFI: ef_inline ef = true)
          (EFD: ef_deterministic ef = true)
          (EC: Events.external_call ef ge vargs m t vres m'),
      T = proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EC) ->
      cl_evstep ge (Callstate (External ef targs tres cconv) vargs k) m T
          (Returnstate vres k) m'

  | evstep_returnstate: forall v optid f e le k m,
      cl_evstep ge (Returnstate v (Kcall optid f e le k)) m nil
           (State f Sskip k e (set_opttemp optid v le)) m.

  Lemma CLC_evstep_ax1 ge : forall c m T c' m' (H: cl_evstep ge c m T c' m' ),
    corestep (CLC_memsem ge) c m c' m'.
  Proof.
    induction 1; try solve [econstructor; eassumption].
    +  apply eval_lvalueT_ax1 in H. apply eval_exprT_ax1 in H0.
         apply assign_locT_ax1 in H2. econstructor; eauto.
    +  apply eval_exprT_ax1 in H. econstructor; eauto.
    + apply eval_exprT_ax1 in H0.
      apply eval_exprTlist_ax1 in H1. econstructor; eauto.
    + apply eval_exprTlist_ax1 in H0. econstructor; eauto.
      apply andb_true_iff; auto.
    + apply eval_exprT_ax1 in H. econstructor; eauto.
    + apply eval_exprT_ax1 in H. econstructor; eauto.
    + apply eval_exprT_ax1 in H. econstructor; eauto.
    + apply alloc_variablesT_ax1 in H1. econstructor; eauto.
         econstructor; eauto.
    + econstructor; eauto.
      rewrite EFI; auto.
  Qed.

  Lemma CLC_evstep_ax2 ge : forall c m c' m' (H:corestep (CLC_memsem ge) c m c' m'),
      exists T : list mem_event, cl_evstep ge c m T c' m'.
  Proof.
    induction 1; try solve [ destruct IHcl_step as [T HT]; eexists; econstructor; eauto];
      try solve [eexists; econstructor; eauto]. 
  + apply eval_lvalueT_ax2 in H. destruct H as [T1 A1].
      apply eval_exprT_ax2 in H0. destruct H0 as [T2 A2].
      apply assign_locT_ax2 in H2. destruct H2 as [T3 A3].
      eexists; econstructor; eauto.
  + apply eval_exprT_ax2 in H; destruct H as [T H].
      eexists; econstructor; eauto.
  + apply eval_exprT_ax2 in H0. destruct H0 as [T1 K1].
      apply eval_exprTlist_ax2 in H1. destruct H1 as [T2 K2].
      eexists; econstructor; eauto.
  + apply eval_exprTlist_ax2 in H0 as [??].
      eexists; econstructor; eauto.
      apply andb_true_iff in H as []; auto.
  + apply eval_exprT_ax2 in H; destruct H as [T H].
      eexists; econstructor; eauto.
  + apply eval_exprT_ax2 in H; destruct H as [T H].
      eexists; econstructor; eauto.
  + apply eval_exprT_ax2 in H; destruct H as [T H].
      eexists; econstructor; eauto.
  + inv H. apply alloc_variablesT_ax2 in H3. destruct H3 as [T3 K3].
      eexists; econstructor; eauto.
  + apply andb_true_iff in H as []; eexists; econstructor; eauto.
Unshelve.
3, 6: eassumption.
apply andb_true_iff in H as []; auto.
auto.
Qed.

  Lemma CLC_evstep_fun ge : forall c m T' c' m' T'' c'' m''
                                   (K: cl_evstep ge c m T' c' m') (K': cl_evstep ge c m T'' c'' m''), T' = T''.
  Proof. intros. generalize dependent m''. generalize dependent c''. generalize dependent T''.
         induction K; simpl; intros; try solve [ inv K'; eauto ].
 - inv K'. exploit eval_exprT_fun. apply H14. apply H0. intros X; inv X.
    exploit eval_lvalueT_fun. apply H13. apply H. intros X; inv X.
    rewrite H15 in H1; inv H1.
    exploit assign_locT_fun. apply H16. apply H2. intros X; inv X; trivial.
   destruct H12; discriminate.
   destruct H12; discriminate.
 - inv K'. exploit eval_exprT_fun. apply H10. apply H. intros X; inv X. trivial.
    destruct H9; discriminate.
    destruct H9; discriminate.
 - inv K'.
    + rewrite H15 in H; inv H.
      exploit eval_exprT_fun. eassumption. apply H0. intros X; inv X.
      exploit eval_exprTlist_fun. eassumption. apply H1. intros X; inv X.
      rewrite H18 in H2; inv H2.
      rewrite H19 in H3; inv H3. auto.
    + destruct H13; discriminate.
    + destruct H13; discriminate.
 - inv K'.
   + exploit (eval_exprTlist_fun _ _ _ _ _ _ _ _ H0); try eassumption; intros X; inv X.
    exploit ef_deterministic_fun; [eassumption | apply EFC | eassumption|].
   intros X; inv X. f_equal; f_equal; f_equal; apply proof_irr.
   + destruct H10; discriminate.
   + destruct H10; discriminate.
 - inv K'; auto. contradiction.
 - inv K'. exploit eval_exprT_fun. eassumption. eapply H. intros X; inv X. auto.
    destruct H10; discriminate.
    destruct H10; discriminate.
 - destruct H; subst x; inv K'; auto. contradiction.
 - inv K'; auto; contradiction.
 - inv K'; try solve [destruct H9; discriminate]. inversion2 H H8. auto.
 - inv K'; try solve [destruct H11; discriminate].
    exploit eval_exprT_fun. eassumption. eapply H. intros X; inv X. auto.
 - inv K'; try contradiction. auto.
 - inv K'; try solve [destruct H10; discriminate].
    exploit eval_exprT_fun. eassumption. eapply H. intros X; inv X. auto.
 - destruct H; subst x; inv K'; auto. contradiction.
 - inv K'. 
      exploit alloc_variablesT_fun. eassumption. apply H1. intros X; inv X. auto.
 - inv K'. exploit ef_deterministic_fun; [eassumption | apply EC | eassumption|].
   intros X; inv X. f_equal; f_equal; apply proof_irr.
Qed.

  Lemma CLC_evstep_elim ge : forall c m T c' m' (K: cl_evstep ge c m T c' m'),
        ev_elim m T m'.
  Proof.
    induction 1; try solve [constructor];
      try solve [ apply eval_exprT_elim in H; trivial]; trivial.
  + eapply assign_locT_elim in H2. destruct H2 as [EV3 _ ].
      eapply eval_lvalueT_elim in H.
      eapply eval_exprT_elim in H0.
      eapply ev_elim_app; eauto. eapply ev_elim_app; eauto.
  + apply eval_exprT_elim in H0.
      apply eval_exprTlist_elim in H1.
      eapply ev_elim_app; eauto.
  + apply eval_exprTlist_elim in H0.
      eapply ev_elim_app; eauto.
      apply proj2_sig.
  + eexists; split; eauto. reflexivity.
  + apply eval_exprT_elim in H.
      eapply ev_elim_app; eauto.
      eexists; split; eauto. reflexivity.
  + eexists; split; eauto. reflexivity.
  + apply alloc_variablesT_elim in H1.
      destruct H1; auto.
  + destruct  (inline_external_call_mem_events ef ge vargs m t
         vres m' EFI EC). simpl in H. subst x. auto.
  Qed.

  Program Definition CLC_evsem ge : @EvSem C := {| msem := CLC_memsem ge; ev_step := cl_evstep ge |}.
  Next Obligation. apply CLC_evstep_ax1. Qed.
  Next Obligation. apply CLC_evstep_ax2. Qed.
(*  Next Obligation. apply CLC_evstep_fun. Qed. *)
  Next Obligation. apply CLC_evstep_elim. Qed.

  Lemma CLC_msem : forall ge, msem (CLC_evsem ge) = CLC_memsem ge.
  Proof. auto. Qed.
End CLC_SEM.

  Lemma at_external_SEM_eq:
     forall ge c m, semantics.at_external (CLC_evsem ge) c m =
     match c with
     | Callstate (External ef _ _ _) args _ => 
         if ef_inline ef then None else Some (ef, args)
     | _ => None
   end.
  Proof. auto. Qed.

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
    rewrite !Int64.unsigned_repr in * by (unfold Int64.max_unsigned; lia); auto.
  - assert (Int.unsigned (Ptrofs.to_int o1) = Int.unsigned (Ptrofs.to_int o2)) by congruence.
    unfold Ptrofs.to_int in *.
    rewrite Ptrofs.modulus_eq32 in * by auto.
    rewrite !Int.unsigned_repr in * by (unfold Int.max_unsigned; lia); auto.
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

Require Import VST.veric.mem_lessdef.
Require Import VST.veric.Clight_mem_lessdef.

Transparent Mem.storebytes.

Lemma storebytes_sub:
  forall m1 m2 b ofs bytes m1',
  mem_sub m1 m2 ->
  Mem.storebytes m1 b ofs bytes = Some m1' ->
  exists m2',
     Mem.storebytes m2 b ofs bytes = Some m2'
  /\ mem_sub m1' m2'.
Proof.
  unfold Mem.storebytes; intros.
  destruct H as (? & ? & ?).
  if_tac in H0; inv H0.
  rewrite if_true by (intros ??; auto).
  do 2 eexists; eauto.
  split; auto; simpl.
  rewrite H; auto.
Qed.

Transparent Mem.alloc.

Lemma alloc_sub:
  forall (m1 m2 : mem) (lo hi : Z) (b : block)  (m1' : Mem.mem'),
  mem_sub m1 m2 ->
  Mem.alloc m1 lo hi = (m1', b) ->
  exists m2' : Mem.mem',
    Mem.alloc m2 lo hi = (m2', b) /\ mem_sub m1' m2'.
Proof.
  intros ??????? Halloc1.
  destruct (Mem.alloc m2 lo hi) eqn: Halloc2.
  injection Halloc1; injection Halloc2; intros; subst.
  destruct H as (? & ? & ?).
  do 2 eexists; eauto.
  split; [|split]; simpl; rewrite ?H, ?H0; auto.
  intros.
  pose H2 as Hperm; eapply Mem.perm_alloc_inv in Hperm; eauto.
  if_tac in Hperm.
  - eapply Mem.perm_implies, perm_F_any.
    subst; rewrite H0; eapply Mem.perm_alloc_2; eauto.
  - eapply Mem.perm_alloc_1; eauto.
Qed.

Opaque Mem.alloc.

Transparent Mem.free.

Lemma free_sub:
  forall (m1 m2 : mem) b lo hi (m1' : Mem.mem'),
  mem_sub m1 m2 ->
  Mem.free m1 b lo hi = Some m1' ->
  exists m2' : Mem.mem',
    Mem.free m2 b lo hi = Some m2' /\ mem_sub m1' m2'.
Proof.
  intros ??????? Hfree1.
  destruct H as (? & ? & ?).
  pose proof Hfree1 as Hfree; unfold Mem.free in Hfree |- *.
  if_tac in Hfree; inv Hfree.
  rewrite if_true by (intros ??; auto).
  do 2 eexists; eauto.
  split; auto; split; auto; intros.
  pose proof (Mem.perm_free_3 _ _ _ _ _ Hfree1 _ _ _ _ H3) as Hperm.
  apply H1 in Hperm.
  eapply Mem.perm_free_inv in Hperm; [|unfold Mem.free; rewrite if_true by (intros ??; eauto); eauto].
  destruct Hperm as [[] | ?]; auto; subst.
  exfalso; eapply Mem.perm_free_2; eauto.
Qed.

Opaque Mem.free.

Lemma free_list_sub:
  forall l (m1 m2 : mem) (m1' : Mem.mem'),
  mem_sub m1 m2 ->
  Mem.free_list m1 l = Some m1' ->
  exists m2' : Mem.mem',
    Mem.free_list m2 l = Some m2' /\ mem_sub m1' m2'.
Proof.
  induction l; simpl; intros.
  { inv H0; eauto. }
  destruct a as ((?, ?), ?).
  destruct (Mem.free m1 _ _ _) eqn: Hfree; inv H0.
  eapply free_sub in Hfree as (? & -> & ?); eauto.
Qed.

Lemma ev_elim_sub : forall T m m' m1, ev_elim m T m' -> mem_sub m m1 ->
  exists m1', mem_sub m' m1' /\ ev_elim m1 T m1'.
Proof.
  induction T; simpl; intros; subst; eauto.
  destruct a.
  - destruct H as (? & ? & ?).
    eapply storebytes_sub in H as (? & ? & Hsub'); eauto.
    eapply IHT in Hsub' as (? & ? & ?); eauto.
  - destruct H.
    eapply mem_sub_loadbytes in H; eauto.
    eapply IHT in H0 as (? & ? & ?); eauto.
  - destruct H as (? & ? & ?).
    eapply alloc_sub in H as (? & ? & Hsub'); eauto.
    eapply IHT in Hsub' as (? & ? & ?); eauto.
  - destruct H as (? & ? & ?).
    eapply free_list_sub in H as (? & ? & Hsub'); eauto.
    eapply IHT in Hsub' as (? & ? & ?); eauto.
Qed.

Lemma assign_locT_sub: forall ce ty m b ofs bf v m' T m1, assign_locT ce ty m b ofs bf v m' T ->
  mem_sub m m1 -> exists m1', mem_sub m' m1' /\ assign_locT ce ty m1 b ofs bf v m1' T.
Proof.
  inversion 1; subst; intros.
  - exploit Mem.store_valid_access_3; eauto; intros [].
    eapply Mem.store_storebytes, storebytes_sub in H1 as (? & ? & ?); eauto.
    do 2 eexists; eauto; constructor; auto.
    apply Mem.storebytes_store; auto.
  - eapply mem_sub_loadbytes in H4; eauto.
    eapply storebytes_sub in H5 as (? & ? & ?); eauto.
    do 2 eexists; eauto; constructor; auto.
  - inv H0.
    eapply mem_sub_loadbytes in H7; eauto.
    eapply Mem.store_storebytes, storebytes_sub in H9 as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; constructor; eauto.
    apply Mem.storebytes_store; eauto.
Qed.

Lemma eval_exprT_sub: forall ge e le m a v T m1, eval_exprT ge e le m a v T -> mem_sub m m1 -> eval_exprT ge e le m1 a v T
with eval_lvalueT_sub: forall ge e le m a b z bf T m1, eval_lvalueT ge e le m a b z bf T -> mem_sub m m1 -> eval_lvalueT ge e le m1 a b z bf T.
Proof.
  + intros until 1; intros Hm. induction H; try solve [econstructor; eauto].
    * econstructor; eauto.
      eapply unaryop_mem_sub; eauto.
    * econstructor; eauto.
      eapply binaryop_mem_sub; eauto.
    * econstructor; eauto.
      eapply sem_cast_mem_sub; eauto.
    * apply deref_locT_elim in H0 as [HT Hderef].
      eapply ev_elim_sub in HT as (? & ? & HT'); eauto.
      eapply Hderef in HT' as []; subst.
      econstructor; eauto.
  + intros until 1; intros Hm. induction H; try solve [econstructor; eauto].
Qed.

Lemma eval_exprTlist_sub: forall ge e le m la lt lv T m1, eval_exprTlist ge e le m la lt lv T -> mem_sub m m1 -> eval_exprTlist ge e le m1 la lt lv T.
Proof.
  induction 1; intros; econstructor; eauto.
  - eapply eval_exprT_sub; eauto.
  - eapply sem_cast_mem_sub; eauto.
Qed.

(* a variant of the commented-out property in sepcomp/event_semantics.v *)
Lemma cl_evstep_extends : forall ge c m T c' m' m1
  (Hext : forall ef se lv m t v m' (EFI : ef_inline ef = true) m1 (EFC : Events.external_call ef se lv m t v m'),
     mem_sub m m1 -> exists m1' (EFC1 : Events.external_call ef se lv m1 t v m1'), mem_sub m' m1' /\
     proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC1) = proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC)), cl_evstep ge c m T c' m' ->
  mem_sub m m1 -> exists m1', cl_evstep ge c m1 T c' m1' /\ mem_sub m' m1'.
Proof.
  intros until 2.
  revert m1; induction H; intros;
    repeat match goal with
    | H : eval_exprT _ _ _ m _ _ _ |- _ => eapply eval_exprT_sub in H; eauto
    | H : eval_lvalueT _ _ _ m _ _ _ _ _ |- _ => eapply eval_lvalueT_sub in H; eauto
    | H : sem_cast _ _ _ m = _ |- _ => eapply sem_cast_mem_sub in H; eauto
    | H : eval_exprTlist _ _ _ m _ _ _ _ |- _ => eapply eval_exprTlist_sub in H; eauto
    end; try solve [do 2 eexists; [econstructor; eauto|]; eauto].
  - eapply assign_locT_sub in H2 as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; eauto.
  - (* CompCert requires external calls to preserve extensions and injections.
       They likely also preserve mem_sub. *)
    edestruct Hext as (? & EFC1 & ? & Heq); eauto.
    rewrite <- Heq.
    do 2 eexists; eauto; eapply evstep_builtin; eauto.
  - assert (bool_val v1 (typeof a) m1 = Some b).
    { unfold bool_val in *.
      destruct (classify_bool _); auto.
      destruct v1; auto.
      destruct (negb Archi.ptr64); try discriminate; destruct (Mem.weak_valid_pointer m _ _) eqn: Hweak; inv H0;
        erewrite mem_sub_weak_valid_pointer; eauto. }
    do 2 eexists; eauto; econstructor; eauto.
  - eapply free_list_sub in H as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; eauto.
  - eapply free_list_sub in H1 as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; eauto.
  - eapply free_list_sub in H0 as (? & ? & ?); eauto.
    do 2 eexists; eauto; econstructor; eauto.
  - apply alloc_variablesT_elim in H1 as [Helim Hm1].
    eapply ev_elim_sub in Helim as (? & ? & Helim'); eauto.
    apply Hm1 in Helim'.
    do 2 eexists; eauto; econstructor; eauto.
  - edestruct Hext as (? & EFC1 & ? & Heq); eauto.
    rewrite <- Heq in H.
    do 2 eexists; eauto; econstructor; eauto.
Qed.
