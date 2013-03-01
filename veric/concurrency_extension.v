Load loadpath.
Require Import msl.ageable msl.rmaps. 
Require Import veric.base sepcomp.sim sepcomp.step_lemmas veric.juicy_extspec
               sepcomp.extspec sepcomp.extensions veric.juicy_mem veric.compcert_rmaps 
               veric.states veric.initial_world veric.res_predicates.
Require Import veristar.tactics veristar.basic.
Import juicy_mem.

(* system call table; Tint is the most general Int/Ptr type used in
 the CompCert languages *)

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 
Notation FORK := 
  (EF_external 2%positive 
  (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation READ := 
  (EF_external 3%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation LOCK := 
  (EF_external 7%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation UNLOCK := 
  (EF_external 8%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

(* special-purpose CompCert memory operations:
   1. rawload: load w/o valid_access check, for checking lock status
   2. rawstore: store w/o valid_access check, for updating lock status
   3. upd_perms: inject a new permission map into the memory; requires proofs 
   of access_max and nextblock_noaccess. *)

Definition rawload (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) :=
 decode_val chunk
   (Mem.getN (size_chunk_nat chunk) ofs (ZMap.get b (mem_contents m))).

Definition rawstore (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val) :=
  {| Mem.mem_contents := ZMap.set b
                            (Mem.setN (encode_val chunk v) ofs
                              (ZMap.get b (mem_contents m))) 
                            (mem_contents m);
     Mem.mem_access := mem_access m;
     Mem.nextblock := nextblock m;
     Mem.nextblock_pos := Mem.nextblock_pos m;
     Mem.access_max := Mem.access_max m;
     Mem.nextblock_noaccess := nextblock_noaccess m |}.

Local Open Scope Z_scope.

Definition pmap := ZMap.t (Z -> perm_kind -> option permission).

Definition init_pmap: pmap := ZMap.init (fun ofs k => None).

Section upd_perms.
Variables (m: mem) (pm: pmap)
          (access_max_pf : forall (b: block) (ofs: Z),
            Mem.perm_order'' (ZMap.get b pm ofs Max) (ZMap.get b pm ofs Cur))
          (nextblock_noaccess_pf : forall (b: block) (ofs: Z) (k: perm_kind),
            b <= 0 \/ b >= nextblock m -> ZMap.get b pm ofs k = None).

Definition upd_perms :=
  {| Mem.mem_contents := mem_contents m;
     Mem.mem_access := pm;
     Mem.nextblock := nextblock m;
     Mem.nextblock_pos := Mem.nextblock_pos m;
     Mem.access_max := access_max_pf;
     Mem.nextblock_noaccess := nextblock_noaccess_pf |}.

End upd_perms.          

Section ConcurrencyExtension.
Variables (cT: Type) 
  (csem: CoreSemantics genv cT juicy_mem jm_init_package).

Notation corestep := csem.(corestep).
Notation at_external := csem.(at_external).
Notation after_external := csem.(after_external).
Notation mk_init_core := csem.(make_initial_core).

(* juicy threads comprise:
   1. an rmap, describing this thread's access to the global memory
   2. a concurrent control, which is either "Krun q", indicating the
   thread is not blocked, or "Klock b ofs q", indicating the thread is
   blocked waiting on a lock at address (b, ofs) *)

Inductive ccontrol : Type :=
| Krun : cT -> ccontrol
| Klock : block -> Z -> cT -> ccontrol.

Definition thread := (rmap * ccontrol)%type.
Definition thread_tbl := FinMap.t nat thread.

(* the lock pool is a finite partial map from the addresses of
   unlocked locks to rmaps. *)

Definition lock_pool := FinMap.t (block * Z) rmap.

Definition isLK (res: resource) := 
  exists rsh, exists psh, exists z, exists pp, res=YES rsh psh (LK z) pp.
Definition isFUN (res: resource) := exists fsig, exists pp, res=PURE (FUN fsig) pp.

(* we don't require "access_cohere m phi" since an appropriate permission map
   matching phi will be injected into the memory before each corestep *)

Definition consistent (phi: rmap) (m: mem) := 
  contents_cohere m phi /\ (*access_cohere m phi /\*) 
  max_access_cohere m phi /\ 
  alloc_cohere m phi.

Definition consistent' (phi: rmap) (m: mem) := 
  contents_cohere m phi /\ access_cohere m phi /\
  max_access_cohere m phi /\ 
  alloc_cohere m phi.

(* thread_tbl_ok: global thread noninterference invariant *)
  
Definition thread_tbl_ok (tm: thread_tbl) (lp: lock_pool) (m: mem) :=
  forall phi (k: ccontrol) (i: nat), FinMap.get tm i = Some (phi, k) -> 
    (*1- threads are only ever waiting on locks *)
    (match k with Klock b ofs q => isLK (phi @ (b, ofs)) | Krun q => True end) /\
    (*2- thread-local rmaps self-join*)
    (forall phi' k' j, i<>j -> FinMap.get tm j = Some (phi', k') -> joins phi phi') /\
    (*3- thread-local rmaps join w/ the lock pool*)
    (forall phi' adr, FinMap.get lp adr = Some phi' -> joins phi phi') /\
    (*4- each thread-local rmap is consistent with the global memory*)
    consistent phi m.

Definition lock_pool_ok (lp: lock_pool) (m: mem) :=
  forall (adr: adr) (phi: rmap), FinMap.get lp adr = Some phi -> 
    (*1- every rmap in the lock pool is consistent with the global memory *)
    consistent phi m /\ 
    (*2- rmaps in the lock pool self-join *)
    (forall adr' phi', FinMap.get lp adr' = Some phi' -> 
      if eq_dec adr adr' then True else joins phi phi').

Definition locks_ok (lp: lock_pool) (tm: thread_tbl) (m: mem) :=
  forall i b ofs phi k, FinMap.get tm i = Some (phi, k) -> 
    isLK (phi @ (b, ofs)) -> Mem.load Mint32 m b ofs = Some (Vint Int.one) -> 
    exists phi', exists rsh, exists psh, exists R, 
      FinMap.get lp (b, ofs) = Some phi' /\ 
      phi @ (b, ofs) = YES rsh psh (LK 1) (SomeP ((unit:Type)::nil) (fun _ => R)) /\
      precise R /\ 
      app_pred R phi'.

Definition schedule := list nat.

(*Definition sched_ok (sched: schedule) (tm: thread_tbl) :=
  (*1- schedule is long enough *)
  (forall i phi k, 
    FinMap.get tm i = Some (phi, k) -> 
    (level phi < length sched)%nat) /\
  (*2- scheduled threads are in the thread table *)
  (forall i sched', 
    sched = i :: sched' -> 
    exists phi, exists k, FinMap.get tm i = Some (phi, k)).*)

(* worlds: 
   1: thread table is consistent w/ the lock pool
   2: lock pools self-joins; lock maps are consistent with the memory
   3: lock resource invariants are well-formed *)

Inductive world: Type := 
  mk_world: forall (sched: schedule) (tm: thread_tbl) (lp: lock_pool) (m: mem)
    (Wthread_tbl: thread_tbl_ok tm lp m)
    (Wlock_pool: lock_pool_ok lp m)
    (Wlocks_wf: locks_ok lp tm m),
    world.

Section selectors.
Variable (w: world).
Definition w_sched := match w with mk_world sched _ _ _ _ _ _ => sched end.
Definition w_tm := match w with mk_world _ tm _ _ _ _ _ => tm end.
Definition w_lp := match w with mk_world _ _ lp _ _ _ _ => lp end.
Definition w_dry := match w with mk_world _ _ _ m _ _ _ => m end.
Hint Unfold w_sched w_tm w_lp w_dry : world.
Lemma w_thread_tbl_ok : thread_tbl_ok w_tm w_lp w_dry. autounfold with world; case w; auto. Qed.
Lemma w_lock_pool_ok : lock_pool_ok w_lp w_dry. autounfold with world; case w; auto. Qed.
Lemma w_locks_ok : locks_ok w_lp w_tm w_dry. autounfold with world; case w; auto. Qed.
End selectors.

Lemma world_exists sched tm lp m : 
  thread_tbl_ok tm lp m -> 
  lock_pool_ok lp m -> 
  locks_ok lp tm m -> 
  exists w, 
    w_sched w = sched /\ w_tm w = tm /\ w_lp w = lp /\ w_dry w = m.
Proof.
intros H1 H2 H3.
exists (mk_world sched _ _ _ H1 H2 H3).
split; auto.
Qed.

Definition age_lock_pool (n: nat) (lp: lock_pool) := FinMap.ageN_map n lp.

Implicit Arguments mkAgeable [A].

Program Instance ageable_fst (A B : Type) `{H: ageable A} : ageable (A * B) := 
  mkAgeable (fun ab => let (a, b) := ab in level a)
            (fun ab => let (a, b) := ab in obnd (fun a0 => Some (a0, b)) (age1 a))
            _.
Next Obligation.
intros; case H; introv; constructor; unfold ageable.age1, ageable.level.
generalize (af_unage age_facts). 
introv H3.
intros [a1 b1]. 
spec H3 a1. 
destruct H3 as [a0 H3].
exists (a0, b1).
rewrite H3; auto.
intros [a b]; generalize (af_level1 age_facts); introv H1.
case_eq (age1 a); simpl; introv H3.
split; introv H4; [done0|done(rewrite <-H1 in H4)].
split; introv H4; [done(rewrite H1 in H3)|done0].
intros [a1 b1][a2 b2]; case_eq (age1 a1); [simpl; introv H1 H2|done0].
done(gen H2 H1; tinv0; apply (af_level2 age_facts)).
Qed.

Definition age_thread_tbl (n: nat) (tm: thread_tbl) := FinMap.ageN_map n tm.

Definition wringout_rmap_aux (phi: rmap) (m: mem) (bpm: block*pmap) : block*pmap :=
  match bpm with
  | (b, pm) => 
      ((b+1)%Z, 
        ZMap.set b (fun ofs pk => 
           match pk, phi @ (b, ofs) with
           | Max, _ => ZMap.get b (mem_access m) ofs Max
           | Cur, res => perm_of_res res
           end) pm)
  end.

Fixpoint nat_iter (n:nat) {A} (f:A->A) (x:A) : A :=
  match n with
    | O => x
    | S n' => f (nat_iter n' f x)
  end.

Lemma nat_iter_succ_r n {A} (f:A->A) (x:A) :
  nat_iter (S n) f x = nat_iter n f (f x).
Proof.
induction n; simpl; auto.
simpl in IHn; rewrite IHn; auto.
Qed.

Theorem nat_iter_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
induction n; simpl; auto.
intros; rewrite IHn; auto.
Qed.

Theorem nat_iter_invariant :
  forall (n:nat) {A} (f:A -> A) (P : A -> Prop),
    (forall x, P x -> P (f x)) ->
    forall x, P x -> P (nat_iter n f x).
Proof.
induction n; simpl; auto.
intros until P; intros H; intros; apply H; apply IHn; auto.
Qed.

Definition wringout_rmap' (phi: rmap) (m: mem): pmap :=
  snd (nat_iter (nat_of_Z (nextblock m)) 
          (wringout_rmap_aux phi m) (0%Z, mem_access m)).

(*stupid hack to ensure block 0 remains untouched:*)
Definition wringout_rmap (phi: rmap) (m: mem): pmap :=
  ZMap.set 0%Z (fun ofs pk => ZMap.get 0%Z (mem_access m) ofs pk) 
    (wringout_rmap' phi m).

Lemma wringout_max_eq (phi: rmap) (m: mem) : forall b ofs, 
  ZMap.get b (wringout_rmap phi m) ofs Max = ZMap.get b (mem_access m) ofs Max.
Proof.
intros b ofs.
unfold wringout_rmap, wringout_rmap'.
case_eq (eq_dec b 0%Z); [intros Heq _; subst|intros Hneq _].
rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
generalize (nat_of_Z (nextblock m)) as nn.
induction nn. 
simpl; auto.
simpl.
revert IHnn.
case (nat_iter nn (wringout_rmap_aux phi m)
         (0%Z, mem_access m)). 
simpl; intros b0 p0 H1.
simpl.
case_eq (eq_dec b b0).
intros -> _.
rewrite ZMap.gss; auto.
intros H _.
rewrite ZMap.gso; auto.
Qed.

Section iter_induction.
Local Open Scope nat_scope. 

Lemma iter_induction (A: Type) (fl: A -> A) (def: A) (P: nat -> A -> Prop) (m: nat) :
  P 0 def -> 
  (forall n a, n < m -> P n a -> P (S n) (fl a)) -> 
  P m (nat_iter m fl def). 
Proof.
intros H1 H2; induction m; auto.
intros; simpl; apply H2; auto.
Qed.

End iter_induction.

Lemma wringout_aux_cur_get (phi: rmap) (m: mem) : 
  forall n,
  let res := nat_iter n (wringout_rmap_aux phi m) (0%Z, mem_access m) in
    (Z_of_nat n = fst res)%Z /\
    (forall b ofs,
      (0 < b < fst res)%Z ->
      ZMap.get b (snd res) ofs Cur = perm_of_res (phi @ (b, ofs))).
Proof.
intros n; apply iter_induction; simpl.
split; auto. 
intros; omegaContradiction.
intros; destruct H0 as [H0 H1]; split. 
unfold wringout_rmap_aux.
revert H0 H1; case a; intros b p.
simpl; intros. 
rewrite Zpos_P_of_succ_nat.
rewrite H0; auto.
intros until ofs; intros H2.
unfold wringout_rmap_aux in *.
revert H0 H1 H2; case a; intros b' p'; simpl; intros H0 H1 H2.
case_eq (eq_dec b b'); [intros Heq _; subst|intros Hneq _]. 
unfold block; rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
eapply H1; eauto.
omega.
Qed.

Lemma wringout_cur_get (phi: rmap) (m: mem) :
  forall b ofs,
    (0 < b < nextblock m)%Z -> 
    ZMap.get b (wringout_rmap phi m) ofs Cur = perm_of_res (phi @ (b, ofs)).
Proof.
intros until ofs; intros H1.
unfold wringout_rmap, wringout_rmap'.
case_eq (eq_dec b 0%Z); [intros Heq _; subst|intros Hneq _].
omegaContradiction.
rewrite ZMap.gso; auto.
generalize (wringout_aux_cur_get phi m (nat_of_Z (nextblock m))).
intros H3.
case_eq (nat_iter (nat_of_Z (nextblock m))
          (wringout_rmap_aux phi m) (0%Z, mem_access m)).
intros b' p Heq.
rewrite Heq in H3.
simpl in H3; simpl.
destruct H3 as [H3 H4].
rewrite nat_of_Z_max in H3.
generalize (Mem.nextblock_pos m); intros H5.
unfold Zmax in H3; rewrite H5 in H3; auto.
rewrite <-H3 in H4.
apply (H4 b ofs H1).
Qed.

Lemma wringout_aux_cur_get_leq0 (phi: rmap) (m: mem) : 
  forall n,
  let res := nat_iter n (wringout_rmap_aux phi m) (0%Z, mem_access m) in
    (Z_of_nat n = fst res)%Z /\ (fst res >= 0)%Z /\
    (forall b ofs,
      (b < 0)%Z ->
      ZMap.get b (snd res) ofs Cur = ZMap.get b (mem_access m) ofs Cur).
Proof.
intros n; apply iter_induction; simpl.
split; auto. split; auto. omega. 
intros; destruct H0 as [H0 H1]; split. 
unfold wringout_rmap_aux.
revert H0 H1; case a; intros b p.
simpl; intros. 
rewrite Zpos_P_of_succ_nat.
rewrite H0; auto.
unfold wringout_rmap_aux in *; split. 
revert H0 H1; case a; intros b' p'; simpl; intros H0 [H1 H2]; omega.
intros until ofs; intros H2.
revert H0 H1 H2; case a; intros b' p'; simpl; intros H0 H1 H2.
case_eq (eq_dec b b'); [intros Heq _; subst|intros Hneq _].
unfold block; rewrite ZMap.gss; auto.
destruct H1 as [H1 H3]; omegaContradiction.
rewrite ZMap.gso; auto.
eapply H1; eauto.
Qed.

Lemma wringout_cur_get_leq0 (phi: rmap) (m: mem) :
  forall b ofs,
    (b <= 0)%Z -> 
    ZMap.get b (wringout_rmap phi m) ofs Cur = ZMap.get b (mem_access m) ofs Cur.
Proof.
intros until ofs; intros H1.
unfold wringout_rmap, wringout_rmap'.
case_eq (eq_dec b 0%Z); [intros Heq _; subst|intros Hneq _].
rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
generalize (wringout_aux_cur_get_leq0 phi m (nat_of_Z (nextblock m))).
intros H3.
case_eq (nat_iter (nat_of_Z (nextblock m))
          (wringout_rmap_aux phi m) (0%Z, mem_access m)).
intros b' p Heq.
rewrite Heq in H3.
simpl in H3; simpl.
destruct H3 as [H3 H4].
rewrite nat_of_Z_max in H3.
generalize (Mem.nextblock_pos m); intros H5.
unfold Zmax in H3; rewrite H5 in H3; auto.
rewrite <-H3 in H4.
destruct H4 as [H4 H6].
assert (H1': (b < 0)%Z) by omega.
apply (H6 b ofs H1').
Qed.

Lemma wringout_aux_cur_get_nextb (phi: rmap) (m: mem) : 
  forall n,
  let res := nat_iter n (wringout_rmap_aux phi m) (0%Z, mem_access m) in
    (Z_of_nat n = fst res)%Z /\
    (forall b ofs,
      (b >= fst res)%Z ->
      ZMap.get b (snd res) ofs Cur = ZMap.get b (mem_access m) ofs Cur).
Proof.
intros n; apply iter_induction; simpl.
split; auto. 
intros; destruct H0 as [H0 H1]; split. 
unfold wringout_rmap_aux.
revert H0 H1; case a; intros b p.
simpl; intros. 
rewrite Zpos_P_of_succ_nat.
rewrite H0; auto.
unfold wringout_rmap_aux in *.
revert H0 H1; case a; intros b' p'; simpl; intros H0 H1.
intros until ofs; intros H2.
case_eq (eq_dec b b'); [intros Heq _; subst|intros Hneq _].
unfold block; rewrite ZMap.gss; auto.
omegaContradiction.
rewrite ZMap.gso; auto.
eapply H1; eauto.
omega.
Qed.

Lemma wringout_cur_get_nextb (phi: rmap) (m: mem) :
  forall b ofs,
    (b >= nextblock m)%Z -> 
    ZMap.get b (wringout_rmap phi m) ofs Cur = ZMap.get b (mem_access m) ofs Cur.
Proof.
intros until ofs; intros H1.
unfold wringout_rmap, wringout_rmap'.
case_eq (eq_dec b 0%Z); [intros Heq _; subst|intros Hneq _].
rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
generalize (wringout_aux_cur_get_nextb phi m (nat_of_Z (nextblock m))).
intros H3.
case_eq (nat_iter (nat_of_Z (nextblock m))
          (wringout_rmap_aux phi m) (0%Z, mem_access m)).
intros b' p Heq.
rewrite Heq in H3.
simpl in H3; simpl.
destruct H3 as [H3 H4].
rewrite nat_of_Z_max in H3.
generalize (Mem.nextblock_pos m); intros H5.
unfold Zmax in H3; rewrite H5 in H3; auto.
rewrite <-H3 in H4.
apply (H4 b ofs H1).
Qed.

Lemma wringout_access_max phi m :
  consistent phi m ->
  forall b ofs,
    Mem.perm_order'' (ZMap.get b (wringout_rmap phi m) ofs Max) 
                     (ZMap.get b (wringout_rmap phi m) ofs Cur).
Proof.
generalize (Mem.access_max m); intros H1.
intros [_ [H2 H3]]; intros b ofs; spec H2 (b, ofs); spec H3 (b, ofs).
simpl in H2, H3.
rewrite wringout_max_eq.
case (Z_le_dec b 0); intros H4.
 rewrite wringout_cur_get_leq0; auto; omega.
assert (H5: (b > 0)%Z) by omega; clear H4.
case (Z_lt_dec b (nextblock m)); intros H6.
 rewrite wringout_cur_get; [|omega].
 revert H2.
 unfold ZIndexed.t.
 unfold max_access_at; simpl.
 case (resource_at phi (@pair Z Z b ofs)); auto.
 unfold perm_of_res. unfold res_retain. unfold valshare.
 destruct k; auto; simpl. 
  admit. (*easy, by perm_order''_trans*)
  admit. (*easy*)
  admit. (*easy*)
intros ? ? ?; omegaContradiction.
assert (H7: (b >= nextblock m)%Z) by omega; clear H6.
rewrite wringout_cur_get_nextb; auto.
Qed.

Lemma wringout_nextblock_noaccess phi m :
  consistent phi m ->
  forall b ofs k,
    (b <= 0 \/ b >= nextblock m -> ZMap.get b (wringout_rmap phi m) ofs k = None)%Z.
Proof.
generalize (Mem.nextblock_noaccess m); intros H1.
intros [_ [_ H3]]; intros b ofs; spec H3 (b, ofs); simpl in H3.
intros [|]; [rewrite wringout_max_eq; auto|].
intros [H4|H4]; [rewrite wringout_cur_get_leq0; auto|].
rewrite wringout_cur_get_nextb; auto.
Qed.

Definition juicy_upd_perms (phi: rmap) (m: mem) (Hcoh: consistent phi m) := 
  upd_perms m (wringout_rmap phi m)
    (wringout_access_max phi m Hcoh) (wringout_nextblock_noaccess phi m Hcoh).            

Lemma perm_of_res_no : perm_of_res (NO Share.bot) = None.
Proof.
unfold perm_of_res; simpl.
unfold perm_of_sh; simpl.
cases_if; auto.
false; apply Share.nontrivial; auto.
cases_if; auto.
false; auto.
Qed.

Lemma perm_of_empty_inv {s t} : perm_of_sh s t = None -> s = Share.bot /\ t = Share.bot.
Proof.
unfold perm_of_sh.
cases_if; auto.
cases_if; auto.
inversion 1.
inversion 1.
cases_if; auto.
cases_if; auto.
inversion 1.
inversion 1.
Qed.

(* sequential steps even in the juicy semantics must first adjust the permission 
   levels in the CompCert memory "w_dry w" *)

Section wringout_juicy_mem.
  Variables (phi: rmap) (m: mem) (Hcoh: consistent phi m).

  Definition wrungout_mem := juicy_upd_perms phi m Hcoh.

  Lemma wringout_contents_cohere : contents_cohere wrungout_mem phi.
  Proof.
    gen Hcoh; intros [H1 [H2 H3]].
    unfold contents_cohere in H1 |- *.
    intros until pp; intros H4.
    unfold wrungout_mem, juicy_upd_perms, upd_perms, contents_at; simpl.
    unfold contents_at in H1.
    eapply H1; eauto.
  Qed.

  Lemma wringout_access_cohere : access_cohere wrungout_mem phi.
  Proof.
    gen Hcoh; intros [H1 [H2 H3]].
    unfold access_cohere in H2 |- *.
    unfold wrungout_mem, juicy_upd_perms, upd_perms, access_at; simpl; intros (b, ofs).
    case_eq (Z_le_dec b 0); [intros Hle _|intros Hgt _].
     rewrite wringout_cur_get_leq0; auto; simpl.
     generalize (Mem.nextblock_noaccess m); intros H4.
     unfold max_access_cohere in H2; generalize (H2 (b, ofs)).
     case (phi @ (b, ofs)); simpl; auto.
       unfold max_access_at; rewrite H4; auto.
       intros t H5; assert (t = Share.bot) as ->.
         clear - H5; gen H5; unfold Mem.perm_order''.
         case_eq (perm_of_sh t Share.bot). inversion 2. 
         done(intros H1; destruct (perm_of_empty_inv H1)).
        rewrite H4, perm_of_res_no; auto.
       unfold max_access_at; rewrite H4; auto.
       done(intros until p0; destruct (perm_of_sh_pshare t p) as [p' ->]; inversion 1).
     unfold perm_of_res; simpl; intros.
     done(rewrite H4, perm_of_empty; auto).
    case_eq (Z_ge_dec b (nextblock m)); [intros Hge _|intros Hlt _].
     rewrite wringout_cur_get_nextb; auto; simpl.
     generalize (Mem.nextblock_noaccess m); intros H4.
     rewrite H4; auto.
     unfold alloc_cohere in H3.
     rewrite H3; auto.
     done(rewrite perm_of_res_no).
     assert (0 < b < nextblock m)%Z by omega.
     done(simpl; apply wringout_cur_get).
  Qed.
     
  Lemma wringout_max_access_cohere : max_access_cohere wrungout_mem phi.
  Proof.
    gen Hcoh; intros [H1 [H2 H3]].
    unfold max_access_cohere in H2 |- *.
    intros (b, ofs); spec H2 (b, ofs); gen H2.
    unfold max_access_at; simpl.
    done(rewrite wringout_max_eq).
  Qed.

  Lemma wringout_alloc_cohere : alloc_cohere wrungout_mem phi.
  Proof. gen Hcoh; intros [H1 [H2 H3]]; auto. Qed.    

  Lemma mk_juicy_mem : {jm: juicy_mem | wrungout_mem=m_dry jm /\ phi=m_phi jm}.
  Proof.
    exists (mkJuicyMem _ _ wringout_contents_cohere wringout_access_cohere 
                           wringout_max_access_cohere wringout_alloc_cohere); auto.
  Qed.

End wringout_juicy_mem.
Implicit Arguments mk_juicy_mem [m phi].

(* lift the mem_forward and allowed_core_modification properties to juicy_memories *)

Definition allowed_freewrite (jm1 jm2 : juicy_mem) :=
  forall b ofs v, 
    m_phi jm1 @ (b, ofs) = YES fullshare pfullshare (VAL v) NoneP -> 
    (m_phi jm2 @ (b, ofs) = NO Share.bot (*free*) \/
     exists v', m_phi jm2 @ (b, ofs) = YES fullshare pfullshare (VAL v') NoneP).

Definition allowed_alloc (jm1 jm2 : juicy_mem) :=
  forall (b: block) ofs rsh psh v, 
    m_phi jm1 @ (b, ofs) = NO Share.bot -> 
    m_phi jm2 @ (b, ofs) = YES rsh psh (VAL v) NoneP -> 
    (b >= nextblock (m_dry jm1))%Z.

Definition nonvals_unchanged (jm1 jm2 : juicy_mem) :=
  forall (b: block) ofs rsh psh k pp, 
        m_phi jm1 @ (b, ofs) = YES rsh psh k pp -> 
        ~isVAL k -> 
        m_phi jm1 @ (b, ofs) = m_phi jm2 @ (b, ofs).

Definition allowed_juicy_modification (jm1 jm2 : juicy_mem) :=
  mem_forward (m_dry jm1) (m_dry jm2) /\
  allowed_core_modification (m_dry jm1) (m_dry jm2) /\
  allowed_freewrite jm1 jm2 /\
  allowed_alloc jm1 jm2 /\
  nonvals_unchanged jm1 jm2.

(* noninterference lemmas *)

Lemma consistent_corestep_lem ge phi c jm c' jm' :
  consistent phi (m_dry jm) -> corestep ge c jm c' jm' -> 
  consistent phi (m_dry jm').
(*should be true (corestep respects read permissions, nonval kinds, only 
   allocates at or above nextblock), but very tedious*)
Admitted.

Lemma joins_corestep_lem {ge phi phi' c jm c' jm'} : 
  joins phi (m_phi jm) -> corestep ge c jm c' jm' -> age1 phi = Some phi' -> 
  joins phi' (m_phi jm').
Admitted. 

Lemma kind_at_age_eq (phi phi' : rmap) k n adr :
  kind_at k adr phi -> ageN n phi = Some phi' -> 
  kind_at k adr phi'.
Proof.
revert phi; induction n.
done(intros phi H1; unfold ageN; simpl; tinv0).
intros phi H1; unfold ageN; simpl.
case_eq (age1 phi); [|done0]; intros phi2 H2 H3.
apply age1_res_option with (loc := adr) in H2. 
destruct H1 as [rsh [psh [pp H1]]]; rewrite H1 in H2; simpl in H2.
apply IHn with (phi := phi2); auto.
revert H2; case_eq (phi2 @ adr); [done0|introv H4 H5|introv H4 H5].
done(simpl in H5; inversion H5; subst; repeat eexists; eauto).
done(simpl in H5; inversion H5).
Qed.

Lemma ageN_first {A B} {Hag: ageable A} {x x'} {y y': B} : 
  @ageN (A * B) (ageable_fst A B) 1 (x, y) = Some (x', y') -> 
  ageN 1 x = Some x' /\ y=y'.
done(unfold ageN; case_eq (age1 x); simpl; introv ->; simpl; [tinv0|done0]). 
Qed.

Lemma ccontrol_age i tm tm' phi phi' k k' :
  FinMap.get tm i = Some (phi, k) -> 
  age_thread_tbl 1 tm = Some tm' -> 
  FinMap.get tm' i = Some (phi', k') -> 
  ageN 1 phi = Some phi' /\ k = k'.
Proof.
introv H1 H2 H3; destruct (FinMap.ageNug _ _ _ H2 H3) as [[x y] [H4 H5]].
unfold thread in H4; rewrite H4 in H1; gen H1; tinv0.
done(apply ageN_first in H5).
Qed.

Lemma isLK_age {phi phi' b ofs} : 
  isLK (phi @ (b, ofs)) -> age1 phi = Some phi' -> 
  isLK (phi' @ (b, ofs)).
Proof.
intros [rsh [psh [z [H1 H2]]]] H3.
cut (kind_at (LK z) (b, ofs) phi').
done(introv [rsh' [psh' [z' H4]]]; do 3 eexists; eauto).
cut (kind_at (LK z) (b, ofs) phi). introv H4.
rewrite <-ageN1 in H3. 
apply (kind_at_age_eq _ _ _ _ _ H4 H3).
done(do 3 eexists; eauto).
Qed.

Lemma thread_tbl_ok_after_corestep 
  ge (w: world) i phi c (Hcoh: consistent phi (w_dry w)) c' jm' tm0 tm' lp' : 
  FinMap.get (w_tm w) i = Some (phi, Krun c) -> 
  corestep ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' -> 
  age_thread_tbl 1 (w_tm w) = Some tm0 ->
  tm' = FinMap.set i (m_phi jm', Krun c') tm0 -> 
  age_lock_pool 1 (w_lp w) = Some lp' -> 
  thread_tbl_ok tm' lp' (m_dry jm').
Proof.
intros H1 H2 H3 H3' H4. split. 
(*threads still waiting on locks after corestep*)
case_eq (eq_nat_dec i i0); introv _; [subst i|]. 
case_eq k; [done0|].
cut (exists c2, k = Krun c2); [done(intros [c2 ->])|].
done(rewrite H3', FinMap.gss in H; gen H; tinv0; eexists).
case_eq k; [done0|].
introv H5; rewrite H3', FinMap.gso in H; auto.
rewrite H5 in H; destruct (FinMap.ageNug _ _ _ H3 H) as [x [H6 H7]].
gen H6 H7; case x; introv H6 H7; destruct (ageN_first H7) as [H9 H10].
cut (isLK (r @ (b, z))); [intro H11|].
done(rewrite ageN1 in H9; apply (isLK_age H11 H9)).
edestruct (w_thread_tbl_ok w); gen H6; eauto.
done(rewrite H10; introv H11 H12 _).
(*thread_tbl case*)
case_eq (eq_nat_dec i i0); introv _. subst i.
(*i = i0*)
split; [introv H5 H6|split; [introv H5|]].
unfold age_thread_tbl in H3. 
rewrite H3', FinMap.gso in H6; auto.
destruct (FinMap.ageNug _ _ _ H3 H6) as [[x y] [H8 H9]].
rewrite H3', FinMap.gss in H; gen H; tinv0.
apply ageN_first in H9; destruct H9 as [H9 H10]; subst y; rewrite ageN1 in H9.
apply joins_comm; eapply joins_corestep_lem; eauto.
destruct (proj2_sig (mk_juicy_mem Hcoh)) as [H10 <-].
generalize (w_thread_tbl_ok w); intros H11.
spec H11 phi (Krun c) i0 H1; destruct H11 as [_ [H11 [H12 H13]]].
done(spec H11 x k' j H5 H8; apply joins_comm).
(*lock pool*)
unfold age_lock_pool in H4. 
destruct (FinMap.ageNug _ _ _ H4 H5) as [x [H8 H9]].
rewrite H3', FinMap.gss in H; gen H; tinv0.
rewrite ageN1 in H9; apply joins_comm; eapply joins_corestep_lem; eauto.
destruct (proj2_sig (mk_juicy_mem Hcoh)) as [H10 <-].
generalize (w_thread_tbl_ok w); intros H11.
spec H11 phi (Krun c) i0 H1; destruct H11 as [_ [H11 [H12 H13]]].
done(spec H12 x adr H8; apply joins_comm).
(*consistent*)
admit.
(*i <> i0*)
admit.
Qed.

Lemma can_age1_juicy_mem': forall j r,
  age (m_phi j) r -> exists j', age1 j = Some j' /\ m_phi j' = r.
Proof.
intros j r H.
unfold age in H.
case_eq (age1_juicy_mem j); intros.
destruct (age1_juicy_mem_unpack _ _ H0).
unfold seplog.ag_rmap in H.
unfold age in H1; rewrite H in H1; inversion H1; subst.
eexists; eauto.
apply age1_juicy_mem_None1 in H0.
unfold seplog.ag_rmap in H.
rewrite H0 in H.
elimtype False; inversion H.
Qed.

Lemma c'c {phi m} : consistent' phi m -> consistent phi m.
Proof.
intros [H1 [H2 [H3 H4]]]; split; auto.
Qed.

Lemma consistent'_mem_unchanged {m phi} (Hcoh: consistent' phi m) :
  m_dry (proj1_sig (mk_juicy_mem (c'c Hcoh))) = m.  
Proof.
case (mk_juicy_mem (c'c Hcoh)); simpl.
intros jm [<- H1].
Admitted. (*TODO: should be easy but tedious*)

Lemma rmaps_consistent'_after_ageN n phi phi' m : 
  consistent' phi m -> ageN n phi = Some phi' -> consistent' phi' m.
Proof.
intros H1 H2; generalize (mk_juicy_mem (c'c H1)); intros [j1 [H3 H4]]. 
assert (wrungout_mem phi m (c'c H1) = m).
  generalize (consistent'_mem_unchanged H1).
  case (mk_juicy_mem (c'c H1)); simpl.
  done(intros jm [-> _]).
rewrite H in *; clear H.
revert j1 phi H1 H2 H3 H4; induction n; intros j1 phi H1 H2 H3 H4.
unfold ageN in H2; simpl in H2; inversion H2; subst.
done(rewrite H0 in H1).
unfold ageN in H2; simpl in H2; revert H2.
case_eq (age1 phi); [|done0]; intros r H5 H6.
rewrite H4 in H5. 
generalize (can_age1_juicy_mem' j1 _ H5); intros [j2 [H7 Heq]].
generalize (age1_juicy_mem_unpack' j1 j2); intros H8; spec H8.
done(split; [rewrite Heq; auto|apply age_jm_dry; auto]).
assert (H9: m = m_dry j2) by (rewrite H3; erewrite age_jm_dry; eauto).
apply (IHn j2 r); auto.
rewrite <-Heq, H9; split.
 apply juicy_mem_contents. split. apply juicy_mem_access. 
 split. apply juicy_mem_max_access. apply juicy_mem_alloc.
Qed.

Lemma rmaps_consistent_after_ageN n phi phi' m : 
  consistent phi m -> ageN n phi = Some phi' -> consistent phi' m.
Proof. Admitted. (*TODO: relatively easy*)

Lemma mk_juicy_eq {m phi} (Hcoh: consistent phi m) :
  let m' := m_dry (proj1_sig (mk_juicy_mem Hcoh)) in
    Mem.mem_contents m = Mem.mem_contents m' /\
    Mem.nextblock m = Mem.nextblock m'.
Proof.
case_eq (mk_juicy_mem Hcoh); intros jm [H1 ?]; simpl.
done(split; rewrite <-H1; unfold wrungout_mem, juicy_upd_perms).
Qed.

Lemma mk_juicy_max_access_eq {m phi} (Hcoh: consistent phi m) : forall loc,
  max_access_at m loc = max_access_at (m_dry (proj1_sig (mk_juicy_mem Hcoh))) loc.
Proof.
intros (b, ofs); unfold max_access_at; simpl.
case_eq (mk_juicy_mem Hcoh); intros jm [H1 ?] H2; simpl.
rewrite <-H1; unfold wrungout_mem, juicy_upd_perms, upd_perms; simpl.
done(rewrite wringout_max_eq).
Qed.

Lemma consistent_mk_juicy {m phi} phi' (Hcoh: consistent phi m) :
  consistent phi' m -> 
  consistent phi' (m_dry (proj1_sig (mk_juicy_mem Hcoh))).
Proof.
generalize (mk_juicy_eq Hcoh); intros [H1 H2] [H3 [H4 H5]]; split.
done(unfold contents_cohere, contents_at in *; rewrite H1 in *).
split; [unfold max_access_cohere in *; intros loc; spec H4 loc|].
done(rewrite <-mk_juicy_max_access_eq).
unfold alloc_cohere in *; intros loc H6; apply (H5 loc).
rewrite H2; auto.
Qed.

Lemma lock_rmap_consistent_after_corestep 
  ge w b ofs phi_lock phi i c c' jm' (Hcoh : consistent phi (w_dry w)) :
  (forall ge c jm c' jm', corestep ge c jm c' jm' -> allowed_juicy_modification jm jm') ->
  FinMap.get (w_lp w) (b, ofs) = Some phi_lock -> 
  FinMap.get (w_tm w) i = Some (phi, Krun c) -> 
  corestep ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' -> 
  consistent phi_lock (m_dry jm').
Proof.
introv Hcoresem_ok H1 H2 H3. 
spec Hcoresem_ok ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' H3.
destruct Hcoresem_ok as [H4 [H5 [H6 [H7 H8]]]].
generalize (w_lock_pool_ok w); intro H9.
spec H9 (b, ofs) phi_lock H1; destruct H9 as [H9 _].
eapply consistent_corestep_lem; eauto.
generalize (proj2_sig (mk_juicy_mem Hcoh)); intros [H10 H11].
apply consistent_mk_juicy; auto.
Qed.

Lemma ageN_joins_eq phi1 phi2 phi1' phi2' n : 
  joins phi1 phi2 -> ageN n phi1 = Some phi1' -> ageN n phi2 = Some phi2' -> 
  joins phi1' phi2'.
Proof.
revert phi1 phi2; induction n; unfold ageN; simpl.
done(introv H1; tinv0; tinv0).
introv H1; case_eq (age1 phi1); [|done0]; introv H2 H3; 
 case_eq (age1 phi2); [|done0]; introv H4 H5.
done(apply (IHn r r0); auto; eapply age1_joins_eq; eauto).
Qed.

Lemma lock_rmaps_join_after_aging n adr lp lp' phi phi2 :
  FinMap.get lp adr = Some phi ->  
  FinMap.ageN_map n lp = Some lp' -> 
  FinMap.get lp' adr = Some phi2 -> 
  (forall (adr' : block * Z) (phi' : rmap),
    FinMap.get lp adr' = Some phi' ->
    if eq_dec adr adr' then True else joins phi phi') -> 
   forall (adr' : block * Z) (phi' : rmap),
   FinMap.get lp' adr' = Some phi' ->
   if eq_dec adr adr' then True else joins phi2 phi'.
Proof.
introv H1 H2 H3 H4 H5; case_eq (eq_dec adr adr'); intros Heq _; [done0|].
destruct (FinMap.ageNg _ _ _ H2 H1) as [x [H6 H7]].
destruct (FinMap.ageNug _ _ _ H2 H5) as [y [H8 H9]].
rewrite H6 in H3; gen H3; tinv0.
cut (joins phi y); [done(introv H10; eapply ageN_joins_eq; eauto)|].
done(spec H4 adr' y H8; gen H4; cases_if).
Qed.

Lemma lock_pool_ok_after_corestep 
  ge (w: world) i phi c (Hcoh: consistent phi (w_dry w)) c' jm' lp' : 
  (forall ge c jm c' jm', corestep ge c jm c' jm' -> allowed_juicy_modification jm jm') ->
  FinMap.get (w_tm w) i = Some (phi, Krun c) -> 
  corestep ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' -> 
  age_lock_pool 1 (w_lp w) = Some lp' -> 
  lock_pool_ok lp' (m_dry jm').
Proof.
introv Hcoresem_ok H1 H2 H3; unfold lock_pool_ok; intros [b ofs] phi0 H4.
destruct (FinMap.ageNug _ _ _ H3 H4) as [phi00 [H5 H6]].
generalize (w_lock_pool_ok w (b, ofs) phi00 H5); intros [H7 H8].
unfold age_lock_pool in H3; split. 
eapply rmaps_consistent_after_ageN; eauto.
eapply lock_rmap_consistent_after_corestep; eauto.
eapply lock_rmaps_join_after_aging; eauto.
Qed.

Lemma locks_ok_after_corestep 
  ge (w: world) i phi c (Hcoh: consistent phi (w_dry w)) c' jm' tm0 tm' lp' : 
  FinMap.get (w_tm w) i = Some (phi, Krun c) -> 
  corestep ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' -> 
  age_thread_tbl 1 (w_tm w) = Some tm0 ->
  tm' = FinMap.set i (m_phi jm', Krun c') tm0 -> 
  age_lock_pool 1 (w_lp w) = Some lp' -> 
  locks_ok lp' tm' (m_dry jm').
Admitted.

Lemma age_thread_tbl_success {w i phi q} : 
  FinMap.get (w_tm w) i = Some (phi, q) -> 
  (level phi > 0)%nat -> 
  exists tm', age_thread_tbl 1 (w_tm w) = Some tm'.
Proof.
assert (H1: forall phi phi' phi0, age1 phi = Some phi0 -> 
 joins phi phi' -> exists phi1, age1 phi' = Some phi1). 
               introv H1 H2.
               cut (exists x, level phi' = S x); [intros [x H3]|].
               done(apply levelS_age1 in H3; eauto).
               cut (level phi0 = level phi'). intro Heq.
               apply age1_levelS in H1; destruct H1 as [n H1]. 
               done(rewrite Heq in H1; eexists; eauto).
               done(apply rmap_join_eq_level).
introv H2 H3; unfold age_thread_tbl.
apply FinMap.ageN_exists; introv H4. 
case_eq (eq_dec x i); introv _; [subst|].
(*x = i*)
done(rewrite H4 in H2; gen H2; tinv0).
(*x <> i *)
gen H4; case y; introv; tinv0; simpl.
cut (exists r', age1 r = Some r'); [introv [r' H5]|].
destruct (age1_levelS _ _ H5); omega.
cut (joins phi r). introv H6.
cut (exists phi', age1 phi = Some phi'); [introv [phi0 H5]|].
destruct (H1 phi r phi0 H5 H6) as [r0 H7].
done(exists r0).
cut (exists x, level phi = S x). introv [x0]; tinv0.
done(destruct (levelS_age1 _ _ H5) as [phi1 H8]; exists phi1).
done(gen H3; case_eq (level phi); [intros; exfalso; omega|intros; eexists; eauto]).
generalize (w_thread_tbl_ok w); intro H6.
spec H6 phi q i H2; destruct H6 as [H6 [H7 H8]].
done(apply (H7 r c x)).
Qed.

Lemma age_lock_pool_success {w i phi q} : 
  FinMap.get (w_tm w) i = Some (phi, q) -> 
  (level phi > 0)%nat -> 
  exists lp', age_lock_pool 1 (w_lp w) = Some lp'.
Admitted.

Lemma world_exists_after_corestep 
  ge {w: world} {i phi c} {Hcoh: consistent phi (w_dry w)} {c' jm' sched} : 
  (forall ge c jm c' jm', corestep ge c jm c' jm' -> allowed_juicy_modification jm jm') ->
  w_sched w = i :: sched -> 
  (level phi > 0)%nat -> 
  FinMap.get (w_tm w) i = Some (phi, Krun c) ->                                 
  corestep ge c (proj1_sig (mk_juicy_mem Hcoh)) c' jm' -> 
  exists w', exists tm0,
    w_sched w = w_sched w' /\ 
    age_thread_tbl 1 (w_tm w) = Some tm0 /\
    w_tm w' = FinMap.set i (m_phi jm', Krun c') tm0 /\  
    age_lock_pool 1 (w_lp w) = Some (w_lp w') /\
    w_dry w' = m_dry jm'.
Proof.
introv Hallowed_coremod H0 Hlev H1 H2.
assert (exists tm0, age_thread_tbl 1 (w_tm w) = Some tm0) as [tm0 H3].
 done(destruct (age_thread_tbl_success H1 Hlev); eexists; eauto).
assert (exists lp', age_lock_pool 1 (w_lp w) = Some lp') as [lp' H4].
 done(destruct (age_lock_pool_success H1 Hlev); eexists; eauto).
destruct (world_exists (w_sched w) 
           (FinMap.set i (m_phi jm', Krun c') tm0) lp' (m_dry jm')).
eapply thread_tbl_ok_after_corestep; eauto.
eapply lock_pool_ok_after_corestep; eauto.
eapply locks_ok_after_corestep; eauto.
destruct H as [H5 [H6 [H7 H8]]]; subst.
exists x; eexists; split3; eauto.
Qed.

Definition init_coremem (ge: genv) (c: cT) (d: jm_init_package): thread*mem := 
  let jm := (initial_jm (jminit_prog d) (jminit_m d) (jminit_G d) (jminit_lev d) 
            (jminit_init_mem d) (jminit_vars_no_dups d) (jminit_fdecs_match d)) in
  ((m_phi jm, Krun c), m_dry jm). 

Definition init_thread_tbl (ge: genv) (c: cT) (d: jm_init_package): thread_tbl := 
  FinMap.set 1%nat  (fst (init_coremem ge c d)) (@FinMap.empty _ _).

Definition init_lock_pool: lock_pool := (@FinMap.empty _ _).

Lemma init_thread_tbl_ok: forall ge c d, 
  thread_tbl_ok (init_thread_tbl ge c d) init_lock_pool (snd (init_coremem ge c d)).
Proof.
intros until d; unfold thread_tbl_ok.
intros until i;  intros H.
split.
destruct k; auto.
unfold init_thread_tbl in H.
case_eq (eq_nat_dec 1 i).
intros Heq _.
rewrite Heq in H.
rewrite FinMap.gss in H; auto.
unfold init_coremem in H.
simpl in H.
inversion H.
intros Hneq _.
rewrite FinMap.gso in H; auto.
Transparent FinMap.empty FinMap.get.
unfold FinMap.empty, FinMap.get in H.
congruence.
split; auto.
intros until j; intros H1 H2.
unfold init_thread_tbl in H2.
rewrite FinMap.gso in H2; auto; auto.
unfold FinMap.empty, FinMap.get in H2.
congruence.
unfold init_thread_tbl in H.
case_eq (eq_nat_dec i 1).
intros Heq _.
rewrite Heq in *.
auto.
intros Hneq _.
rewrite FinMap.gso in H; auto.
unfold FinMap.get, FinMap.empty in H. 
congruence.
split; intros.
unfold init_lock_pool in H0.
unfold FinMap.get, FinMap.empty in H0.
congruence.
unfold init_thread_tbl in H.
case_eq (eq_nat_dec i 1).
intros Heq _.
rewrite Heq in *.
rewrite FinMap.gss in H.
unfold init_coremem in H.
set (jm := 
  (initial_jm (jminit_prog d) (jminit_m d) 
    (jminit_G d) (jminit_lev d) (jminit_init_mem d)
    (jminit_vars_no_dups d) (jminit_fdecs_match d))) in *.
generalize (juicy_mem_contents jm).
generalize (juicy_mem_max_access jm).
generalize (juicy_mem_alloc jm).
unfold fst in H.
inversion H; subst.
unfold init_coremem.
simpl; intros; split3; auto.
intros Hneq _.
rewrite FinMap.gso in H; auto.
unfold FinMap.get, FinMap.empty in H; simpl in H.
congruence.
Qed.

Lemma init_lock_pool_ok: forall m, lock_pool_ok init_lock_pool m.
Proof.
unfold init_lock_pool, lock_pool_ok.
intros until phi; intros H1.
unfold FinMap.get, FinMap.empty in H1.
congruence.
Qed.

Lemma init_locks_ok: forall m ge c d, 
  locks_ok init_lock_pool (init_thread_tbl ge c d) m.
Proof.
unfold init_lock_pool, locks_ok; intros.
unfold init_thread_tbl in H.
case (eq_nat_dec i 1).
intros Heq; subst.
unfold isLK in H0.
destruct H0 as [rsh [psh [z [pp H0]]]].
rewrite FinMap.gss in H.
unfold init_coremem in H.
simpl in H.
inv H.
generalize (inflate_initial_mem_all_VALs (jminit_m d)
  (initial_core (Genv.globalenv (jminit_prog d)) 
    (jminit_G d) (jminit_lev d))); unfold all_VALs.
intros H2.
spec H2 (b, ofs).
destruct (inflate_initial_mem (jminit_m d)
           (initial_core (Genv.globalenv (jminit_prog d)) 
              (jminit_G d) (jminit_lev d)) @ (b, ofs)); try congruence.
unfold isVAL in H2.
destruct H2 as [v H2].
rewrite H2 in H0.
inv H0.
intros Hneq.
rewrite FinMap.gso in H; auto.
unfold FinMap.empty, FinMap.get in H.
congruence.
Qed.

Definition cm_make_initial_jmem (d: jm_init_package): juicy_mem :=
  initial_jm (jminit_prog d) (jminit_m d) 
    (jminit_G d) (jminit_lev d) (jminit_init_mem d)
    (jminit_vars_no_dups d) (jminit_fdecs_match d).

Definition cm_initial_mem (ge: genv) (jm: juicy_mem) (d: jm_init_package): Prop:=
  Genv.globalenv (jminit_prog d) = ge /\ jm = cm_make_initial_jmem d. 

Program Definition cm_make_initial_core 
      (sched: schedule) (d: jm_init_package) (ge: genv) (v: val) (args: list val) :=
  match make_initial_core csem ge v args with
  | None => None
  | Some c => let thread1 := (m_phi (cm_make_initial_jmem d), c) in
              Some (mk_world sched (init_thread_tbl ge c d) init_lock_pool 
                       (snd (init_coremem ge c d)) _ _ _)
  end.
Next Obligation. intros; apply init_thread_tbl_ok. Qed.
Next Obligation. intros; apply init_lock_pool_ok. Qed.
Next Obligation. intros; apply init_locks_ok. Qed.

Definition cm_at_external (w: world) := 
  match w with mk_world (i::sched) tm lp m _ _ _ => 
    match FinMap.get tm i with 
    | None => None
    | Some (phi, Klock b ofs c) => None
    | Some (phi, Krun c) => 
      if eq_nat_dec (level phi) 0%nat then None 
      else match at_external c with
           | None => None
           | Some (EXIT, sig, args) => None
           | Some (FORK, sig, args) => None
           | Some (LOCK, sig, args) => None
           | Some (UNLOCK, sig, args) => None
           | Some (ef, sig, args) => Some (ef, sig, args)
           end end
  | mk_world nil tm lp m _ _ _ => None
  end.

Program Definition cm_after_external (ret: option val) (w: world): option world :=
  match w_sched w with 
  | i::sched => 
    match FinMap.get (w_tm w) i with
    | None => None
    | Some (phi, Klock b ofs c) => None
    | Some (phi, Krun c) => 
      match after_external ret c with 
      | None => None
      | Some c' => Some (mk_world (i::sched) (FinMap.set i (phi, Krun c') (w_tm w)) 
                           (w_lp w) (w_dry w) _ _ _)
      end
    end
  | nil => None
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(* cm is safely halted when either schedule is empty or thread rmaps at level 0 *)

Definition cm_safely_halted (ge: genv) (w: world): option int := 
  match w_sched w with 
  | nil => Some Int.zero
  | i::sched => match FinMap.get (w_tm w) i with 
                | Some (phi, _) => if eq_nat_dec (level phi) 0%nat then Some Int.zero
                                   else None
                | None => None
                end
  end.

Inductive cswitch: nat -> world -> world -> Prop :=
| ctx_switch : forall i sched w w', 
  age_lock_pool 1 (w_lp w) = Some (w_lp w') -> 
  age_thread_tbl 1 (w_tm w) = Some (w_tm w') -> 
  w_sched w = i :: sched -> 
  w_sched w' = sched -> 
  w_dry w' = w_dry w -> 
  cswitch i w w'.

Definition val2ptr (v : val) : option (block * int) := 
  match v with 
  | Vptr b ofs => Some (b, ofs)
  | _ => None
  end.

Definition val2int (v : val) : option int := 
  match v with 
  | Vint i => Some i
  | _ => None
  end.

Inductive step: genv -> world -> world -> Prop :=
| step_NONE: forall ge w w' i sched,
  w_sched w = i::sched -> 
  FinMap.get (w_tm w) i = None -> 
  cswitch i w w' -> 
  step ge w w'
| step_CORE: forall ge w tm0 w' i sched phi q q' jm' n (Hcoh: consistent phi (w_dry w)),
  w_sched w = i::sched -> 
  FinMap.get (w_tm w) i = Some (phi, Krun q) -> 
  corestep ge q (proj1_sig (mk_juicy_mem Hcoh)) q' jm' -> 
  w_sched w = w_sched w' -> 
  age_thread_tbl n (w_tm w) = Some tm0 -> 
  w_tm w' = (FinMap.set i (m_phi jm', Krun q') tm0) -> 
  age_lock_pool n (w_lp w) = Some (w_lp w') -> 
  w_dry w' = m_dry jm' -> 
  step ge w w'
| step_EXIT: forall ge w w' i phi q sig arg,
  FinMap.get (w_tm w) i = Some (phi, Krun q) -> 
  at_external q = Some ((EXIT, sig), arg::nil) -> 
  cswitch i w w' -> 
  step ge w w'
| step_PRELOCK: forall ge w w2 w' i phi q sig arg b ofs,
  FinMap.get (w_tm w) i = Some (phi, Krun q) -> 
  at_external q = Some ((LOCK, sig), (arg::nil)) ->
  val2ptr arg = Some (b, ofs) -> 
  w_sched w2 = w_sched w -> 
  w_tm w2 = FinMap.set i (phi, Klock b (Int.signed ofs) q) (w_tm w) -> 
  w_lp w2 = w_lp w -> 
  w_dry w2 = w_dry w -> 
  cswitch i w2 w' -> 
  step ge w w'
| step_SPINLOCK: forall ge w w' i phi q b ofs,
  FinMap.get (w_tm w) i = Some (phi, Klock b ofs q) -> 
  rawload Mint32 (w_dry w) b ofs = Vint Int.zero -> 
  cswitch i w w' -> 
  step ge w w'
| step_LOCK: forall ge w w' i phi0 phi_lock phi q q' b ofs,
  FinMap.get (w_tm w) i = Some (phi0, Klock b ofs q) ->
  rawload Mint32 (w_dry w) b ofs = Vint Int.one ->
  after_external (Some (Vint Int.zero)) q = Some q' ->
  FinMap.get (w_lp w) (b, ofs) = Some phi_lock -> 
  join phi0 phi_lock phi -> 
  w_sched w' = w_sched w -> (*no context switch?*)
  w_tm w' = FinMap.set i (phi, Krun q') (w_tm w) -> 
  w_lp w' = FinMap.remove (b, ofs) (w_lp w) -> 
  w_dry w' = rawstore Mint32 (w_dry w) b ofs (Vint Int.zero) -> 
  step ge w w'
| step_UNLOCK: forall ge w w2 w' i phi0 phi_lock phi q q' sig arg b ofs rsh psh R,
  FinMap.get (w_tm w) i = Some (phi, Krun q) -> 
  join phi0 phi_lock phi -> 
  at_external q = Some ((UNLOCK, sig), arg::nil) ->
  val2ptr arg = Some (b, ofs) -> 
  rawload Mint32 (w_dry w) b (Int.signed ofs) = Vint Int.zero ->
  phi @ (b, Int.signed ofs) = YES rsh psh (LK 4) (SomeP [unit:Type] (fun _ => R)) -> (*fix args*)
  app_pred R phi_lock -> 
  after_external (Some (Vint Int.one)) q = Some q' ->
  w_sched w2 = w_sched w -> 
  w_tm w2 = FinMap.set i (phi, Krun q') (w_tm w) -> 
  w_lp w2 = FinMap.set (b, Int.signed ofs) phi_lock (w_lp w) -> 
  w_dry w2 = rawstore Mint32 (w_dry w) b (Int.signed ofs) (Vint Int.one) -> 
  cswitch i w2 w' -> 
  step ge w w'
| step_FORK: forall ge w w2 w' i i' phi_child phi_parent phi 
                       funsig q q2 q' sig fptr arg b ofs fP,
  FinMap.get (w_tm w) i = Some (phi, Krun q) ->
  join phi_child phi_parent phi -> 
  at_external q = Some ((FORK, sig), fptr::arg::nil) -> 
  val2ptr fptr = Some (b, ofs) -> 
  phi @ (b, Int.signed ofs) = PURE (FUN funsig) (SomeP [val:Type] fP) -> 
  app_pred (fP (arg,tt)) phi_child -> 
  after_external (Some (Vint Int.zero)) q = Some q2 ->
  FinMap.get (w_tm w) i' = None -> (*i' fresh*)
  mk_init_core ge arg (arg::nil) = Some q' ->
  w_sched w2 = w_sched w -> 
  let tm2 := FinMap.set i (phi_parent, Krun q2) (w_tm w) in
  w_tm w2 = FinMap.set i' (phi_child, Krun q') tm2 -> 
  w_lp w2 = w_lp w ->       
  w_dry w2 = w_dry w -> 
  cswitch i w2 w' -> 
  step ge w w'.

Inductive cm_corestep: genv -> world -> juicy_mem -> world -> juicy_mem -> Prop :=
| cm_step_corestep: forall ge jm w jm' w',
  m_dry jm=w_dry w -> 
  step ge w w' -> 
  m_dry jm'=w_dry w' -> 
  cm_corestep ge w jm w' jm'.

Program Definition cm_esem (sched: schedule) (d: jm_init_package) :=
  Build_CoreSemantics genv world juicy_mem jm_init_package 
    cm_initial_mem
    (cm_make_initial_core sched d)
    cm_at_external
    cm_after_external
    cm_safely_halted
    cm_corestep _ _ _.
Next Obligation.
intros until q'; intros H1.
inv H1.
inv H0.
(*NONE*)
destruct q; simpl in H1, H3; subst.
simpl; rewrite H3; auto.
(*SEQ*)
destruct q; simpl in H1, H3; subst.
apply corestep_not_at_external in H4.
simpl; rewrite H3, H4.
if_tac; auto.
Admitted.
Next Obligation.
intros until q'; intros H1.
inv H1.
inv H0.
inv H1.
unfold cm_safely_halted.
destruct (w_sched q).
inv H5.
inv H5.
rewrite H3; auto.
inv H1.
specialize (w_thread_tbl_ok q phi (Krun q0) i H3).
admit. (*by H8*)
Admitted.
Next Obligation.
intros sched d ge q.
unfold cm_safely_halted.
destruct q.
destruct sched0; [left; auto|]. 
unfold w_tm, w_sched.
simpl.
destruct (FinMap.get tm n).
destruct t; auto.
destruct c; try solve [left; auto|right; auto].
destruct (at_external c); try solve [left; auto|right; auto].
destruct p; try solve [left; auto|right; auto].
destruct p; try solve [left; auto|right; auto].
destruct e; try solve [if_tac; [left|right]; auto].
if_tac; auto.
auto.
Qed.

Definition cm_cores (i: nat) := if eq_nat_dec i 1 then Some csem else None.

Definition cm_proj_core (w: world) (i: nat) :=
  match FinMap.get (w_tm w) i with
  | None => None
  | Some (phi, Krun k) => Some k
  | Some (phi, Klock b ofs k) => Some k
  end.

Definition cm_active (w: world): nat :=
  match w_sched w with
  | nil => 1%nat 
  | i::sched => i
  end.

Definition cm_runnable (ge: genv) (w: world) :=
  match w_sched w with
  | nil => None
  | i::sched => 
    match FinMap.get (w_tm w) i with
    | None => None
    | Some (phi, Krun k) => match at_external k with
                            | None => Some i
                            | Some _ => None
                            end
    | Some (phi, Klock b ofs k) => None
    end
  end.

Definition cm_proj_zint (w: world) := tt.

Definition proj_zext (z: Z) := z.

Definition cm_zmult (u: unit) (z: Z) := z.

Implicit Arguments Extension.Make [G xT cT M D Z].

(*TODO: supply these signatures*)
Variable (client_sig: juicy_ext_sig Z).
Variable (esig: juicy_ext_sig Z).

Program Definition concurrency_extension (sched: schedule) (d: jm_init_package) :=
  Extension.Make unit Z (cm_esem sched d) cm_cores client_sig esig (EXIT::nil)
  cm_proj_core _
  cm_active _ _
  cm_runnable _ _ 
  _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
                             
End ConcurrencyExtension.


