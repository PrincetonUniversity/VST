
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

Require Import compcert.common.Memory.
Require Import compcert.common.Values. (*for val*)
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.pos.
Require Import VST.concurrency.common.threads_lemmas.
Require Import compcert.lib.Axioms.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import compcert.lib.Maps.
Require Import Coq.ZArith.ZArith.
Require Import VST.msl.Coqlib2.

Require Import VST.concurrency.common.lksize.

Set Implicit Arguments.


Inductive ctl {cT:Type} : Type :=
| Krun : cT -> ctl
| Kblocked : cT -> ctl
| Kresume : cT -> val -> ctl (* Carries the return value. Probably a unit.*)
| Kinit : val -> val -> ctl. (* vals correspond to vf and arg respectively. *)

Definition EqDec: Type -> Type :=
  fun A : Type => forall a a' : A, {a = a'} + {a <> a'}.

(* Nth_error for lists*)
(** * Definition of threadpool*)

Module ThreadPool.
  Section ThreadPool.

    Context {resources: Resources}.
    Context {Sem: Semantics}.
    
    Local Notation ctl := (@ctl semC).

    Notation tid:= nat.
    
    Class ThreadPool :=
      { t : Type;
        mkPool : ctl -> res -> t;
        containsThread : t -> tid -> Prop;
        getThreadC : forall {tid tp}, containsThread tp tid -> ctl;
        getThreadR : forall {tid tp}, containsThread tp tid -> res;
        resourceList : t -> seq.seq res;
        lockGuts : t -> AMap.t lock_info;  (* Gets the set of locks + their info    *)
        lockSet : t -> access_map;         (* Gets the permissions for the lock set *)
        lockRes : t -> address -> option lock_info;
        addThread : t -> val -> val -> res -> t;
        updThreadC : forall {tid tp}, containsThread tp tid -> ctl -> t;
        updThreadR : forall {tid tp}, containsThread tp tid -> res -> t;
        updThread : forall {tid tp}, containsThread tp tid -> ctl -> res -> t;
        updLockSet : t -> address -> lock_info -> t;
        remLockSet : t -> address -> t;
        latestThread : t -> tid;
        lr_valid : (address -> option lock_info) -> Prop;
        (*Find the first thread i, that satisfiList
es (filter i) *)
        find_thread_: t -> (ctl -> bool) -> option tid
        ; resourceList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (resourceList tp) i = Some (getThreadR cnti)          
        ;  containsThread_dec_:
             forall i tp, {containsThread tp i} + { ~ containsThread tp i}

        (*Proof Irrelevance of contains*)
        ;  cnt_irr: forall t tid
                      (cnt1 cnt2: containsThread t tid),
            cnt1 = cnt2

        (* Add Thread properties*)
        ;  cntAdd:
             forall {j tp} vf arg p,
               containsThread tp j ->
               containsThread (addThread tp vf arg p) j

        ;  cntAddLatest:
             forall {tp} vf arg p,
               containsThread (addThread tp vf arg p) (latestThread tp)

        ;  cntAdd':
             forall {j tp} vf arg p,
               containsThread (addThread tp vf arg p) j ->
               (containsThread tp j /\ j <> latestThread tp) \/ j = latestThread tp

        (* Update properties*)
        ;  cntUpdateC:
             forall {tid tid0 tp} c
               (cnt: containsThread tp tid),
               containsThread tp tid0->
               containsThread (updThreadC cnt c) tid0
        ;  cntUpdateC':
             forall {tid tid0 tp} c
               (cnt: containsThread tp tid),
               containsThread (updThreadC cnt c) tid0 ->
               containsThread tp tid0

        ;  cntUpdateR:
             forall {i j tp} r
               (cnti: containsThread tp i),
               containsThread tp j->
               containsThread (updThreadR cnti r) j
        ;  cntUpdateR':
             forall {i j tp} r
               (cnti: containsThread tp i),
               containsThread (updThreadR cnti r) j ->
               containsThread tp j

        ;  cntUpdate:
             forall {i j tp} c p
               (cnti: containsThread tp i),
               containsThread tp j ->
               containsThread (updThread cnti c p) j
        ;  cntUpdate':
             forall {i j tp} c p
               (cnti: containsThread tp i),
               containsThread (updThread cnti c p) j ->
               containsThread tp j

        ;  cntUpdateL:
             forall {j tp} add lf,
               containsThread tp j ->
               containsThread (updLockSet tp add lf) j
        ;  cntRemoveL:
             forall {j tp} add,
               containsThread tp j ->
               containsThread (remLockSet tp add) j

        ;  cntUpdateL':
             forall {j tp} add lf,
               containsThread (updLockSet tp add lf) j ->
               containsThread tp j
        ;  cntRemoveL':
             forall {j tp} add,
               containsThread (remLockSet tp add) j ->
               containsThread tp j

        (*;  gssLockPool:
    forall tp ls,
      lockSet (updLockSet tp ls) = ls*) (*Will change*)

        ;  gsoThreadLock:
             forall {i tp} c p (cnti: containsThread tp i),
               lockSet (updThread cnti c p) = lockSet tp

        ;  gsoThreadCLock :
             forall {i tp} c (cnti: containsThread tp i),
               lockSet (updThreadC cnti c) = lockSet tp

        ;  gsoThreadRLock :
             forall {i tp} p (cnti: containsThread tp i),
               lockSet (updThreadR cnti p) = lockSet tp

        ;  gsoAddLock :
             forall tp vf arg p,
               lockSet (addThread tp vf arg p) = lockSet tp

        ;  gssAddRes :
             forall {tp} vf arg pmap j
               (Heq: j = latestThread tp)
               (cnt': containsThread (addThread tp vf arg pmap) j),
               getThreadR cnt' = pmap

        (*Get thread Properties*)
        ;  gssThreadCode :
             forall {tid tp} (cnt: containsThread tp tid) c' p'
               (cnt': containsThread (updThread cnt c' p') tid),
               getThreadC cnt' = c'

        ;  gsoThreadCode :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) c' p'
               (cntj': containsThread (updThread cnti c' p') j),
               getThreadC cntj' = getThreadC cntj

        ;  gssThreadRes :
             forall {tid tp} (cnt: containsThread tp tid) c' p'
               (cnt': containsThread (updThread cnt c' p') tid),
               getThreadR cnt' = p'

        ;  gsoThreadRes :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) (Hneq: i <> j) c' p'
               (cntj': containsThread (updThread cnti c' p') j),
               getThreadR cntj' = getThreadR cntj

        ;  gssThreadCC :
             forall {tid tp} (cnt: containsThread tp tid) c'
               (cnt': containsThread (updThreadC cnt c') tid),
               getThreadC cnt' = c'

        ;  gsoThreadCC :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) c'
               (cntj': containsThread (updThreadC cnti c') j),
               getThreadC cntj = getThreadC cntj'

        ;  getThreadCC :
             forall {tp} i j
               (cnti : containsThread tp i) (cntj : containsThread tp j)
               c' (cntj' : containsThread (updThreadC cnti c') j),
               getThreadC cntj' = if Nat.eq_dec i j then c' else getThreadC cntj

        ;  gssThreadRR :
             forall {tid tp} (cnt: containsThread tp tid) p'
               (cnt': containsThread (updThreadR cnt p') tid),
               getThreadR cnt' = p'

        ;  gsoThreadRR :
             forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
               (cntj: containsThread tp j) p'
               (cntj': containsThread (updThreadR cnti p') j),
               getThreadR cntj = getThreadR cntj'

        ;  gThreadCR :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) c'
               (cntj': containsThread (updThreadC cnti c') j),
               getThreadR cntj' = getThreadR cntj

        ;  gThreadRC :
             forall {i j tp} (cnti: containsThread tp i)
               (cntj: containsThread tp j) p
               (cntj': containsThread (updThreadR cnti p) j),
               getThreadC cntj' = getThreadC cntj

        ;  gsoThreadCLPool :
             forall {i tp} c (cnti: containsThread tp i) addr,
               lockRes (updThreadC cnti c) addr = lockRes tp addr

        ;  gsoThreadLPool :
             forall {i tp} c p (cnti: containsThread tp i) addr,
               lockRes (updThread cnti c p) addr = lockRes tp addr

        ;  gsoAddLPool :
             forall tp vf arg p (addr : address),
               lockRes (addThread tp vf arg p) addr = lockRes tp addr

        ;  gLockSetRes :
             forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
               (cnti': containsThread (updLockSet tp addr res) i),
               getThreadR cnti' = getThreadR cnti

        ;  gLockSetCode :
             forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
               (cnti': containsThread (updLockSet tp addr res) i),
               getThreadC cnti' = getThreadC cnti

        ;  gssLockRes :
             forall tp addr pmap,
               lockRes (updLockSet tp addr pmap) addr = Some pmap

        ;  gsoLockRes:
             forall tp addr addr' pmap
               (Hneq: addr <> addr'),
               lockRes (updLockSet tp addr pmap) addr' =
               lockRes tp addr'

        ;  gssLockSet :
             forall tp b ofs rmap ofs',
               (ofs <= ofs' < ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               (Maps.PMap.get b (lockSet (updLockSet tp (b, ofs) rmap)) ofs') = Some Writable

        ;  gsoLockSet_1 :
             forall tp b ofs ofs'  pmap
               (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
               (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
               (Maps.PMap.get b (lockSet tp)) ofs'
        ;  gsoLockSet_2 :
             forall tp b b' ofs ofs' pmap,
               b <> b' ->
               (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
               (Maps.PMap.get b' (lockSet tp)) ofs'

        ;  lockSet__updLockSet:
             forall tp i (pf: containsThread tp i) c pmap addr rmap,
               lockSet (updLockSet tp addr rmap) =
               lockSet (updLockSet (updThread pf c pmap) addr rmap)

        ;  updThread_updThreadC__comm :
             forall tp i j c pmap' c'
               (Hneq: i <> j)
               (cnti : containsThread tp i)
               (cntj : containsThread tp j)
               (cnti': containsThread (updThread cntj c' pmap') i)
               (cntj': containsThread (updThreadC cnti c) j),
               updThreadC cnti' c = updThread cntj' c' pmap'

        ;  updThread_comm :
             forall tp i j c pmap c' pmap'
               (Hneq: i <> j)
               (cnti : containsThread tp i)
               (cntj : containsThread tp j)
               (cnti': containsThread (updThread cntj c' pmap') i)
               (cntj': containsThread (updThread cnti c pmap) j),
               updThread cnti' c pmap = updThread cntj' c' pmap'

        ;  add_updateC_comm :
             forall tp i vf arg pmap c'
               (cnti: containsThread tp i)
               (cnti': containsThread (addThread tp vf arg pmap) i),
               addThread (updThreadC cnti c') vf arg pmap =
               updThreadC cnti' c'

        ;  add_update_comm :
             forall tp i vf arg pmap c' pmap'
               (cnti: containsThread tp i)
               (cnti': containsThread (addThread tp vf arg pmap) i),
               addThread (updThread cnti c' pmap') vf arg pmap =
               updThread cnti' c' pmap'

        ;  updThread_lr_valid :
             forall tp i (cnti: containsThread tp i) c' m',
               lr_valid (lockRes tp) ->
               lr_valid (lockRes (updThread cnti c' m'))

        (*New Axioms, to avoid breaking the modularity *)
        ; lockSet_spec_2 :
            forall (js : t) (b : block) (ofs ofs' : Z),
              Intv.In ofs' (ofs, (ofs + Z.of_nat lksize.LKSIZE_nat)%Z) ->
              lockRes js (b, ofs) -> (lockSet js) !! b ofs' = Some Memtype.Writable

        ;  lockSet_spec_3 :
             forall ds b ofs,
               (forall z, z <= ofs < z+LKSIZE -> lockRes ds (b,z) = None)%Z ->
               (lockSet ds) !! b ofs = None

        ;  gsslockSet_rem : forall ds b ofs ofs0,
            lr_valid (lockRes ds) ->
            Intv.In ofs0 (ofs, ofs + lksize.LKSIZE)%Z ->
            isSome ((lockRes ds) (b,ofs)) ->  (*New hypothesis needed. Shouldn't be a problem *)
            (lockSet (remLockSet ds (b, ofs))) !! b ofs0 =
            None

        ;  gsolockSet_rem1 : forall ds b ofs b' ofs',
            b  <> b' ->
            (lockSet (remLockSet ds (b, ofs))) !! b' ofs' =
            (lockSet ds)  !! b' ofs'

        ;  gsolockSet_rem2 : forall ds b ofs ofs',
            lr_valid (lockRes ds) ->
            ~ Intv.In ofs' (ofs, ofs + lksize.LKSIZE)%Z ->
            (lockSet (remLockSet ds (b, ofs))) !! b ofs' =
            (lockSet ds)  !! b ofs'
        ;  gsslockResUpdLock: forall js a res,
            lockRes (updLockSet js a res) a =
            Some res
        ;  gsolockResUpdLock : forall js loc a res,
            loc <> a ->
            lockRes (updLockSet js loc res) a =
            lockRes js a

        ;  gsslockResRemLock : forall js a,
            lockRes (remLockSet js a) a =
            None
        ;  gsolockResRemLock : forall js loc a,
            loc <> a ->
            lockRes (remLockSet js loc) a =
            lockRes js a

        ;  gRemLockSetCode :
             forall {i tp} addr (cnti: containsThread tp i)
               (cnti': containsThread (remLockSet tp addr) i),
               getThreadC cnti' = getThreadC cnti

        ;  gRemLockSetRes :
             forall {i tp} addr (cnti: containsThread tp i)
               (cnti': containsThread (remLockSet tp addr) i),
               getThreadR cnti' = getThreadR cnti

        ;  gsoAddCode :
             forall {tp} vf arg pmap j
               (cntj: containsThread tp j)
               (cntj': containsThread (addThread tp vf arg pmap) j),
               getThreadC cntj' = getThreadC cntj

        ;  gssAddCode :
             forall {tp} vf arg pmap j
               (Heq: j = latestThread tp)
               (cnt': containsThread (addThread tp vf arg pmap) j),
               getThreadC cnt' = Kinit vf arg

        ;  gsoAddRes :
             forall {tp} vf arg pmap j
               (cntj: containsThread tp j) (cntj': containsThread (addThread tp vf arg pmap) j),
               getThreadR cntj' = getThreadR cntj

        ;  updLock_updThread_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c map l lmap,
             forall (cnti': containsThread (updLockSet ds l lmap) i),
               updLockSet
                 (@updThread _ ds cnti c map) l lmap =
               @updThread  _ (updLockSet ds l lmap) cnti' c map

        ;  remLock_updThread_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c map l,
             forall (cnti': containsThread (remLockSet ds l) i),
               remLockSet
                 (updThread cnti c map)
                 l =
               updThread cnti' c map
        ;  remLock_updThreadC_comm :
             forall ds,
             forall i (cnti: containsThread ds i) c l,
             forall (cnti': containsThread (remLockSet ds l) i),
               remLockSet (updThreadC cnti c) l = updThreadC cnti' c
      }.

  End ThreadPool.
End ThreadPool.

Module OrdinalPool.

  Definition empty_lset {lock_info}:AMap.t lock_info:=
    AMap.empty lock_info.

  Lemma find_empty:
    forall a l,
      @AMap.find a l empty_lset = None.
    unfold empty_lset.
    unfold AMap.empty, AMap.find; reflexivity.
  Qed.

  
  Section OrdinalThreadPool.

    Context {resources: Resources}.

    Context {Sem: Semantics}.
    
    Local Notation ctl := (@ctl semC).

    Notation tid:= nat.
    
    Record t := mk
                  { num_threads : pos
                    ; pool :> 'I_num_threads -> ctl
                    ; perm_maps : 'I_num_threads -> res
                    ; lset : AMap.t lock_info
                  }.

    Definition one_pos : pos.pos := pos.mkPos NPeano.Nat.lt_0_1.
    
    Definition mkPool c res :=
      mk one_pos
        (fun _ =>  c)
        (fun _ => res) (*initially there are no locks*)
        empty_lset.
    
    Definition lockGuts := lset.
    Definition lockSet (tp:t) := A2PMap (lset tp).

    Definition lockRes t : address -> option lock_info:=
      AMap.find (elt:=lock_info)^~ (lockGuts t).

    Definition lr_valid (lr: address -> option lock_info):=
      forall b ofs,
        match lr (b,ofs) with
        | Some r => forall ofs0:Z, (ofs < ofs0 < ofs+LKSIZE)%Z -> lr (b, ofs0) = None
        | _ => True
        end.

    Lemma is_pos: forall n, (0 < S n)%coq_nat.
    Proof. move=> n; omega. Qed.
    Definition mk_pos_S (n:nat):= mkPos (is_pos n).
    Lemma lt_decr: forall n m: nat, S n < m -> n < m.
    Proof. move=> m n /ltP LE.
           assert (m < n )%coq_nat by omega.
             by move: H => /ltP. Qed.
    Program Fixpoint find_thread' {st:t}{filter:ctl -> bool} n (P: n < num_threads st) {struct n}:=
      if filter (@pool st (@Ordinal (num_threads st) n P))
      then Some n
      else match n with
           | S n' =>  find_thread' n' (lt_decr  n' _ P)
           | O => None
           end.
    
    Next Obligation.
      intros; exact st.
    Defined.
    Next Obligation.
      intros. auto.
    Qed.
    Next Obligation.
      intros. subst; reflexivity.
    Defined.
    Definition pos_pred (n:pos): nat.
    Proof. destruct n. destruct n eqn:AA; [omega|].
           exact n0.
    Defined.

    Program Definition find_thread (st:t)(filter:ctl -> bool): option tid:=
      @find_thread' st filter (pos_pred (num_threads st)) _ .
    Next Obligation.
      rewrite /pos_pred /= => st filter.
      elim (num_threads st) => n N_pos /=.
      destruct n; try omega; eauto.
    Qed.

    Import Coqlib.

    Lemma lockSet_WorNE: forall js b ofs,
        (lockSet js) !! b ofs = Some Memtype.Writable \/
        (lockSet js) !! b ofs = None.
    Proof.
      intros. unfold lockSet.
      unfold A2PMap.
      rewrite <- List.fold_left_rev_right.
      match goal with |- context [List.fold_right ?F ?Z ?A] =>
                      set (f := F); set (z:=Z); induction A end.
      right. simpl. rewrite PMap.gi. auto.
      change (List.fold_right f z (a::l)) with (f a (List.fold_right f z l)).
      unfold f at 1 3.
      destruct a. destruct a.
      destruct (peq b0 b).
      - subst b0.
        pose proof permissions.setPermBlock_or (Some Memtype.Writable) b z0 LKSIZE_nat (fold_right f z l) b ofs as H.
        destruct H as [-> | ->]; auto.
      - rewrite permissions.setPermBlock_other_2; auto.
    Qed.

    Lemma lockSet_spec_2 :
      forall (js : t) (b : block) (ofs ofs' : Z),
        Intv.In ofs' (ofs, (ofs + Z.of_nat lksize.LKSIZE_nat)%Z) ->
        lockRes js (b, ofs) -> (lockSet js) !! b ofs' = Some Memtype.Writable.
    Proof.
      intros.
      hnf in H0.
      hnf in H. simpl in H.
      unfold lockSet. unfold A2PMap.
      rewrite <- List.fold_left_rev_right.
      unfold lockRes in H0. unfold lockGuts in H0.
      match type of H0 with isSome ?A = true=> destruct A eqn:?H; inv H0 end.
      apply AMap.find_2 in H1.
      apply AMap.elements_1 in H1.
      apply SetoidList.InA_rev in H1.
      unfold AMap.key in H1.
      forget (@rev (address * lock_info) (AMap.elements (elt:=lock_info) (lset js))) as el.
      match goal with |- context [List.fold_right ?F ?Z ?A] =>
                      set (f := F); set (z:=Z) end.
      revert H1; induction el; intros.
      inv H1.
      apply SetoidList.InA_cons in H1.
      destruct H1.
      hnf in H0. destruct a; simpl in H0. destruct H0; subst a l0.
      simpl. rewrite setPermBlock_lookup; if_tac; auto.
      contradiction H0; split; auto.
      apply IHel in H0; clear IHel.
      simpl.
      unfold f at 1. destruct a. destruct a.
      rewrite setPermBlock_lookup; if_tac; auto.
    Qed.

    Lemma lockSet_spec_1: forall js b ofs,
        lockRes js (b,ofs) ->
        (lockSet js) !! b ofs = Some Memtype.Writable.
    Proof.
      intros.
      eapply lockSet_spec_2; eauto.
      unfold Intv.In.
      simpl. pose proof LKSIZE_pos; rewrite Z2Nat.id; omega.
    Qed.

    Open Scope nat_scope.

    (* Definition containsThread_dec (tp : t) (i : NatTID.tid) : bool:=
  Compare.Pcompare i (num_threads tp). *)
    Definition containsThread (tp : t) (i : NatTID.tid) : Prop:=
      i < num_threads tp.

    Definition containsThread_dec:
      forall i tp, {containsThread tp i} + { ~ containsThread tp i}.
    Proof.
      intros.
      unfold containsThread.
      destruct (leq (S i) (num_threads tp)) eqn:Hleq;
        by auto.
    Defined.

    Definition getThreadC {i tp} (cnt: containsThread tp i) : ctl :=
      tp (Ordinal cnt).

    Definition unique_Krun' tp i :=
      ( forall j cnti q,
          @getThreadC j tp cnti = Krun q ->
          eq_nat_dec i j ).

    Definition is_running tp i:=
      exists cnti q, @getThreadC i tp cnti = Krun q.

    Lemma unique_runing_not_running:
      forall tp i,
        unique_Krun' tp i ->
        ~ is_running tp i ->
        forall j, unique_Krun' tp j.
    Proof.
      unfold unique_Krun', is_running.
      intros.
      specialize (H  _ _ _ H1);
        destruct (eq_nat_dec i j0); inversion H; subst.

      exfalso; apply H0 .
      exists cnti, q; assumption.
    Qed.


    Definition getThreadR {i tp} (cnt: containsThread tp i) : res :=
      (perm_maps tp) (Ordinal cnt).

    Definition latestThread tp := n (num_threads tp).

    Definition addThread (tp : t) (vf arg : val) (pmap : res) : t :=
      let: new_num_threads := pos_incr (num_threads tp) in
      let: new_tid := ordinal_pos_incr (num_threads tp) in
      mk new_num_threads
         (fun (n : 'I_new_num_threads) =>
            match unlift new_tid n with
            | None => Kinit vf arg
            | Some n' => tp n'
            end)
         (fun (n : 'I_new_num_threads) =>
            match unlift new_tid n with
            | None => pmap
            | Some n' => (perm_maps tp) n'
            end)
         (lset tp).

    Definition updLockSet tp (add:address) (lf:lock_info) : t :=
      mk (num_threads tp)
         (pool tp)
         (perm_maps tp)
         (AMap.add add lf (lockGuts tp)).

    Definition remLockSet tp  (add:address) : t :=
      mk (num_threads tp)
         (pool tp)
         (perm_maps tp)
         (AMap.remove add (lockGuts tp)).

    Definition updThreadC {tid tp} (cnt: containsThread tp tid) (c' : ctl) : t :=
      mk (num_threads tp)
         (fun n => if n == (Ordinal cnt) then c' else (pool tp)  n)
         (perm_maps tp)
         (lset tp).

    Definition updThreadR {tid tp} (cnt: containsThread tp tid)
               (pmap' : res) : t :=
      mk (num_threads tp) (pool tp)
         (fun n =>
            if n == (Ordinal cnt) then pmap' else (perm_maps tp) n)
         (lset tp).

    Definition updThread {tid tp} (cnt: containsThread tp tid) (c' : ctl)
               (pmap : res) : t :=
      mk (num_threads tp)
         (fun n =>
            if n == (Ordinal cnt) then c' else tp n)
         (fun n =>
            if n == (Ordinal cnt) then pmap else (perm_maps tp) n)
         (lset tp).

    (*TODO: see if typeclasses can automate these proofs, probably not thanks dep types*)

    (*Proof Irrelevance of contains*)
    Lemma cnt_irr: forall t tid
                     (cnt1 cnt2: containsThread t tid),
        cnt1 = cnt2.
    Proof. intros. apply proof_irr. Qed.

    (* Update properties*)
    Lemma numUpdateC :
      forall {tid tp} (cnt: containsThread tp tid) c,
        num_threads tp =  num_threads (updThreadC cnt c).
    Proof.
      intros tid tp cnt c.
      destruct tp; simpl; reflexivity.
    Qed.

    Lemma cntUpdateC :
      forall {tid tid0 tp} c
        (cnt: containsThread tp tid),
        containsThread tp tid0 ->
        containsThread (updThreadC cnt c) tid0.
    Proof.
      intros tid tp.
      unfold containsThread; intros.
      rewrite <- numUpdateC; assumption.
    Qed.
    Lemma cntUpdateC':
      forall {tid tid0 tp} c
        (cnt: containsThread tp tid),
        containsThread (updThreadC cnt c) tid0 ->
        containsThread tp tid0.
    Proof.
      intros tid tp.
      unfold containsThread; intros.
      rewrite <- numUpdateC in H; assumption.
    Qed.

    Lemma cntUpdateR:
      forall {i j tp} r
        (cnti: containsThread tp i),
        containsThread tp j->
        containsThread (updThreadR cnti r) j.
    Proof.
      intros tid tp.
      unfold containsThread; intros.
        by simpl.
    Qed.

    Lemma cntUpdateR':
      forall {i j tp} r
        (cnti: containsThread tp i),
        containsThread (updThreadR cnti r) j ->
        containsThread tp j.
    Proof.
      intros tid tp.
      unfold containsThread; intros.
        by simpl.
    Qed.

    Lemma cntUpdate :
      forall {i j tp} c p
        (cnti: containsThread tp i),
        containsThread tp j ->
        containsThread (updThread cnti c p) j.
    Proof.
      intros tid tp.
      unfold containsThread; intros.
        by simpl.
    Qed.

    Lemma cntUpdate':
      forall {i j tp} c p
        (cnti: containsThread tp i),
        containsThread (updThread cnti c p) j ->
        containsThread tp j.
    Proof.
      intros.
      unfold containsThread in *; intros.
        by simpl in *.
    Qed.

    Lemma cntUpdateL:
      forall {j tp} add lf,
        containsThread tp j ->
        containsThread (updLockSet tp add lf) j.
    Proof.
      intros; unfold containsThread, updLockSet in *;
        simpl; by assumption.
    Qed.
    Lemma cntRemoveL:
      forall {j tp} add,
        containsThread tp j ->
        containsThread (remLockSet tp add) j.
    Proof.
      intros; unfold containsThread, updLockSet in *;
        simpl; by assumption.
    Qed.

    Lemma cntUpdateL':
      forall {j tp} add lf,
        containsThread (updLockSet tp add lf) j ->
        containsThread tp j.
    Proof.
      intros. unfold containsThread, updLockSet in *;
                simpl in *; by assumption.
    Qed.
    Lemma cntRemoveL':
      forall {j tp} add,
        containsThread (remLockSet tp add) j ->
        containsThread tp j.
    Proof.
      intros. unfold containsThread, updLockSet in *;
                simpl in *; by assumption.
    Qed.

    Lemma cntAdd:
      forall {j tp} vf arg p,
        containsThread tp j ->
        containsThread (addThread tp vf arg p) j.
    Proof.
      intros;
        unfold addThread, containsThread in *;
        simpl;
          by auto.
    Qed.

    Lemma cntAddLatest:
      forall {tp} vf arg p,
        containsThread (addThread tp vf arg p) (latestThread tp).
    Proof.
      intros;
        unfold addThread, containsThread, latestThread;
        simpl;
          by auto.
    Qed.

    Lemma cntAdd':
      forall {j tp} vf arg p,
        containsThread (addThread tp vf arg p) j ->
        (containsThread tp j /\ j <> num_threads tp) \/ j = num_threads tp.
    Proof.
      intros.
      unfold containsThread in *.
      simpl in *.
      destruct (j < (num_threads tp)) eqn:Hlt.
      left.
      split;
        by [auto | ssromega].
      right.
      rewrite ltnS in H.
      rewrite leq_eqVlt in H.
      move/orP:H=> [H | H];
                    first by move/eqP:H.
      exfalso.
        by ssromega.
    Qed.

    Lemma contains_add_latest: forall ds p a r,
        containsThread (addThread ds p a r)
                       (latestThread ds).
    Proof. intros.
           simpl. unfold containsThread, latestThread.
           simpl. ssromega.
    Qed.

    Lemma updLock_updThread_comm:
      forall ds,
      forall i (cnti: containsThread ds i) c map l lmap,
      forall (cnti': containsThread (updLockSet ds l lmap) i),
        updLockSet
          (@updThread _ ds cnti c map) l lmap =
        @updThread _ (updLockSet ds l lmap) cnti' c map.
      unfold updLockSet, updThread; simpl; intros.
      f_equal.
    Qed.
    Lemma remLock_updThread_comm:
      forall ds,
      forall i (cnti: containsThread ds i) c map l,
      forall (cnti': containsThread (remLockSet ds l) i),
        remLockSet
          (updThread cnti c map)
          l =
        updThread cnti' c map.
      unfold remLockSet, updThread; simpl; intros.
      f_equal.
    Qed.

    Lemma remLock_updThreadC_comm :
      forall ds i (cnti: containsThread ds i) c l
        (cnti': containsThread (remLockSet ds l) i),
        remLockSet (updThreadC cnti c) l = updThreadC cnti' c.
    Proof.
      unfold remLockSet, updThreadC; simpl; intros.
      f_equal.
    Qed.

    (* TODO: most of these proofs are similar, automate them*)
    (** Getters and Setters Properties*)

    Set Bullet Behavior "None".
    Set Bullet Behavior "Strict Subproofs".

    Lemma gsslockResUpdLock: forall js a res,
        lockRes (updLockSet js a res) a =
        Some res.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find; simpl.
      forget (AMap.this (lockGuts js)) as el.
      unfold AMap.find; simpl.
      induction el.
      *
        simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
      *
        rewrite AMap.Raw.add_equation. destruct a0.
        destruct (AddressOrdered.compare a a0).
        simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
        simpl.
        destruct (@AMap.Raw.PX.MO.elim_compare_eq a a); auto. rewrite H. auto.
        simpl.
        destruct (AddressOrdered.compare a a0).
        pose proof (AddressOrdered.lt_trans l1 l0).
        apply AddressOrdered.lt_not_eq in H. contradiction H.
        reflexivity.
        apply AddressOrdered.lt_not_eq in l0.
        hnf in e. subst. contradiction l0; reflexivity.
        auto.
    Qed.


    Ltac address_ordered_auto :=
      auto; repeat match goal with
                   | H: AddressOrdered.eq ?A ?A |- _ => clear H
                   | H: AddressOrdered.eq ?A ?B |- _ => hnf in H; subst A
                   | H: ?A <> ?A |- _ => contradiction H; reflexivity
                   | H: AddressOrdered.lt ?A ?A |- _ =>
                     apply AddressOrdered.lt_not_eq in H; contradiction H; reflexivity
                   | H: AddressOrdered.lt ?A ?B, H': AddressOrdered.lt ?B ?A |- _ =>
                     contradiction (AddressOrdered.lt_not_eq (AddressOrdered.lt_trans H H')); reflexivity
                   end.

    Lemma gsolockResUpdLock: forall js loc a res,
        loc <> a ->
        lockRes (updLockSet js loc res) a =
        lockRes js a.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find; simpl.
      forget (AMap.this (lockGuts js)) as el.
      unfold AMap.find; simpl.
      induction el; simpl.
      destruct (AddressOrdered.compare a loc); auto.
      address_ordered_auto.
      destruct a0.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a0 a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare loc a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      pose proof (AddressOrdered.lt_trans l1 l0).
      destruct (AddressOrdered.compare a loc); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
    Qed.

    Lemma gsslockResRemLock: forall js a,
        lockRes (remLockSet js a) a =
        None.
    Proof.
      intros.
      unfold lockRes, remLockSet; simpl. unfold AMap.find, AMap.remove; simpl.
      destruct js; simpl. destruct lset0; simpl.
      assert (SetoidList.NoDupA (@AMap.Raw.PX.eqk _) this).
      apply SetoidList.SortA_NoDupA with (@AMap.Raw.PX.ltk _); auto with typeclass_instances.
      rename this into el.
      revert H; clear; induction el; simpl; intros; auto.
      destruct a0.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      inv H.
      clear - H2.
      revert H2; induction el; intros; auto.
      simpl. destruct a.
      destruct (AddressOrdered.compare a0 a); simpl; address_ordered_auto.
      contradiction H2. left. reflexivity.
      destruct (AddressOrdered.compare a a0); simpl; address_ordered_auto.
      apply IHel.
      inv H; auto.
    Qed.

    Lemma gsolockResRemLock: forall js loc a,
        loc <> a ->
        lockRes (remLockSet js loc) a =
        lockRes js a.
    Proof.
      intros.
      unfold lockRes, remLockSet; simpl. unfold AMap.find, AMap.remove; simpl.
      destruct js; simpl. destruct lset0; simpl.
      rename this into el.
      induction sorted; simpl; auto.
      destruct a0 as [b ?].
      destruct (AddressOrdered.compare loc b); simpl; address_ordered_auto;
        destruct (AddressOrdered.compare a b); simpl; address_ordered_auto.
      assert (forall (y: address * lock_info), SetoidList.InA (@AMap.Raw.PX.eqk _) y l -> AMap.Raw.PX.ltk (b,l0) y).
      apply SetoidList.InfA_alt; auto with typeclass_instances.
      specialize (H1 (a,l0)).
      assert (~SetoidList.InA (AMap.Raw.PX.eqk (elt:=lock_info)) (a, l0) l ).
      intro. specialize (H1 H2).
      change (AddressOrdered.lt b a) in H1. address_ordered_auto.
      clear - H2.
      induction l as [| [b ?]]; simpl in *; auto.
      destruct (AddressOrdered.compare a b); simpl; address_ordered_auto.
      contradiction H2. left; auto.
    Qed.


    Lemma gsoThreadLock:
      forall {i tp} c p (cnti: containsThread tp i),
        lockSet (updThread cnti c p) = lockSet tp.
    Proof.
        by auto.
    Qed.

    Lemma gsoThreadCLock:
      forall {i tp} c (cnti: containsThread tp i),
        lockSet (updThreadC cnti c) = lockSet tp.
    Proof.
        by auto.
    Qed.

    Lemma gsoThreadRLock:
      forall {i tp} p (cnti: containsThread tp i),
        lockSet (updThreadR cnti p) = lockSet tp.
    Proof.
      auto.
    Qed.

    Lemma gsoAddLock:
      forall tp vf arg p,
        lockSet (addThread tp vf arg p) = lockSet tp.
    Proof.
      auto.
    Qed.

    Lemma PX_in_rev:
      forall elt a m, AMap.Raw.PX.In (elt:=elt) a m <-> AMap.Raw.PX.In a (rev m).
    Proof.
      intros.
      unfold AMap.Raw.PX.In.
      unfold AMap.Raw.PX.MapsTo.
      split; intros [e ?]; exists e.
      rewrite SetoidList.InA_rev; auto.
      rewrite <- SetoidList.InA_rev; auto.
    Qed.

    Import SetoidList.
    Arguments InA {A}{eqA} x _.
    Arguments AMap.In {elt} x m.

    Lemma lockRes_range_dec: forall tp b ofs,
        { (exists z, z <= ofs < z+LKSIZE /\ lockRes tp (b,z) )%Z  } + {(forall z, z <= ofs < z+LKSIZE -> lockRes tp (b,z) = None)%Z }.
    Proof.
      intros tp b ofs.
      assert (H : (0 <= LKSIZE)%Z) by (pose proof LKSIZE_pos; omega).
      destruct (@RiemannInt_SF.IZN_var _ H) as (n, ->).
      induction n.
      - right. simpl. intros. omega.
      - destruct IHn as [IHn | IHn].
        + left; destruct IHn as (z & r & Hz).
          exists z; split; auto. zify. omega.
        + destruct (lockRes tp (b, (ofs - Z.of_nat n)%Z)) eqn:Ez.
          * left. exists (ofs - Z.of_nat n)%Z; split. 2:rewrite Ez; auto.
            zify; omega.
          * right; intros z r.
            destruct (zeq ofs (z + Z.of_nat n)%Z).
            -- subst; auto. rewrite <-Ez; do 2 f_equal. omega.
            -- apply IHn. zify. omega.
    Qed.

    Lemma lockSet_spec_3:
      forall ds b ofs,
        (forall z, z <= ofs < z+LKSIZE -> lockRes ds (b,z) = None)%Z ->
        (lockSet ds) !! b ofs = None.
    Proof.
      intros.
      unfold lockSet. unfold A2PMap.
      rewrite <- !List.fold_left_rev_right.
      match goal with |- context [fold_right ?F ?I] => set (f:=F); set (init:=I)end.
      unfold lockRes in H.
      assert (H': forall z,  (z <= ofs < z + LKSIZE)%Z ->
                        ~ AMap.In (b,z) (lockGuts ds)). {
        intros. intro. destruct H1; apply AMap.find_1 in H1.
        rewrite H in H1. inv H1. auto.
      } clear H.
      unfold lockGuts in *.
      assert (H7 : forall (x : AMap.key) (e : lock_info),
                 @InA _ (@AMap.eq_key_elt lock_info) (x, e) (rev (AMap.elements (lset ds))) ->
                 AMap.MapsTo x e (lset ds)). {
        intros. apply AMap.elements_2. rewrite -> InA_rev in H. apply H.
      }
      change address with AMap.key.
      forget (rev (AMap.elements (lset ds))) as al.
      revert H7; induction al; intros.
      simpl. rewrite PMap.gi. auto.
      change ((f a (fold_right f init al)) !! b ofs = None).
      unfold f at 1. destruct a as [[? ?] ?].
      simpl.
      rewrite setPermBlock_lookup; if_tac; auto.
      destruct H as [Heq H]; subst.
      apply H' in H. contradiction H.
      specialize (H7 (b,z) l). spec H7; [left; reflexivity |].
      exists l; auto.
    Qed.

    Lemma gsslockSet_rem: forall ds b ofs ofs0,
        lr_valid (lockRes ds) ->
        Intv.In ofs0 (ofs, ofs + lksize.LKSIZE)%Z ->
        isSome ((lockRes ds) (b,ofs)) ->  (*New hypothesis needed. Shouldn't be a problem *)
        (lockSet (remLockSet ds (b, ofs))) !! b ofs0 =
        None.
    Proof.
      intros.
      hnf in H0; simpl in H0.
      apply lockSet_spec_3.
      unfold LKSIZE in H0.
      unfold LKSIZE.
      intros.
      destruct (zeq ofs z).
      * subst ofs.
        unfold lockRes. unfold lockGuts. unfold remLockSet. simpl.
        assert (H8 := @AMap.remove_1 _ (lockGuts ds) (b,z) (b,z) (refl_equal _)).
        destruct (AMap.find (b, z) (AMap.remove (b, z) (lockGuts ds))) eqn:?; auto.
        apply  AMap.find_2 in Heqo.
        contradiction H8; eexists; eassumption.
      * hnf in H.
        destruct (lockRes ds (b,z)) eqn:?; inv H1.
      + destruct (lockRes ds (b,ofs)) eqn:?; inv H4.
        assert (z <= ofs < z+2 * size_chunk AST.Mptr \/ ofs <= z <= ofs+2 * size_chunk AST.Mptr)%Z by omega.
        destruct H1.
      - specialize (H b z). rewrite Heqo in H. unfold LKSIZE in H.
        specialize (H ofs). spec H; [omega|]. congruence.
      - specialize (H b ofs). rewrite Heqo0 in H. specialize (H z).
        unfold LKSIZE in H.
        spec H; [omega|]. congruence.
        + unfold lockRes, remLockSet.  simpl.
          assert (H8 := @AMap.remove_3 _ (lockGuts ds) (b,ofs) (b,z)).
          destruct (AMap.find (b, z) (AMap.remove (b, ofs) (lockGuts ds))) eqn:?; auto.
          apply  AMap.find_2 in Heqo0. apply H8 in Heqo0.
          unfold lockRes in Heqo.
          apply AMap.find_1 in Heqo0. congruence.
    Qed.



    Lemma gsolockSet_rem1: forall ds b ofs b' ofs',
        b  <> b' ->
        (lockSet (remLockSet ds (b, ofs))) !! b' ofs' =
        (lockSet ds)  !! b' ofs'.
    Proof.

      intros.
      destruct (lockRes_range_dec ds b' ofs').
      - destruct e as [z [ineq HH]]. unfold LKSIZE in ineq.
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResRemLock; auto.
          intros AA. inversion AA; subst. congruence.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        rewrite gsolockResRemLock; auto.
        intros AA. inversion AA; congruence.
    Qed.

    Lemma gsolockSet_rem2: forall ds b ofs ofs',
        lr_valid (lockRes ds) ->
        ~ Intv.In ofs' (ofs, ofs + lksize.LKSIZE)%Z ->
        (lockSet (remLockSet ds (b, ofs))) !! b ofs' =
        (lockSet ds)  !! b ofs'.
    Proof.
      intros.
      destruct (lockRes_range_dec ds b ofs').
      - destruct e as [z [ineq HH]].
        assert (ofs <> z).
        { intros AA. inversion AA.
          apply H0. hnf.
          simpl; omega. }
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResRemLock; auto.
          intros AA. inversion AA. congruence.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        destruct (zeq ofs z).
        subst ofs; rewrite gsslockResRemLock; auto.
        rewrite gsolockResRemLock; auto.
        intros AA. inversion AA; congruence.
    Qed.

    Lemma gssThreadCode {tid tp} (cnt: containsThread tp tid) c' p'
          (cnt': containsThread (updThread cnt c' p') tid) :
      getThreadC cnt' = c'.
    Proof.
      simpl.
      unfold eq_op; simpl. rewrite eq_refl; auto.
    Qed.

    Lemma eq_op_false: forall A i j, i <>j -> @eq_op A i j = false.
    Proof.
      intros.
      unfold eq_op; simpl.
      unfold Equality.op. destruct A eqn:?. simpl.
      unfold Equality.sort in *.
      destruct m; simpl in *.
      generalize (a i j); intros. inv H0; auto. contradiction H;auto.
    Qed.

    Lemma gsoThreadCode:
      forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
        (cntj: containsThread tp j) c' p'
        (cntj': containsThread (updThread cnti c' p') j),
        getThreadC cntj' = getThreadC cntj.
    Proof.
      intros.
      simpl.
      unfold eq_op. simpl.
      rewrite eq_op_false; auto.
      unfold updThread in cntj'. unfold containsThread in *. simpl in *.
      unfold getThreadC. do 2 apply f_equal. apply proof_irr.
    Qed.

    Lemma gssThreadRes {tid tp} (cnt: containsThread tp tid) c' p'
          (cnt': containsThread (updThread cnt c' p') tid) :
      getThreadR cnt' = p'.
    Proof.
      simpl.
      unfold eq_op; simpl. rewrite eq_refl; auto.
    Qed.

    Lemma gsoThreadRes {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) (Hneq: i <> j) c' p'
          (cntj': containsThread (updThread cnti c' p') j) :
      getThreadR cntj' = getThreadR cntj.
    Proof.
      simpl.
      unfold eq_op; simpl.
      rewrite eq_op_false; auto.
      unfold updThread in cntj'. unfold containsThread in *. simpl in *.
      unfold getThreadR. do 2 apply f_equal. apply proof_irr.
    Qed.

    Lemma gssThreadCC {tid tp} (cnt: containsThread tp tid) c'
          (cnt': containsThread (updThreadC cnt c') tid) :
      getThreadC cnt' = c'.
    Proof.
      simpl.
      unfold eq_op; simpl. rewrite eq_refl. auto.
    Qed.

    Lemma gsoThreadCC {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
          (cntj: containsThread tp j) c'
          (cntj': containsThread (updThreadC cnti c') j) :
      getThreadC cntj = getThreadC cntj'.
    Proof.
      simpl.
      unfold eq_op; simpl.
      rewrite eq_op_false; auto.
      unfold updThreadC in cntj'. unfold containsThread in *.
      simpl in cntj'. unfold getThreadC.
      do 2 apply f_equal. by apply proof_irr.
    Qed.

    Lemma getThreadCC
          {tp} i j
          (cnti : containsThread tp i) (cntj : containsThread tp j)
          c' (cntj' : containsThread (updThreadC cnti c') j):
      getThreadC cntj' = if eq_nat_dec i j then c' else getThreadC cntj.
    Proof.
      destruct (eq_nat_dec i j); subst;
        [rewrite gssThreadCC |
         erewrite <- @gsoThreadCC with (cntj := cntj)];
        now eauto.
    Qed.

    Lemma gssThreadRR {tid tp} (cnt: containsThread tp tid) p'
          (cnt': containsThread (updThreadR cnt p') tid) :
      getThreadR cnt' = p'.
    Proof.
      simpl.
      unfold eq_op; simpl. rewrite eq_refl. auto.
    Qed.

    Lemma gsoThreadRR {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
          (cntj: containsThread tp j) p'
          (cntj': containsThread (updThreadR cnti p') j) :
      getThreadR cntj = getThreadR cntj'.
    Proof.
      simpl.
      unfold eq_op; simpl.
      rewrite eq_op_false; auto.
      unfold updThreadR in cntj'. unfold containsThread in *.
      simpl in cntj'. unfold getThreadR.
      do 2 apply f_equal. by apply proof_irr.
    Qed.

    Lemma gThreadCR {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) c'
          (cntj': containsThread (updThreadC cnti c') j) :
      getThreadR cntj' = getThreadR cntj.
    Proof.
      simpl.
      unfold getThreadR.
      unfold updThreadC, containsThread in *. simpl in *.
      do 2 apply f_equal.
      apply proof_irr.
    Qed.

    Lemma gThreadRC {i j tp} (cnti: containsThread tp i)
          (cntj: containsThread tp j) p
          (cntj': containsThread (updThreadR cnti p) j) :
      getThreadC cntj' = getThreadC cntj.
    Proof.
      simpl.
      unfold getThreadC.
      unfold updThreadR, containsThread in *. simpl in *.
      do 2 apply f_equal.
      apply proof_irr.
    Qed.

    Lemma unlift_m_inv :
      forall tp i (Htid : i < (num_threads tp).+1) ord
        (Hunlift: unlift (ordinal_pos_incr (num_threads tp))
                         (Ordinal (n:=(num_threads tp).+1)
                                  (m:=i) Htid)=Some ord),
        nat_of_ord ord = i.
    Proof.
      intros.
      assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp))
                                   (Ordinal (n:=(num_threads tp).+1)
                                            (m:=i) Htid) (Some ord)).
      rewrite <- Hunlift.
      apply/unliftP.
      inversion Hcontra; subst.
      inversion H0.
      unfold bump.
      assert (pf: ord < (num_threads tp))
        by (by rewrite ltn_ord).
      assert (H: (num_threads tp) <= ord = false).
      rewrite ltnNge in pf.
      rewrite <- Bool.negb_true_iff. auto.
      rewrite H. simpl. rewrite add0n. reflexivity.
    Defined.

    Lemma gssAddRes:
      forall {tp} vf arg pmap j
        (Heq: j = latestThread tp)
        (cnt': containsThread (addThread tp vf arg pmap) j),
        getThreadR cnt' = pmap.
    Proof.
      intros. subst.
      simpl.
      unfold containsThread in cnt'. simpl in cnt'.
      destruct (unlift (ordinal_pos_incr (num_threads tp))
                       (Ordinal (n:=(num_threads tp).+1)
                                (m:=num_threads tp) cnt')) eqn:H.
      apply unlift_m_inv in H.
      destruct o.
      simpl in *.
      subst. exfalso;
               ssromega.
      rewrite H. by reflexivity.
    Qed.

    Lemma gsoAddRes:
      forall {tp} vf arg pmap j
        (cntj: containsThread tp j) (cntj': containsThread (addThread tp vf arg pmap) j),
        getThreadR cntj' = getThreadR cntj.
    Proof.
      intros.
      simpl.
      destruct (unlift (ordinal_pos_incr (num_threads tp))
                       (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj')) eqn:Hunlift.
      rewrite Hunlift.
      apply unlift_m_inv in Hunlift.
      subst j.  simpl in *.
      unfold getThreadR.
      destruct o.
      simpl;
        by erewrite proof_irr with (a1 := i) (a2:= cntj).
      exfalso .
      unfold containsThread in *. simpl in *.
      assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                         != (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj')).
      { apply/eqP. intros Hcontra.
        unfold ordinal_pos_incr in Hcontra.
        inversion Hcontra; auto. subst. by ssromega.
      }
      apply unlift_some in Hcontra. rewrite Hunlift in Hcontra.
      destruct Hcontra; by discriminate.
    Qed.

    Lemma gssAddCode:
      forall {tp} vf arg pmap j
        (Heq: j = latestThread tp)
        (cnt': containsThread (addThread tp vf arg pmap) j),
        getThreadC cnt' = Kinit vf arg.
    Proof.
      intros. subst.
      simpl.
      unfold containsThread in cnt'. simpl in cnt'.
      destruct (unlift (ordinal_pos_incr (num_threads tp))
                       (Ordinal (n:=(num_threads tp).+1)
                                (m:=num_threads tp) cnt')) eqn:H.
      apply unlift_m_inv in H.
      destruct o. simpl in *.
      subst. exfalso;
               ssromega.
      rewrite H.
        by reflexivity.
    Qed.

    Lemma gsoAddCode:
      forall {tp} vf arg pmap j
        (cntj: containsThread tp j)
        (cntj': containsThread (addThread tp vf arg pmap) j),
        getThreadC cntj' = getThreadC cntj.
    Proof.
      intros.
      simpl.
      destruct (unlift (ordinal_pos_incr (num_threads tp))
                       (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj')) eqn:Hunlift.
      rewrite Hunlift.
      apply unlift_m_inv in Hunlift.
      subst j.  simpl in *.
      unfold getThreadC.
      destruct o.
      simpl;
        by erewrite proof_irr with (a1 := i) (a2:= cntj).
      exfalso.
      unfold containsThread in *.
      simpl in *.
      assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                         != (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj')).
      { apply/eqP. intros Hcontra.
        unfold ordinal_pos_incr in Hcontra.
        inversion Hcontra; auto. subst.
          by ssromega.
      }
      apply unlift_some in Hcontra. rewrite Hunlift in Hcontra.
      destruct Hcontra;
        by discriminate.
    Qed.

    Lemma add_update_comm:
      forall tp i vf arg pmap c' pmap'
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp vf arg pmap) i),
        addThread (updThread cnti c' pmap') vf arg pmap =
        updThread cnti' c' pmap'.
    Proof.
      intros.
      (* let's box pool and perm_maps in another
                      function to avoid redoing the same proof *)
      pose (fun tp ord => (pool tp ord, perm_maps tp ord)) as p.
      assert (H: p (addThread (updThread cnti c' pmap') vf arg pmap)
                 = p (updThread cnti' c' pmap')).
      { unfold addThread, updThread, p; simpl.
        extensionality ord.
        destruct (unlift (ordinal_pos_incr (num_threads tp)) ord)
          as [o|] eqn:Hunlift.
        rewrite Hunlift.
        destruct ord as [m pfm].
        apply unlift_m_inv in Hunlift.
        simpl in *.
        subst m.
        destruct o as [m pfo].
        destruct (m == i) eqn:Hmi; move/eqP:Hmi=>Hmi.
        subst m.
        erewrite proof_irr with (a1 := pfo) (a2 := cnti).
        unfold eq_op; simpl. rewrite eq_refl; auto.
        unfold eq_op; simpl. rewrite eq_op_false; auto.
        rewrite Hunlift.
        destruct ord as [m pfm].
        assert (Ordinal (n:=(num_threads tp).+1) (m:=m) pfm
                        != Ordinal (n:=(num_threads tp).+1)
                        (m:=i) cnti').
        { apply/eqP; intros Heq.
          inversion Heq; subst.
          assert (Hcontra:
                    (ordinal_pos_incr (num_threads tp)) !=
                                                        (Ordinal (n:=(num_threads tp).+1) (m:=i) pfm)).
          { apply/eqP. intros Hcontra.
            unfold containsThread in *; simpl in *.
            unfold ordinal_pos_incr in Hcontra.
            inversion Hcontra. subst.
              by ssromega.
          }
          apply unlift_some in Hcontra. simpl in Hcontra.
          rewrite Hunlift in Hcontra.
          destruct Hcontra;
            by discriminate.
        }
        unfold eq_op in H|-*.
        apply negb_true_iff in H. rewrite H. auto.
      }
      unfold p in H. simpl in H.
      apply prod_fun in H.
      destruct H as [H1 H2].
      unfold addThread, updThread.
      rewrite H1 H2.
        by reflexivity.
    Qed.

    Lemma add_updateC_comm:
      forall tp i vf arg pmap c'
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp vf arg pmap) i),
        addThread (updThreadC cnti c') vf arg pmap =
        updThreadC cnti' c'.
    Proof.
      intros.
      assert (H: pool (addThread (updThreadC cnti c')
                                 vf arg pmap)
                 = pool (updThreadC cnti' c')).
      { unfold addThread, updThread; simpl.
        extensionality ord.
        destruct (unlift (ordinal_pos_incr (num_threads tp)) ord)
          as [o|] eqn:Hunlift.
        rewrite Hunlift.
        destruct ord as [m pfm].
        apply unlift_m_inv in Hunlift.
        simpl in *.
        subst m.
        destruct o as [m pfo].
        destruct (m == i) eqn:Hmi; move/eqP:Hmi=>Hmi; auto.
        rewrite Hunlift.
        destruct ord as [m pfm].
        assert (Ordinal (n:=(num_threads tp).+1) (m:=m) pfm
                        != Ordinal (n:=(num_threads tp).+1)
                        (m:=i) cnti').
        { apply/eqP; intros Heq.
          inversion Heq; subst.
          assert (Hcontra:
                    (ordinal_pos_incr (num_threads tp)) !=
                                                        (Ordinal (n:=(num_threads tp).+1) (m:=i) pfm)).
          { apply/eqP. intros Hcontra.
            unfold containsThread in *; simpl in *.
            unfold ordinal_pos_incr in Hcontra.
            inversion Hcontra. subst.
              by ssromega.
          }
          apply unlift_some in Hcontra. simpl in Hcontra.
          rewrite Hunlift in Hcontra.
          destruct Hcontra;
            by discriminate.
        }
        apply negb_true_iff in H. rewrite H. auto.
      }
      unfold addThread, updThreadC in *; simpl in *.
      rewrite H.
        by reflexivity.
    Qed.

    Lemma updThread_comm :
      forall tp  i j c pmap c' pmap'
        (Hneq: i <> j)
        (cnti : containsThread tp i)
        (cntj : containsThread tp j)
        (cnti': containsThread (updThread cntj c' pmap') i)
        (cntj': containsThread (updThread cnti c pmap) j),
        updThread cnti' c pmap = updThread cntj' c' pmap'.
    Proof.
      intros.
      unfold updThread. simpl.

      pose (fun tp ord => (pool tp ord, perm_maps tp ord)) as p.
      assert (H: p (updThread cnti' c pmap)
                 = p (updThread cntj' c' pmap')).
      { unfold updThread, p; simpl.
        extensionality ord.
        repeat match goal with
               | [|- context[match ?Expr with _ => _ end]] =>
                 destruct Expr eqn:?
               | [H: _ = true |- _] =>
                 move/eqP:H=>H
               | [H: _ = false |- _] =>
                 move/eqP:H=>H
               end; auto;
          destruct ord;
          try (inversion Heqb0; subst);
          try (inversion Heqb1; subst);
          try(inversion Heqb; subst);
          try by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cnti) in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1.
        erewrite proof_irr with (a1 := i0) (a2 := cntj) in Heqb0;
          by exfalso.
        inversion Heqb2; subst.
        erewrite proof_irr with (a1 := i0) (a2 := cnti') in Heqb;
          by exfalso.
      }
      unfold p in H. simpl in H.
      apply prod_fun in H.
      destruct H as [H1 H2].
      rewrite H1 H2.
        by reflexivity.
    Qed.

    Lemma updThread_updThreadC_comm :
      forall tp i j c pmap' c'
        (Hneq: i <> j)
        (cnti : containsThread tp i)
        (cntj : containsThread tp j)
        (cnti': containsThread (updThread cntj c' pmap') i)
        (cntj': containsThread (updThreadC cnti c) j),
        updThreadC cnti' c = updThread cntj' c' pmap'.
    Proof.
      intros.
      unfold updThread, updThreadC. simpl.
      assert (H: pool (updThreadC cnti' c)
                 = pool (updThread cntj' c' pmap')).
      { unfold updThread, updThreadC; simpl.
        extensionality ord.
        repeat match goal with
               | [|- context[match ?Expr with _ => _ end]] =>
                 destruct Expr eqn:?
               | [H: _ = true |- _] =>
                 move/eqP:H=>H
               | [H: _ = false |- _] =>
                 move/eqP:H=>H
               end; auto;
          destruct ord;
          try (inversion Heqb0; subst);
          try (inversion Heqb1; subst);
          try(inversion Heqb; subst);
          try by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cnti) in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1;
          by exfalso.
        erewrite proof_irr with (a1 := i0) (a2 := cntj') in Heqb1.
        erewrite proof_irr with (a1 := i0) (a2 := cntj) in Heqb0;
          by exfalso.
        inversion Heqb2; subst.
        erewrite proof_irr with (a1 := i0) (a2 := cnti') in Heqb;
          by exfalso.
      }
      simpl in H.
      rewrite H. auto.
    Qed.

    Lemma updThread_same :
      forall tp i (cnti : containsThread tp i),
      updThread cnti (getThreadC cnti) (getThreadR cnti) = tp.
    Proof.
      intros; destruct tp; simpl.
      unfold updThread; simpl; f_equal.
      - extensionality.
        destruct (_ == _) eqn: eq; auto.
        destruct (eqP eq); auto.
      - extensionality.
        destruct (_ == _) eqn: eq; auto.
        destruct (eqP eq); auto.
    Qed.

    Lemma updThread_twice :
      forall tp i (cnti : containsThread tp i) c c' r r'
        (cnti' : containsThread (updThread cnti c r) i),
      updThread cnti' c' r' = updThread cnti c' r'.
    Proof.
      intros; destruct tp; simpl.
      unfold updThread; simpl; f_equal.
      - extensionality.
        destruct (_ == _) eqn: eq; auto.
      - extensionality.
        destruct (_ == _) eqn: eq; auto.
    Qed.

    Lemma updThreadRC : forall tp i (cnti : containsThread tp i) c,
      updThread cnti c (getThreadR cnti) = updThreadC cnti c.
    Proof.
      intros; destruct tp; simpl.
      unfold updThread, updThreadC; simpl; f_equal.
      extensionality.
      destruct (_ == _) eqn: eq; auto.
      destruct (eqP eq); auto.
    Qed.

    Lemma gsoThreadCLPool:
      forall {i tp} c (cnti: containsThread tp i) addr,
        lockRes (updThreadC cnti c) addr = lockRes tp addr.
    Proof.
        by auto.
    Qed.

    Lemma gsoThreadLPool:
      forall {i tp} c p (cnti: containsThread tp i) addr,
        lockRes (updThread cnti c p) addr = lockRes tp addr.
    Proof.
        by auto.
    Qed.

    Lemma gsoAddLPool:
      forall tp vf arg p (addr : address),
        lockRes (addThread tp vf arg p) addr = lockRes tp addr.
    Proof.
      intros.
      unfold addThread, lockRes.
        by reflexivity.
    Qed.

    Lemma gLockSetRes:
      forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
        (cnti': containsThread (updLockSet tp addr res) i),
        getThreadR cnti' = getThreadR cnti.
    Proof.
      intros.
      unfold getThreadR, containsThread. simpl in *.
      do 2 apply f_equal.
        by apply cnt_irr.
    Qed.

    Lemma gLockSetCode:
      forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
        (cnti': containsThread (updLockSet tp addr res) i),
        getThreadC cnti' = getThreadC cnti.
    Proof.
      intros.
      unfold getThreadC, containsThread. simpl in *.
      do 2 apply f_equal.
        by apply cnt_irr.
    Qed.

    Lemma gRemLockSetCode:
      forall {i tp} addr (cnti: containsThread tp i)
        (cnti': containsThread (remLockSet tp addr) i),
        getThreadC cnti' = getThreadC cnti.
    Proof.
      intros.
      unfold getThreadC, containsThread. simpl in *.
      do 2 apply f_equal.
        by apply cnt_irr.
    Qed.

    Lemma gRemLockSetRes:
      forall {i tp} addr (cnti: containsThread tp i)
        (cnti': containsThread (remLockSet tp addr) i),
        getThreadR cnti' = getThreadR cnti.
    Proof.
      intros.
      unfold getThreadR, containsThread. simpl in *.
      do 2 apply f_equal.
        by apply cnt_irr.
    Qed.

    Lemma gssLockRes:
      forall tp addr pmap,
        lockRes (updLockSet tp addr pmap) addr = Some pmap.
    Proof.
      intros.
      unfold lockRes, updLockSet. simpl.
      unfold AMap.find, AMap.add; simpl.
      forget (AMap.this (lockGuts tp)) as el.
      clear. induction el; simpl.
      destruct (AddressOrdered.compare addr addr); address_ordered_auto.
      destruct a.
      destruct (AddressOrdered.compare addr a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare addr addr); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare a a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare addr a); address_ordered_auto.
    Qed.

    Lemma gsoLockRes:
      forall tp addr addr' pmap
        (Hneq: addr <> addr'),
        lockRes (updLockSet tp addr pmap) addr' =
        lockRes tp addr'.
    Proof.
      intros.
      rename addr into a; rename addr' into b.
      unfold lockRes, updLockSet. simpl. destruct tp; simpl. destruct lset0; simpl.
      unfold AMap.find, AMap.add; simpl.
      rename this into el.
      induction el as [ | [c ?]].
      simpl.
      destruct (AddressOrdered.compare b a); address_ordered_auto.
      simpl.
      destruct (AddressOrdered.compare a c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b a); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare c a); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b a); simpl; address_ordered_auto.
      pose proof (AddressOrdered.lt_trans l0 l1); address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      destruct (AddressOrdered.compare b c); simpl; address_ordered_auto.
      apply IHel.
      inv sorted; auto.
    Qed.

    Lemma gssLockSet:
      forall tp b ofs rmap ofs',
        (ofs <= ofs' < ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
        (Maps.PMap.get b (lockSet (updLockSet tp (b, ofs) rmap)) ofs') =
        Some Memtype.Writable.
    Proof.
      intros.
      apply lockSet_spec_2 with ofs; auto.
      red.
      rewrite gssLockRes. reflexivity.
    Qed.

    Lemma gsoLockSet_12 :
      forall tp b b' ofs ofs' pmap,
        ~ adr_range (b,ofs) LKSIZE (b',ofs') ->
        (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b' (lockSet tp)) ofs'.
    Proof.

      intros.
      destruct (lockRes_range_dec tp b' ofs').
      - destruct e as [z [ineq HH]]. unfold LKSIZE in ineq.
        erewrite lockSet_spec_2.
        erewrite lockSet_spec_2; auto.
        + hnf; simpl; eauto.
        + auto.
        + hnf; simpl; eauto.
        + rewrite gsolockResUpdLock; auto.
          intros AA. inversion AA.
          eapply H. unfold adr_range. subst; split; auto.
      - erewrite lockSet_spec_3.
        erewrite lockSet_spec_3; auto.
        intros.
        rewrite gsolockResUpdLock; auto.
        intros AA. inversion AA.
        eapply H. unfold adr_range. subst; split; auto.
    Qed.

    Lemma gsoLockSet_1:
      forall tp b ofs ofs'  pmap
        (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
        (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b (lockSet tp)) ofs'.
    Proof.
      intros.
      apply gsoLockSet_12. intros [? ?]. unfold LKSIZE_nat in *; rewrite Z2Nat.id in Hofs; simpl in *; omega.
    Qed.

    Lemma gsoLockSet_2 :
      forall tp b b' ofs ofs' pmap,
        b <> b' ->
        (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
        (Maps.PMap.get b' (lockSet tp)) ofs'.
    Proof.
      intros.
      apply gsoLockSet_12. intros [? ?]. contradiction.
    Qed.

    Lemma lockSet_updLockSet:
      forall tp i (pf: containsThread tp i) c pmap addr rmap,
        lockSet (updLockSet tp addr rmap) =
        lockSet (updLockSet (updThread pf c pmap) addr rmap).
    Proof.
      intros.
      unfold lockSet, updLockSet, updThread.
      simpl;
        by reflexivity.
    Qed.

    Lemma updThread_lr_valid:
      forall tp i (cnti: containsThread tp i) c' m',
        lr_valid (lockRes tp) ->
        lr_valid (lockRes (updThread cnti c' m')).
    Proof.
      repeat intro.
      rewrite gsoThreadLPool; apply H.
    Qed.

    Lemma contains_iff_num:
      forall tp tp'
        (Hcnt: forall i, containsThread tp i <-> containsThread tp' i),
        num_threads tp = num_threads tp'.
    Proof.
      intros.
      unfold containsThread in *.
      remember (num_threads tp).
      remember (num_threads tp').
      destruct p, p0; simpl in *.
      assert (n = n0).
      clear - Hcnt.
      generalize dependent n0.
      induction n; intros.
      destruct n0; auto.
      destruct (Hcnt 0).
      exfalso.
      specialize (H0 ltac:(ssromega));
        by ssromega.
      destruct n0.
      exfalso.
      destruct (Hcnt 0).
      specialize (H ltac:(ssromega));
        by ssromega.
      erewrite IHn; eauto.
      intros; split; intro H.
      assert (i.+1 < n.+1) by ssromega.
      specialize (fst (Hcnt (i.+1)) H0).
      intros.
      clear -H1;
        by ssromega.
      assert (i.+1 < n0.+1) by ssromega.
      specialize (snd (Hcnt (i.+1)) H0).
      intros.
      clear -H1;
        by ssromega.
      subst.
        by erewrite proof_irr with (a1 := N_pos) (a2 := N_pos0).
    Qed.

    Lemma leq_stepdown:
      forall {m n},
        S n <= m -> n <= m.
    Proof. intros; ssromega. Qed.
    
    Lemma lt_sub:
      forall {m n},
        S n <= m ->
        m - (S n) <  m.
    Proof. intros; ssromega. Qed.

    
    Fixpoint containsList_upto_n (n m:nat): n <= m -> seq.seq (sigT (fun i => i < m)):=
      match n with
      | O => fun _ => nil
      | S n' => fun (H: S n' <= m) =>
                 (existT (fun i => i < m) (m-(S n')) (lt_sub H)) ::
                 (containsList_upto_n n' m) (leq_stepdown H)                                  
      end.

    Lemma containsList_upto_n_spec:
      forall m n (H: n <= m)
        i (cnti:  (fun i => i < m) (m - n + i)),
        i < n ->
        nth_error (containsList_upto_n n m H) i = Some (existT _ (m - n + i) (cnti)). 
    Proof.
      intros.
      remember (n - i) as k.
      assert (HH: n = i + k) by ssromega.
      clear Heqk.
      revert m n H cnti H0 HH.
      induction i.
      intros.
      - destruct n; try (exfalso; ssromega).
        simpl. f_equal.
        eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
        ssromega.
      - intros.
        assert (n = (n - 1).+1) by ssromega.
        revert H cnti .
        dependent rewrite H1.
        intros H cnti.
        simpl.
        rewrite IHi.
        + ssromega.
        + intros. f_equal.
          eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
          clear - H.
          ssromega.
        + ssromega.
        + ssromega.
    Qed.
      
    Lemma leq_refl: forall n, n <= n. Proof. intros; ssromega. Qed.
    
    Definition containsList' (n:nat): seq.seq (sigT (fun i => i < n)):=
      containsList_upto_n n n (leq_refl n).

    Definition contains_from_ineq (tp:t):
        {i : tid & i < num_threads tp } -> {i : tid & containsThread tp i}:=
       fun (H : {i : tid & i < num_threads tp}) =>
         let (x, i) := H in existT (containsThread tp) x i.

    Definition containsList (tp:t): seq.seq (sigT (containsThread tp)):=
      map (contains_from_ineq tp) (containsList' (num_threads tp)).

    Lemma containsList'_spec: forall i n
            (cnti: (fun i => i < n) i),
            List.nth_error (containsList' n) i = Some (existT _ i (cnti)).
    Proof.
      intros.
      unfold containsList'.
      - rewrite containsList_upto_n_spec.
        + simpl in cnti; ssromega.
        + intros. f_equal.
          eapply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat.
          simpl in cnti; ssromega.
        + assumption.
    Qed.

      
    Lemma containsList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (containsList tp) i = Some (existT _ i cnti).
    Proof.
      intros.
      unfold containsList. 
      rewrite list_map_nth containsList'_spec; simpl.
      reflexivity.
    Qed.
      
    Definition indexed_contains tp:= (fun Ncontained: (sigT (containsThread tp)) =>
             let (i, cnti) := Ncontained in getThreadR cnti).
    
    Definition resourceList (tp:t): seq.seq res:=
      map (@indexed_contains tp)
          (containsList tp).

      

    Lemma resourceList_spec: forall i tp
            (cnti: containsThread tp i),
            List.nth_error (resourceList tp) i = Some (getThreadR cnti).
    Proof.
      intros.
      unfold containsThread in cnti.
      destruct tp.
      destruct num_threads0 as [n ?].
      unfold getThreadR; simpl.
      simpl in *.
      induction n.
      - exfalso. ssromega.
      - unfold resourceList.
        rewrite list_map_nth.
        rewrite containsList_spec.
        reflexivity.
    Qed.
        
    Definition OrdinalThreadPool: ThreadPool.ThreadPool :=
      (@ThreadPool.Build_ThreadPool _ _
                                    t
                                    mkPool
                                    containsThread
                                    (@getThreadC) 
                                    (@getThreadR) 
                                    resourceList
                                    lockGuts
                                    lockSet
                                    (@lockRes) 
                                    addThread
                                    (@updThreadC) 
                                    (@updThreadR)
                                    (@updThread) 
                                    updLockSet 
                                    remLockSet 
                                    latestThread 
                                    lr_valid 
                                    (*Find the first thread i, that satisfies (filter i) *)
                                    find_thread
                                    resourceList_spec
                                    containsThread_dec
                                    (*Proof Irrelevance of contains*)
                                    cnt_irr
                                    (@cntAdd)
                                    (@cntAddLatest)
                                    (@cntAdd')
                                    (@cntUpdateC)
                                    (@cntUpdateC')
                                    (@cntUpdateR)
                                    (@cntUpdateR')
                                    (@cntUpdate)
                                    (@cntUpdate')
                                    (@cntUpdateL)
                                    (@cntRemoveL)
                                    (@cntUpdateL')
                                    (@cntRemoveL')
                                    (@gsoThreadLock)
                                    (@gsoThreadCLock)
                                    (@gsoThreadRLock)
                                    (@gsoAddLock)
                                    (@gssAddRes)
                                    (@gssThreadCode)
                                    (@gsoThreadCode)
                                    (@gssThreadRes)
                                    (@gsoThreadRes)
                                    (@gssThreadCC)
                                    (@gsoThreadCC)
                                    (@getThreadCC)
                                    (@gssThreadRR)
                                    (@gsoThreadRR)
                                    (@gThreadCR)
                                    (@gThreadRC)
                                    (@gsoThreadCLPool)
                                    (@gsoThreadLPool)
                                    (@gsoAddLPool)
                                    (@gLockSetRes)
                                    (@gLockSetCode)
                                    (@gssLockRes)
                                    (@gsoLockRes)
                                    (@gssLockSet)
                                    (@gsoLockSet_1)
                                    gsoLockSet_2
                                    lockSet_updLockSet
                                    updThread_updThreadC_comm
                                    updThread_comm
                                    add_updateC_comm
                                    add_update_comm
                                    updThread_lr_valid
                                    lockSet_spec_2
                                    lockSet_spec_3
                                    gsslockSet_rem
                                    gsolockSet_rem1
                                    gsolockSet_rem2
                                    gsslockResUpdLock
                                    gsolockResUpdLock
                                    gsslockResRemLock
                                    gsolockResRemLock
                                    (@ gRemLockSetCode)
                                    (@gRemLockSetRes)
                                    (@gsoAddCode)
                                    (@gssAddCode)
                                    (@gsoAddRes)
                                    updLock_updThread_comm
                                    remLock_updThread_comm
                                    remLock_updThreadC_comm
      ).

  End OrdinalThreadPool.
End OrdinalPool.
