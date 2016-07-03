From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

Require Import compcert.common.Values. (*for val*)
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.pos.
Require Import concurrency.threads_lemmas.
Require Import compcert.lib.Axioms.
Require Import compcert.lib.Axioms.
Require Import concurrency.addressFiniteMap.
Require Import compcert.lib.Maps.
Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.

(*TODO: Enrich Resources interface to enable access of resources*)

Definition empty_lset {lock_info}:AMap.t lock_info:=
  AMap.empty lock_info.

Lemma find_empty:
  forall a l,
    @AMap.find a l empty_lset = None.
      unfold empty_lset.
      unfold AMap.empty, AMap.find; reflexivity.
Qed.

Module OrdinalPool (SEM:Semantics) (RES:Resources) <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES:=RES.
                            
  Module TID:=NatTID.
  Module RES:=RES.
  Module SEM:=SEM.
  Import TID.
  Import SEM.
  Import RES.
  
  Global Notation code:=C.
  
  Record t' := mk
                 { num_threads : pos
                   ; pool :> 'I_num_threads -> @ctl code
                   ; perm_maps : 'I_num_threads -> res
                   ; lset : AMap.t lock_info
                 }.
  
  Definition t := t'.

  Definition lockGuts := lset.
  Definition lockSet (tp:t) := A2PMap (lset tp).

  Definition lockRes t : address -> option lock_info:=
    AMap.find (elt:=lock_info)^~ (lockGuts t).

  (*Fixpoint lockSet_spec': forall js b ofs n,
      (lockSet js) !! b ofs =
      if ssrbool.isSome (lockRes js (b,ofs)) then Some Memtype.Writable else None.
  
  Lemma lockSet_spec: forall js b ofs,
      (lockSet js) !! b ofs =
      if ssrbool.isSome (lockRes js (b,ofs)) then Some Memtype.Writable else None.
  Admitted.*)
Require Import msl.Coqlib2.
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
  simpl.
  destruct (peq b0 b).
  subst b0.
  unfold permissions.setPerm.
  rewrite !PMap.gss.
   repeat (if_tac; auto).
  unfold permissions.setPerm.
  rewrite !PMap.gso;  auto.
Qed.
  
  Lemma lockSet_spec_2 :
    forall (js : t') (b : block) (ofs ofs' : Z),
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
    simpl. unfold permissions.setPerm. rewrite !PMap.gss.
    repeat match goal with |- context [is_left ?A] => destruct A; simpl; auto end.
    omega.
    apply IHel in H0; clear IHel.
    simpl.
    unfold f at 1. destruct a. destruct a.
    unfold permissions.setPermBlock. simpl.
    unfold permissions.setPerm. rewrite !PMap.gss.
    destruct (peq b0 b). subst b0. rewrite !PMap.gss.
    repeat match goal with |- context [is_left ?A] => destruct A; simpl; auto end.
    rewrite !PMap.gso; auto.
  Qed.

  Lemma lockSet_spec_1: forall js b ofs,
      lockRes js (b,ofs) ->
      (lockSet js) !! b ofs = Some Memtype.Writable.
  Proof.
    intros.
    eapply lockSet_spec_2; eauto.
    unfold Intv.In.
    simpl. omega.
  Qed.
    
Open Scope nat_scope.

  Definition containsThread (tp : t) (i : NatTID.tid) : Prop:=
    i < num_threads tp.

  Definition getThreadC {i tp} (cnt: containsThread tp i) : ctl :=
    tp (Ordinal cnt).
  
  Definition getThreadR {i tp} (cnt: containsThread tp i) : res :=
    (perm_maps tp) (Ordinal cnt).

  Definition latestThread tp := n (num_threads tp).

  Definition addThread (tp : t) (vf arg : val) (pmap : res) : t :=
    let: new_num_threads := pos_incr (num_threads tp) in
    let: new_tid := ordinal_pos_incr (num_threads tp) in
    mk new_num_threads
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
           | None => Kinit vf arg  (*Could be a new state Kinit?? *)
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
 pose proof (AddressOrdered.lt_trans l0 l1).
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
 assert (forall y, SetoidList.InA (@AMap.Raw.PX.eqk _) y l -> AMap.Raw.PX.ltk (b,l0) y).
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

  Lemma lockSet_upd: forall ds b ofs pmap,
      lockSet (updLockSet ds (b, ofs) pmap) =
      permissions.setPerm (Some Memtype.Writable) b ofs (lockSet ds).
  Proof.
    intros.
   unfold lockSet, updLockSet; simpl.
  unfold A2PMap.
 match goal with |- fold_left ?F ?Z _ = _ => set (f:=F) end.
 unfold lockGuts.
 unfold AMap.elements.
 rewrite <- !List.fold_left_rev_right. simpl.
 forget (AMap.this (lset ds)) as el.
 unfold permissions.setPerm.
 induction el as [ | [a ?]].
 simpl.
 (* NOT TRUE!
  updLockSet changes permissions at 4 locations (starting at ofs),
 but setPerm changes permissions only at 1 location (at ofs).
 *)

  Admitted.

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

 Lemma gsslockSet_rem': forall ds b ofs,
      (lockSet (remLockSet ds (b, ofs))) !! b ofs =
      None.
  Proof.
    intros.
   unfold lockSet, remLockSet; simpl.
 (* NOT TRUE: Suppose address 100 and 102 are in the lock set.
  Then "remove" address 102, but the permission at 102 is still Writable.
*)

(*
 unfold A2PMap, AMap.remove; simpl.
 destruct ds; simpl. destruct lset0; simpl.
 rewrite <- !List.fold_left_rev_right.
 match goal with |- context [fold_right ?F] => set (f:=F) end.
 assert (SetoidList.NoDupA (@AMap.Raw.PX.eqk _) this). 
 apply SetoidList.SortA_NoDupA with (@AMap.Raw.PX.ltk _); auto with typeclass_instances.
 clear sorted.*)
(*
 pose proof (@AMap.remove_1 _ (lockGuts ds) (b,ofs) (b,ofs)).
 spec H; [reflexivity |].
 unfold A2PMap.
 forget (AMap.remove (elt:=lock_info) (b, ofs) (lockGuts ds)) as m.
 rewrite <- !List.fold_left_rev_right.
 unfold AMap.In in H. unfold AMap.elements.
 unfold AMap.Raw.elements.
 assert (~ AMap.Raw.PX.In (b, ofs) (rev (AMap.this m)))
   by (contradict H; rewrite PX_in_rev; auto).
 clear H. forget (rev (AMap.this m)) as el.
 match goal with |- context [fold_right ?F] => set (f:=F) end.
 induction el; simpl. rewrite PMap.gi; auto.
 destruct a. destruct a.
 destruct (EqDec_address (b0,z) (b,ofs)). inv e.
 unfold f at 1.
 simpl.
 contradiction H0. eauto.
 unfold f at 1. simpl.
 unfold permissions.setPerm.
 rewrite !PMap.gss.
 destruct (peq b0 b). subst b0. rewrite !PMap.gss.
 
 *)

  Admitted.

  Lemma gsslockSet_rem: forall ds b ofs ofs0,
      Intv.In ofs0 (ofs, ofs + lksize.LKSIZE)%Z ->
      (lockSet (remLockSet ds (b, ofs))) !! b ofs0 =
      None.
  Proof.
    intros.
  hnf in H. simpl in H.
 (* NOT TRUE.  See lemma just above *)
  Admitted.
  
  Lemma gsolockSet_rem1: forall ds b ofs b' ofs',
      b  <> b' ->
      (lockSet (remLockSet ds (b, ofs))) !! b' ofs' =
      (lockSet ds)  !! b' ofs'.
  Proof.
    intros.
   unfold lockSet, remLockSet. simpl.
 unfold A2PMap.
 rewrite <- !List.fold_left_rev_right.
 match goal with |- context [fold_right ?F] => set (f:=F) end.
 simpl. unfold AMap.elements, AMap.Raw.elements.
 unfold lockGuts. 
   (* NOT TRUE.  See lemmas just above *)
  Admitted.

  Lemma gsolockSet_rem2: forall ds b ofs ofs',
      ~ Intv.In ofs' (ofs, ofs + lksize.LKSIZE)%Z ->
      (lockSet (remLockSet ds (b, ofs))) !! b ofs' =
      (lockSet ds)  !! b ofs'.
  Proof.
    intros. (* NOT TRUE.  See lemmas just above *)
  Admitted.

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
    getThreadC cntj' = if eq_tid_dec i j then c' else getThreadC cntj.
  Proof.
    destruct (eq_tid_dec i j); subst;
    [rewrite gssThreadCC |
     erewrite <- @gsoThreadCC with (cntj := cntj)];
    now eauto.
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
    forall {i tp} (cnt: containsThread tp i) vf arg pmap j
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
      by erewrite proof_irr with (a1 := i0) (a2:= cntj).
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
      ~ adr_range (b,ofs) 4 (b',ofs') -> 
      (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
      (Maps.PMap.get b' (lockSet tp)) ofs'.
  Proof.
   intros.
   simpl in *. unfold lockSet, updLockSet. simpl.
   unfold A2PMap, AMap.add. simpl.
  rewrite <- !List.fold_left_rev_right.
  match goal with |- context [fold_right ?F _ ?B] => set (f:=F) end.
  unfold lockGuts; simpl. unfold AMap.elements; simpl.
  forget (AMap.this (lset tp)) as el.
  unfold AMap.Raw.elements.
  (* THIS IS DOUBTFUL, for the same reason about overlapping locks
    as some of the lemmas above *)
  Admitted.

  Lemma gsoLockSet_1 :
    forall tp b ofs ofs'  pmap
      (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
      (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
      (Maps.PMap.get b (lockSet tp)) ofs'.
  Proof.
    intros.
    apply gsoLockSet_12. intros [? ?]. simpl in Hofs; omega.
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
    
End OrdinalPool.
  