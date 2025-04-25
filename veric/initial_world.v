From iris.algebra Require Import agree.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From iris_ora.algebra Require Import agree.
Require Import VST.zlist.sublist.
Require Import VST.shared.shared.
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.shared.resource_map.
Require Import VST.veric.seplog.
Require Import VST.veric.shares.
Require Import VST.shared.dshare.
Require Import VST.veric.mpred.
Require Import VST.veric.mapsto_memory_block.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Import Values.

Open Scope maps.

Lemma adr_range_divide:
  forall b i p q loc,
    p >= 0 -> q >= 0 -> (adr_range (b,i) (p+q) loc <-> (adr_range (b,i) p loc \/ adr_range (b,i+p) q loc)).
Proof.
split; intros.
destruct loc as [b' z']; destruct H1.
assert (i <= z' < i+p \/ i+p <= z' < i+p+q)  by lia.
destruct H3; [left|right]; split; auto; lia.
destruct loc as [b' z']; destruct H1; destruct H1; split; auto; lia.
Qed.

Lemma store_init_data_outside':
  forall F V (ge: Genv.t F V)  b a m p m',
  Genv.store_init_data ge m b p a = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + init_data_size a) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ nextblock m = nextblock m'.
Proof.
intros.
  unfold max_access_at. simpl.
  destruct a; simpl in H; try apply store_outside' in H; auto.
  inv H; auto.
  invSome. apply store_outside' in H2; auto.
Qed.

Lemma store_init_data_list_outside':
  forall F V (ge: Genv.t F V)  b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + init_data_list_size il) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ nextblock m = nextblock m'.
Proof.
  induction il; simpl; intros.
  inv H; auto.
  invSome.
  specialize (IHil _ _ _ H2).
  destruct IHil as [? [? ?]].
  rewrite <- H3; rewrite <- H1; clear H3 H1 H2.
  remember (init_data_list_size il) as n.
  assert (n >= 0).
  subst n; clear; induction il; simpl; try lia.
  generalize (init_data_size_pos a); lia.
  clear il Heqn.
  apply store_init_data_outside' in H.
  generalize (init_data_size_pos a); intro.
  destruct H as [? [? ?]]; repeat split; auto.
  clear H3 H4.
  intros. specialize (H0 b' ofs); specialize (H b' ofs).
  destruct H0.
  destruct H0; left; split; auto; lia.
  rewrite <- H0.
  destruct H.
  destruct H; left; split; auto; lia.
  right. auto.
Qed.

Lemma split_top_neq: fst (Share.split Share.top) <> Share.top.
Proof.
case_eq (Share.split Share.top); intros; simpl.
eapply nonemp_split_neq1; eauto.
Qed.

Section mpred.

Context `{!heapGS Σ}.

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
intros. rewrite fold_left_rev_right.
f_equal; extensionality x y; auto.
Qed.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , init_data_list_size (gvar_init l)) end.

Lemma initblocksize_name: forall V a id n, initblocksize V a = (id,n) -> fst a = id.
Proof. destruct a; intros; simpl; inv H; auto.  Qed.

Fixpoint find_id {A} (id: ident) (G: list (ident * A)) : option A  :=
 match G with
 | (id', f)::G' => if eq_dec id id' then Some f else find_id id G'
 | nil => None
 end.

Lemma in_map_fst: forall {A B: Type} (i: A) (j: B) (G: list (A*B)),
  In (i,j) G -> In i (map (@fst _ _ ) G).
Proof.
 induction G; simpl; intros; auto.
 destruct H; [left|right]. subst; simpl; auto. auto.
Qed.

Lemma find_id_i {A}:
  forall id fs G,
            In (id,fs) G ->
             list_norepet (map (@fst _ _) G) ->
                  @find_id A id G = Some fs.
Proof.
induction G; simpl; intros.
contradiction.
destruct H. subst. rewrite if_true; auto.
inv H0.
destruct a as [i j].
if_tac.
subst i.
simpl in *; f_equal.
apply in_map_fst in H. contradiction.
auto.
Qed.

Lemma find_id_e {A}:
   forall id G fs, @find_id A id G = Some fs -> In (id,fs) G.
Proof.
 induction G; simpl; intros. inv H. destruct a. if_tac in H.
 inv H; subst; auto. right; apply (IHG fs); auto.
Qed.

Lemma find_id_In_map_fst {A} i t: forall V (Hi: @find_id A i V = Some t), In i (map fst V).
Proof.
induction V; simpl; intros. inv Hi.
destruct a as [j u]; simpl. unfold eq_dec, EqDec_ident, ident_eq in Hi.
destruct (peq i j); subst; [left | right]; auto.
Qed.

Lemma find_id_app {A} i fs: forall G1 G2 (G: find_id i (G1 ++ G2) = Some fs),
@find_id A i G1 = Some fs \/ find_id i G2 = Some fs.
Proof. induction G1; simpl; intros. right; trivial. 
destruct a. destruct (eq_dec i i0); [ left; trivial | eauto].
Qed.

Lemma find_id_app1 {A} i x G2: forall G1, find_id i G1 = Some x -> @find_id A i (G1++G2) = Some x.
  Proof.
    induction G1; simpl; intros. inv H.
    destruct a. destruct (eq_dec i i0); [trivial | auto].
  Qed.

Lemma find_id_app2 {A} i x G2: forall G1, list_norepet (map fst (G1++G2)) ->
                   find_id i G2 = Some x -> @find_id A i (G1++G2) = Some x.
  Proof.
    induction G1; simpl; intros. trivial. 
    destruct a. inv H. destruct (eq_dec i i0); [subst i0; elim H3; clear - H0 | auto].
    apply find_id_e in H0. apply (in_map fst) in H0.
    rewrite map_app. apply in_or_app; right. apply H0.
  Qed.

Section inflate.
(* build an initial resource map from a CompCert memory, including funspecs *)
Variable (m: mem) (block_bounds: block -> (Z * nat)).
Context {F} (ge: Genv.t (fundef F) type) (G: funspecs(Σ := Σ)).

Definition funspec_of_loc loc := if eq_dec loc.2 0 then
  match Genv.invert_symbol ge loc.1 with
  | Some id => find_id id G
  | None => None
  end else None.

Definition inflate_loc loc := 
  match access_at m loc Cur with
  | Some Freeable => loc ↦ VAL (contents_at m loc)
  | Some Writable => loc ↦{#Ews} VAL (contents_at m loc)
  | Some Readable => loc ↦{#Ers} VAL (contents_at m loc)
  | Some Nonempty => match funspec_of_loc loc with
                     | Some f => func_at f loc
                     | _ => mapsto_no loc Share.bot
                     end
  | _ => mapsto_no loc Share.bot
  end.

Lemma readable_Ews : readable_share Ews.
Proof. auto. Qed.

Definition res_of_loc (loc : address) : sharedR (leibnizO resource) :=
  match access_at m loc Cur with
  | Some Freeable => (shared.YES(V := leibnizO resource) (DfracOwn (Share Tsh)) readable_top (to_agree (VAL (contents_at m loc))))
  | Some Writable => (shared.YES(V := leibnizO resource) (DfracOwn (Share Ews)) readable_Ews (to_agree (VAL (contents_at m loc))))
  | Some Readable => (shared.YES(V := leibnizO resource) (DfracOwn (Share Ers)) readable_Ers (to_agree (VAL (contents_at m loc))))
  | Some Nonempty => match funspec_of_loc loc with
                     | Some _ => (shared.YES(V := leibnizO resource) (DfracBoth (Share Share.bot)) I (to_agree FUN))
                     | _ => (shared.NO (Share Share.bot) bot_unreadable)
                     end
  | _ => (shared.NO (Share Share.bot) bot_unreadable)
  end.

(* Put an extra NO Share.bot on the end to avoid problems with size-0 gvars. *)
Definition rmap_of_mem : gmapR address (sharedR (leibnizO resource)) :=
  [^op list] n ∈ seq 1 (Pos.to_nat (Mem.nextblock m) - 1),
  let b := Pos.of_nat n in let '(lo, z) := block_bounds b in
  [^op list] o ∈ seq 0 (z + 1), let loc := (b, lo + Z.of_nat o)%Z in {[loc := res_of_loc loc]}.

Definition inflate_initial_mem : mpred :=
  [∗ list] n ∈ seq 1 (Pos.to_nat (Mem.nextblock m) - 1),
  let b := Pos.of_nat n in let '(lo, z) := block_bounds b in
  [∗ list] o ∈ seq 0 (z + 1), let loc := (b, lo + Z.of_nat o)%Z in inflate_loc loc.

(* What do we actually need this for?
Definition all_VALs := ∀ l dq r, <absorb> l ↦{dq} r → ⌜∃ v, r = VAL v⌝.

Lemma inflate_initial_mem_all_VALs: inflate_initial_mem ⊢ all_VALs.
Proof.
  rewrite /inflate_initial_mem /all_VALs.
  iIntros "H" (???); iApply (bi.impl_intro_r with "H"); iIntros "H".
  forget (Pos.to_nat (nextblock m) - 1) as n; iInduction n as [|] "IH".
  { simpl. Search bi_affinely bi_absorbingly.
Search emp.
Abort.
*)

Definition initial_core : mpred :=
  [∗ list] n ∈ seq 1 (Pos.to_nat (Mem.nextblock m) - 1),
  let b := Pos.of_nat n in
  match funspec_of_loc (b, 0) with
  | Some f => func_at f (b, 0)
  | None => mapsto_no (b, 0) Share.bot
  end.

Global Instance initial_core_affine : Affine initial_core.
Proof.
  apply big_sepL_affine; intros ??.
  destruct (funspec_of_loc _); apply _.
Qed.

End inflate.

Lemma list_disjoint_rev2:
   forall A (l1 l2: list A), list_disjoint l1 (rev l2) = list_disjoint l1 l2.
Proof.
intros.
unfold list_disjoint.
apply Axioms.prop_ext; split; intros; eapply H; eauto.
rewrite <- In_rev; auto.
rewrite In_rev; auto.
Qed.

(*Lemma writable_blocks_app:
  forall bl bl' rho, writable_blocks (bl++bl') rho = writable_blocks bl rho * writable_blocks bl' rho.
Proof.
induction bl; intros.
simpl; rewrite emp_sepcon; auto.
simpl.
destruct a as [b n]; simpl.
rewrite sepcon_assoc.
f_equal.
apply IHbl.
Qed.*)

Fixpoint prog_funct' {F V} (l: list (ident * globdef F V)) : list (ident * F) :=
 match l with nil => nil | (i,Gfun f)::r => (i,f):: prog_funct' r | _::r => prog_funct' r
 end.

Definition prog_funct {F} (p: program F) := prog_funct' (prog_defs p).

Lemma find_symbol_add_globals_nil:
  forall {F V} i g id p prog_pub,
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p)).
Proof. intros. simpl.
       unfold Genv.find_symbol, Genv.add_global in *; simpl.
      destruct (eq_dec i id); subst.
        rewrite Maps.PTree.gss. intuition. congruence.
        rewrite -> Maps.PTree.gso by auto. split; intro Hx.
        rewrite Maps.PTree.gempty in Hx; inv Hx.
         inv Hx.
Qed.

Lemma find_symbol_add_globals_cons:
  forall {F V} i g id dl prog_pub (HD: 0 < Zlength dl),
   ~ In i (map fst dl) -> list_norepet (map fst dl) ->
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id).
Proof.
intros.
  assert (Genv.genv_next (Genv.empty_genv F V prog_pub) = 1%positive)  by reflexivity.
  assert (Genv.find_symbol (Genv.empty_genv F V prog_pub)  id = None) by (intros; apply Maps.PTree.gempty).
 forget (Genv.empty_genv F V prog_pub) as ge.
 forget (1%positive) as n.
  revert ge n H H0 H1 H2 HD; induction dl; intros.
  (*base case*)
        simpl in *. rewrite Zlength_nil in HD. lia.
  (*induction step*)
        simpl; auto.
        rewrite -> Zlength_cons in *.
        destruct a as [a ag]; simpl in *.
        destruct dl.
          simpl in *. clear IHdl.
          assert (a<>i /\ ~ False) by (clear - H; intuition).
          clear H; destruct H3.
          destruct (eq_dec id a).
            subst id. unfold Genv.find_symbol, Genv.add_global; simpl.
              rewrite Maps.PTree.gso; trivial. rewrite H1.
              rewrite Maps.PTree.gss.
              split; intro; try congruence. assert (n = n+1)%positive. clear - H4. congruence. lia.
          unfold Genv.find_symbol, Genv.add_global; simpl.
            rewrite H1.
            destruct (eq_dec id i).
              subst i.
              rewrite Maps.PTree.gss. rewrite Pplus_one_succ_r.
                split; intro; try congruence. trivial.
              rewrite Maps.PTree.gso; trivial.
              rewrite Maps.PTree.gso; trivial.
              unfold Genv.find_symbol in H2. rewrite H2.
              split; intros. congruence. subst. exfalso. apply n1; trivial.

        replace ((n + Z.to_pos (Z.succ (Zlength (p :: dl))))%positive) with
          ((Pos.succ n) + Z.to_pos (Zlength (p ::dl)))%positive.
        2: { clear - n dl. rewrite Z2Pos.inj_succ.
                   rewrite Pplus_one_succ_r. rewrite Pplus_one_succ_l.
                     rewrite Pos.add_assoc. trivial.
                   rewrite Zlength_correct. simpl. lia. }
        simpl in H0. inv H0.
        assert (a<>i /\ ~ In i (map fst (p::dl))) by (clear - H; intuition).
        clear H; destruct H0.
        destruct (eq_dec id a).
         subst id.
         split; intro; try congruence. exfalso.
         clear IHdl.
         assert (~In a (map fst (((p::dl)++(i,g)::nil)))).
             rewrite map_app. rewrite in_app_iff.
             intros [?|?]; try contradiction.
             simpl in H3. destruct H3; try congruence.
         forget ((p::dl) ++ (i, g) :: nil) as vl.
         assert (Genv.find_symbol (Genv.add_global ge (a,ag)) a = Some (Genv.genv_next ge)).
            unfold Genv.find_symbol, Genv.add_global; simpl. rewrite Maps.PTree.gss; auto.

         forget (Genv.add_global ge (a,ag)) as ge1.
         forget (Genv.genv_next ge) as N; clear ge H2.
         assert (Pos.succ N + Z.to_pos (Zlength (p :: dl)) > N)%positive by lia.
         forget (Pos.succ N + Z.to_pos (Zlength (p :: dl)))%positive as K.
         clear - H1 H3 H2 H4.
         revert ge1 K H2 H1 H3 H4; induction vl; simpl; intros.
            inversion2 H1 H4; lia.
         apply (IHvl (Genv.add_global ge1 a0) K H2); auto.
           unfold Genv.find_symbol, Genv.add_global in H4|-*; simpl in *.
           rewrite Maps.PTree.gso; auto.


         apply IHdl; auto.
        unfold Genv.find_symbol, Genv.add_global in H2|-*; simpl.
                 rewrite Maps.PTree.gso; auto.
                   rewrite Zlength_correct. simpl. lia.
Qed.

Lemma find_symbol_add_globals:
  forall {F V} i g id dl prog_pub,
   ~ In i (map fst dl) -> list_norepet (map fst dl) ->
  match dl with
    nil => forall p,
      (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p))
  | _ =>
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id)
  end.
Proof.
intros.
destruct dl.
  intros; apply find_symbol_add_globals_nil.
  apply find_symbol_add_globals_cons; trivial.
    rewrite Zlength_correct. simpl. lia.
Qed.


Lemma find_symbol_add_globals':
  forall {F V} i g id dl prog_pub,
  match dl with
    nil => forall p,
      (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p))
  | _ =>
     ~ In i (map fst dl) -> list_norepet (map fst dl) ->
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id)
  end.
Proof.
intros.
destruct dl.
  intros; apply find_symbol_add_globals_nil.
  apply find_symbol_add_globals_cons; trivial.
    rewrite Zlength_correct. simpl. lia.
Qed.

Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.

Lemma nth_error_rev:
  forall T (vl: list T) (n: nat),
   (n < length vl)%nat ->
  nth_error (rev vl) n = nth_error vl (length vl - n - 1).
Proof.
 induction vl; simpl; intros. apply nth_error_nil.
 destruct (eq_dec n (length vl)).
 subst.
 pattern (length vl) at 1; rewrite <- rev_length.
 rewrite <- (Nat.add_0_r (length (rev vl))).
 rewrite nth_error_app.
 case_eq (length vl); intros. simpl. auto.
 simpl. replace (S n - n - 1)%nat with O by lia.
 simpl; auto.
 rewrite -> nth_error_app1 by (rewrite rev_length; lia).
 rewrite -> IHvl by lia. clear IHvl.
 destruct n; destruct (length vl). congruence.
 simpl. replace (n-0)%nat with n by lia; auto.
 lia.
 simpl; replace (S n1 - n - 1)%nat with (S (S n1 - S n - 1))%nat by lia.
 reflexivity.
Qed.

(*Partial attempt at porting add_globals_hack*)
Lemma add_globals_hack_nil {F}:
   forall gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (rev nil) ->
   forall id, Genv.find_symbol gev id = None.
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl. apply Maps.PTree.gempty.
Qed.

Lemma add_globals_hack_single {F}:
   forall v gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (cons v nil) ->
   forall id b, (Genv.find_symbol gev id = Some b <-> fst v = id /\ b = 1%positive).
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl.
  destruct (peq (fst v) id).
     subst id. rewrite Maps.PTree.gss.
       split; intros. split; trivial. congruence.
       destruct H; subst. trivial.
  rewrite Maps.PTree.gso.
    split; intros. rewrite Maps.PTree.gempty in H. inv H.
    destruct H; subst. congruence.
  auto.
Qed.

Lemma advance_next_length:
  forall F V vl n, @Genv.advance_next F V vl n = (Pos.of_nat (S (length vl)) + n - 1)%positive.
Proof.
 unfold Genv.advance_next; induction vl; simpl fold_left; intros.
  simpl Pos.of_nat. rewrite Pos.add_comm. symmetry. apply Pos.add_sub.
  simpl length. rewrite IHvl. rewrite Pplus_one_succ_l.
  f_equal.
  symmetry; rewrite -> Nat2Pos.inj_succ by lia.
  rewrite Pplus_one_succ_r. symmetry; apply Pos.add_assoc.
Qed.

Lemma Zpos_Posofnat: forall n, (n>0)%nat -> Z.pos (Pos.of_nat n) = Z.of_nat n.
Proof.
 intros. destruct n. lia. simpl  Z.of_nat. f_equal. lia.
Qed.

Lemma add_globals_hack {F}:
   forall vl gev prog_pub,
    list_norepet (map fst vl) ->
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (rev vl) ->

   (forall id b, 0 <= Zpos b - 1 < Zlength vl ->
                           (Genv.find_symbol gev id = Some b <->
                            nth_error (map (@fst _ _) vl) (length vl - Pos.to_nat b) = Some id)).
Proof. intros. subst.
     apply iff_trans with (nth_error (map fst (rev vl)) (Z.to_nat (Zpos b - 1)) = Some id).
   2: {
     rewrite map_rev; rewrite nth_error_rev.
             replace (length (map fst vl) - Z.to_nat (Zpos b - 1) - 1)%nat
                        with (length vl - Pos.to_nat b)%nat ; [intuition | ].
    rewrite map_length.
    transitivity (length vl - (Z.to_nat (Z.pos b-1)+1))%nat; try lia.
    rewrite map_length.
    rewrite Zlength_correct in H1.
    forget (Z.pos b-1) as i; forget (length vl) as n; clear - H1.
    apply inj_lt_rev. rewrite Z_to_nat_max; auto.
    rewrite (Coqlib.Zmax_spec i 0). if_tac; lia.
  }
  rename H1 into Hb; revert H; induction vl; simpl rev; simpl map;
       simpl Genv.find_symbol; intros;
       try rewrite Zlength_nil in *.
      unfold Genv.find_symbol. rewrite Maps.PTree.gempty.
     intuition auto; try done. rewrite -> nth_error_nil in *; done.
       destruct a. inv H. rewrite Zlength_cons in Hb.
       destruct (eq_dec (Z.pos b-1) (Zlength vl)).
        clear IHvl Hb. rewrite e. rewrite Zlength_correct.
        rewrite Nat2Z.id.
        replace b with (Z.to_pos (1+ (Zlength vl)))
          by (rewrite <- e; replace (1 + (Z.pos b - 1)) with (Z.pos b) by lia;
                  apply Pos2Z.id).
        clear e b.
        rewrite <- Zlength_rev. rewrite <- rev_length.
         replace (length (rev vl)) with (length (rev vl) + 0)%nat by lia.
         rewrite map_app. rewrite <- map_length with (f:=@fst ident (globdef (fundef F) type)).
        rewrite nth_error_app.
        apply iff_trans with (i=id); [ | simpl; split; intro; subst; auto; inv H; auto].
        rewrite In_rev in H2. rewrite <- map_rev in H2.
       rewrite <- list_norepet_rev in H3. rewrite <- map_rev in H3.
         forget (rev vl) as dl.
    assert (FSA := find_symbol_add_globals i g  id _ prog_pub H2 H3).
    { destruct dl.
      rewrite (FSA (Z.to_pos (1 + Zlength (@nil (ident * globdef (fundef F) type))))).
      simpl. intuition.
      replace (Z.to_pos (1 + Zlength (p :: dl))) with (1 + Z.to_pos (Zlength (p :: dl)))%positive ; auto.
      clear.
      rewrite Zlength_cons.      rewrite Zlength_correct.
      rewrite Z2Pos.inj_add; try solve [simpl; lia].
    }
    spec IHvl ; [ lia |].
    specialize (IHvl H3).
    rewrite Genv.add_globals_app.
    unfold Genv.add_globals at 1. simpl fold_left.
    unfold Genv.find_symbol, Genv.add_global.
    simpl Genv.genv_symb.
    destruct (eq_dec id i).
    + subst i. rewrite Maps.PTree.gss.
      rewrite Genv.genv_next_add_globals.
      rewrite advance_next_length.
      simpl Genv.genv_next.
      rewrite map_app.
      rewrite In_rev in H2. rewrite <- map_rev in H2. rewrite Pos.add_sub.
      split; intro.
      - assert (H': b = Pos.of_nat (S (length (rev vl)))) by congruence.
        clear H; rename H' into H.
          subst b. exfalso; apply n; clear.
          rewrite <- Zlength_rev. rewrite Zlength_correct. forget (length (rev vl)) as i.
          rewrite -> Zpos_Posofnat by lia. rewrite Nat2Z.inj_succ. unfold Z.succ.  lia.
     - exfalso.
       assert (Z.pos b-1 >= 0) by (clear - Hb; lia).
       pose proof (Z2Nat.id _ (Z.ge_le _ _ H0)).
       clear - H1 H H2 n.
       rewrite Zlength_correct in n. apply n. clear n.
       rewrite <- H1.
       f_equal. clear - H H2.
       forget (Z.to_nat (Z.pos b-1)) as j.
       replace (length vl) with (length (map fst (rev vl)))
           by (rewrite map_length; rewrite rev_length; auto).
       forget (map fst (rev vl)) as al.
       revert al H2 H; clear; induction j; destruct al; simpl; intros; auto. inv H; intuition.
       exfalso; clear - H; induction j; inv H; auto.
       f_equal. apply IHj; auto.
    + rewrite -> Maps.PTree.gso by auto.
      rewrite map_app.
      destruct IHvl.
      split; intro.
      - apply H in H1. rewrite nth_error_app1; auto.
        clear - n Hb. rewrite map_length. rewrite rev_length. rewrite Zlength_correct in Hb,n.
        assert (Z.pos b-1>=0) by lia.
        pose proof (Z2Nat.id _ (Z.ge_le _ _ H)).
        forget (Z.to_nat(Z.pos b-1)) as j. rewrite <- H0 in *.
        destruct Hb. clear - H2 n. lia.
      - assert (Z.to_nat (Z.pos b-1) < length (map (@fst _ _) (rev vl)))%nat.
        { clear - Hb n H1.
          rewrite Zlength_correct in n. rewrite map_length; rewrite rev_length.
          assert (Z.to_nat (Z.pos b-1) <> length vl).
          { contradict n. rewrite <- n.
            rewrite Z2Nat.id; auto. lia. }
          forget (Z.to_nat (Z.pos b-1)) as j.
          clear - H1 H.
          assert (S (length vl) = length (map fst (rev vl) ++ map fst ((i, g) :: nil))).
          { simpl. rewrite app_length; rewrite map_length; rewrite rev_length; simpl; lia. }
          assert (j < S (length vl))%nat; [ | lia].
          rewrite H0. forget (map fst (rev vl) ++ map fst ((i, g) :: nil)) as al.
          clear - H1. revert al H1; induction j; destruct al; simpl in *; intros; inv H1; auto; try lia.
          specialize (IHj _ H0); lia. }
        rewrite -> nth_error_app1 in H1 by auto.
        apply H0 in H1. auto.
Qed.

Lemma find_symbol_globalenv {F}:
  forall (prog: program F) i b,
   list_norepet (prog_defs_names prog) ->
  Genv.find_symbol (Genv.globalenv prog) i = Some b ->
  0 < Z.pos b <= Z_of_nat (length (prog_defs prog)) /\
  exists d, nth_error (prog_defs prog) (Z.to_nat (Z.pos b-1)) = Some (i,d).
Proof.
intros.
unfold Genv.globalenv in H0.
change (AST.prog_public prog) with (prog_public prog) in H0.
change (AST.prog_defs prog) with (prog_defs prog) in H0.
assert (RANGE: 0 <= Z.pos b - 1 < Zlength (rev (prog_defs prog))). {
 rewrite <- (rev_involutive (prog_defs prog)) in H0.
 clear - H0.
 revert H0; induction (rev (prog_defs prog));  simpl Genv.find_symbol; intros.
 unfold Genv.find_symbol in H0. simpl in H0. rewrite Maps.PTree.gempty in H0; inv H0.
 rewrite Genv.add_globals_app in H0.
 simpl in H0. destruct a.
 destruct (eq_dec i0 i). subst.
 unfold Genv.add_global, Genv.find_symbol in H0. simpl in H0.
 rewrite Maps.PTree.gss in H0. inv H0.
 clear.
 split.
 match goal with |- _ <= Z.pos ?A - _ => pose proof (Zgt_pos_0  A); lia end.
 rewrite Zlength_cons.
 induction l. rewrite Zlength_nil /=. lia.
 rewrite Zlength_cons.
 rewrite /= Genv.add_globals_app.
   simpl Genv.genv_next.
 match goal with |- context [Pos.succ ?J] =>
  forget J as j
 end.
 clear - IHl.
 replace (Z.pos (Pos.succ j) - 1) with (Z.succ (Z.pos j - 1)). lia.
  unfold Z.succ.  rewrite Pos2Z.inj_succ.  lia.
 unfold Genv.add_global, Genv.find_symbol in IHl, H0. simpl in H0.
 rewrite -> Maps.PTree.gso in H0 by auto.
 apply IHl in H0.
 rewrite Zlength_cons. lia.
 }
 split.
 rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE. lia.
 rewrite <- list_norepet_rev in H.
 unfold prog_defs_names in H.
 change (AST.prog_defs prog) with (prog_defs prog) in H.
 rewrite <- map_rev in H.
 rewrite add_globals_hack in H0; [ | apply H | rewrite rev_involutive; auto | auto ].
 rewrite map_rev in H0.
 rewrite nth_error_rev in H0.
 rewrite list_map_nth in H0.
 match type of H0 with option_map _ ?A = _ =>
   revert H0; case_eq A; intros
 end.
 destruct p; simpl in H1. inv H1.
 exists g.
 rewrite <- H0. f_equal.
 rewrite rev_length. rewrite map_length.
 clear - RANGE.
 rewrite Zlength_rev in RANGE. rewrite Zlength_correct in RANGE.
 rewrite <- (Z2Nat.id (Z.pos b)) in * by lia.
 rewrite -> Z2Nat.inj_pos in *.
 forget (Pos.to_nat b) as n. clear b.
 replace (Z.of_nat n - 1) with (Z.of_nat (n-1)) by (rewrite -> inj_minus1 by lia; f_equal; auto).
 rewrite Nat2Z.id.
 lia.
 inv H1.
 rewrite rev_length. rewrite map_length.
 clear - RANGE. rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE.
 forget (length (prog_defs prog)) as N.
 assert (Z_of_nat N > 0) by lia.
 destruct N; inv H.
 assert (Pos.to_nat b > 0)%nat; [apply Pos2Nat.is_pos| lia].
Qed.

Fixpoint alloc_globals_rev {F V} (ge: Genv.t F V) (m: mem) (vl: list (ident * globdef F V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
     match alloc_globals_rev ge m vl' with
     | Some m' => Genv.alloc_global ge m' v
     | None => None
     end
  end.

Lemma alloc_globals_app:
   forall F V (ge: Genv.t F V) m m2 vs vs',
  Genv.alloc_globals ge m (vs++vs') = Some m2 <->
    exists m', Genv.alloc_globals ge m vs = Some m' /\
                    Genv.alloc_globals ge m' vs' = Some m2.
Proof.
intros.
revert vs' m m2; induction vs; intros.
simpl.
intuition. exists m; intuition. destruct H as [? [H ?]]; inv H; auto.
simpl.
case_eq (Genv.alloc_global ge m a); intros.
specialize (IHvs vs' m0 m2).
auto.
intuition; try discriminate.
destruct H0 as [? [? ?]]; discriminate.
Qed.

Lemma alloc_globals_rev_eq:
     forall F V (ge: Genv.t F V) m vl,
     Genv.alloc_globals ge m (rev vl) = alloc_globals_rev ge m vl.
Proof.
intros.
revert m; induction vl; intros; auto.
simpl.
rewrite <- IHvl.
case_eq (Genv.alloc_globals ge m (rev vl)); intros.
case_eq (Genv.alloc_global ge m0 a); intros.
rewrite alloc_globals_app.
exists m0; split; auto.
simpl. rewrite H0; auto.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
exfalso.
apply alloc_globals_app in H1.
destruct H1 as [m' [? ?]].
inversion2 H H1.
simpl in H2.
rewrite H0 in H2; inv H2.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
exfalso.
apply alloc_globals_app in H0.
destruct H0 as [m' [? ?]].
inversion2 H H0.
Qed.


Lemma zlength_nonneg: forall A l, 0 <= @Zlength A l.
Proof. intros.
  induction l. rewrite Zlength_nil. lia.
  rewrite Zlength_cons. lia.
Qed.

Lemma alloc_globals_rev_nextblock:
  forall {F V} (ge: Genv.t F V) vl m, alloc_globals_rev ge Mem.empty vl = Some m ->
     nextblock m = Z.to_pos(Z.succ (Zlength vl)).
Proof.
  intros.
   revert m H; induction vl; simpl; intros. inv H; apply nextblock_empty.
  invSome. apply IHvl in H.
  apply Genv.alloc_global_nextblock in H2.  rewrite Zlength_cons. rewrite H2.
  rewrite Z2Pos.inj_succ.
  rewrite <- H. trivial. apply Z.lt_succ_r. apply zlength_nonneg.
Qed.


Lemma store_zeros_max_access:  forall m b z N m',
      store_zeros m b z N = Some m' -> max_access_at m' = max_access_at m.
Proof.
 intros. symmetry in H; apply R_store_zeros_correct in H.
 remember (Some m') as m1. revert m' Heqm1; induction H; intros; inv Heqm1.
 auto.
 rewrite (IHR_store_zeros m'0 (eq_refl _)).
 clear - e0.
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold max_access_at; simpl. auto.
 Opaque store.
Qed.


Lemma store_zeros_access:  forall m b z N m',
      store_zeros m b z N = Some m' -> access_at m' = access_at m.
Proof.
 intros. symmetry in H; apply R_store_zeros_correct in H.
 remember (Some m') as m1. revert m' Heqm1; induction H; intros; inv Heqm1.
 auto.
 rewrite (IHR_store_zeros m'0 (eq_refl _)).
 clear - e0.
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold access_at; simpl. auto.
 Opaque store.
Qed.

Lemma store_zeros_contents1: forall m b z N m' loc,
      fst loc <> b ->
      store_zeros m b z N = Some m' ->
      contents_at m loc = contents_at m' loc.
Proof.
 intros. symmetry in H0; apply R_store_zeros_correct in H0.
 remember (Some m') as m1. revert m' Heqm1; induction H0; intros; inv Heqm1.
 auto.
 transitivity (contents_at m' loc).
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold contents_at; simpl. rewrite -> Maps.PMap.gso by auto. auto.
 eapply IHR_store_zeros; eauto.
 Opaque store.
Qed.


Lemma alloc_global_old:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, (fst loc < nextblock m)%positive ->
        access_at m loc = access_at m' loc
       /\ contents_at m loc = contents_at m' loc.
Proof.
 intros.
 destruct loc as [b ofs]; simpl in *; subst.
 assert (NEQ: b <> nextblock m) by (intro Hx; inv Hx; lia).
 unfold Genv.alloc_global in H. destruct iv.
 destruct g.
*
 revert H; case_eq (alloc m 0 1); intros.
 unfold drop_perm in H1.
 destruct (range_perm_dec m0 b0 0 1 Cur Freeable); inv H1.
 unfold contents_at, max_access_at, access_at in *;
 simpl in *.
 Transparent alloc. unfold alloc in H. Opaque alloc.
 inv H; simpl in *.
 rewrite Maps.PMap.gss. repeat rewrite (Maps.PMap.gso _ _ NEQ). auto.
*
 forget (init_data_list_size (gvar_init v)) as N.
 revert H; case_eq (alloc m 0 N); intros.
 invSome. invSome.
 assert (access_at m (b,ofs) = access_at m0 (b,ofs)
          /\ contents_at m (b,ofs) = contents_at m0 (b,ofs)). {
 clear - H NEQ.
 split. extensionality k. eapply alloc_access_other; try eassumption.
 left. intro. subst b0. apply alloc_result in H. contradiction.
 Transparent alloc. unfold alloc in H. Opaque alloc.
 unfold contents_at. inv H. simpl.
 rewrite -> Maps.PMap.gso by auto. auto.
 }
 assert (b0=nextblock m) by (inv H; auto). subst b0.
 unfold max_access_at.
 destruct H2 as [H2a H2b]; rewrite H2a H2b; clear H H2a H2b.
 rewrite <- (store_zeros_access _ _ _ _ _ H1).
 apply store_zeros_contents1 with (loc:= (b,ofs)) in H1.
 2: simpl; congruence. rewrite H1; clear H1 m0.
 apply store_init_data_list_outside' in H4.
 destruct H4 as [? [? ?]].
 specialize (H b ofs).  destruct H.
 destruct H; subst; congruence. unfold block in *; rewrite H; rewrite H1.
 clear - H5 NEQ.
 unfold drop_perm in H5.
 destruct (range_perm_dec m2 (nextblock m) 0 N Cur Freeable); inv H5.
 unfold contents_at, access_at, max_access_at in *;
 simpl in *.
  repeat rewrite (Maps.PMap.gso _ _ NEQ). auto.
Qed.

Fixpoint prog_vars' {F V} (l: list (ident * globdef F V)) : list (ident * globvar V) :=
 match l with nil => nil | (i,Gvar v)::r => (i,v):: prog_vars' r | _::r => prog_vars' r
 end.

Definition prog_vars {F} (p: program F) := prog_vars' (prog_defs p).

(* What do we actually need this for?
Definition no_locks : mpred := ∀ addr dq z z' R, ¬ addr ↦{dq} (LK z z' R).
*)

Lemma make_tycontext_s_find_id i G : (make_tycontext_s(Σ := Σ) G) !! i = find_id i G.
Proof.
  induction G as [| (j, fs) f IHf]. destruct i; reflexivity.
  simpl.
  rewrite Maps.PTree.gsspec.
  rewrite IHf.
  reflexivity.
Qed.

Program Definition drop_last_block m := {| mem_contents := mem_contents m;
  mem_access := Maps.PMap.set (nextblock m - 1)%positive (fun _ _ => None) (mem_access m);
  nextblock := (nextblock m - 1)%positive |}.
Next Obligation.
Proof.
  intros.
  destruct (eq_dec b (nextblock m - 1)%positive).
  - subst; rewrite Maps.PMap.gss //.
  - rewrite Maps.PMap.gso //; apply access_max.
Qed.
Next Obligation.
Proof.
  intros.
  destruct (eq_dec b (nextblock m - 1)%positive).
  - subst; rewrite Maps.PMap.gss //.
  - rewrite Maps.PMap.gso //; apply nextblock_noaccess.
    unfold Plt in *; lia.
Qed.
Next Obligation.
Proof.
  apply contents_default.
Qed.

Lemma rmap_of_drop_last_block : forall m {F} (ge : Genv.t (fundef F) type) G loc, res_of_loc (drop_last_block m) ge G loc =
  if eq_dec loc.1 (nextblock m - 1)%positive then (shared.NO (Share Share.bot) bot_unreadable) else res_of_loc m ge G loc.
Proof.
  intros; rewrite /res_of_loc /drop_last_block /access_at /contents_at /=.
  destruct (eq_dec loc.1 (nextblock m - 1)%positive).
  - rewrite e Maps.PMap.gss //.
  - rewrite Maps.PMap.gso //.
Qed.

Lemma rmap_of_drop_last : forall m block_bounds {F} (ge : Genv.t (fundef F) type) G n, (n < Pos.to_nat (nextblock m) - 1)%nat ->
  ([^op list] n0 ∈ seq 1 n, let '(lo, z) := block_bounds (Pos.of_nat n0) in
   [^op list] o ∈ seq 0 (z + 1), {[(Pos.of_nat n0, lo + Z.of_nat o) := res_of_loc m ge G (Pos.of_nat n0, lo + Z.of_nat o)]} ) =
  ([^op list] n0 ∈ seq 1 n, let '(lo, z) := block_bounds (Pos.of_nat n0) in
   [^op list] o ∈ seq 0 (z + 1), {[(Pos.of_nat n0, lo + Z.of_nat o) := res_of_loc (drop_last_block m) ge G (Pos.of_nat n0, lo + Z.of_nat o)]} ).
Proof.
  intros.
  apply big_opL_ext; intros ??[-> ?]%lookup_seq.
  destruct (block_bounds (Pos.of_nat _)).
  apply big_opL_ext; intros.
  rewrite rmap_of_drop_last_block.
  if_tac; try done.
  simpl in *; lia.
Qed.

Lemma lookup_singleton_list : forall {A} {B : ora} (l : list A) (f : A -> B) k i, (([^op list] i↦v ∈ l, ({[adr_add k (Z.of_nat i) := f v]})) !! i ≡
  if adr_range_dec k (Z.of_nat (length l)) i then f <$> (l !! (Z.to_nat (i.2 - k.2))) else None)%stdpp.
Proof.
  intros.
  remember (rev l) as l'; generalize dependent l; induction l'; simpl; intros.
  { destruct l; simpl; last by apply app_cons_not_nil in Heql'.
    rewrite lookup_empty; if_tac; auto. }
  apply (f_equal (@rev _)) in Heql'; rewrite rev_involutive in Heql'; subst; simpl.
  rewrite lookup_proper; last apply big_opL_snoc.
  rewrite lookup_op IHl'; last by rewrite rev_involutive.
  destruct k as (?, o), i as (?, o').
  if_tac; [|if_tac].
  - destruct H; subst; simpl.
    rewrite lookup_singleton_ne; last by rewrite /adr_add; intros [=]; lia.
    rewrite if_true; last by rewrite app_length; lia.
    rewrite lookup_app.
    by destruct (lookup_lt_is_Some_2 (rev l') (Z.to_nat (o' - o))) as (? & ->); first lia.
  - destruct H0 as [-> Hrange].
    rewrite app_length /= in Hrange.
    assert (o' = o + Z.of_nat (length (rev l')))%Z as -> by (rewrite /adr_range in H; lia).
    rewrite /adr_add lookup_singleton /= list_lookup_middle //; lia.
  - rewrite lookup_singleton_ne //.
    rewrite /adr_add /=; intros [=]; subst; contradiction H0.
    split; auto; rewrite app_length /=; lia.
Qed.

Lemma lookup_of_loc : forall m {F} ge G b lo z loc,
  (([^op list] o ∈ seq 0 z, {[(b, (lo + Z.of_nat o)%Z) := @res_of_loc m F ge G (b, (lo + Z.of_nat o)%Z)]} ) !! loc ≡
  if adr_range_dec (b, lo) z loc then Some (res_of_loc m ge G loc) else None)%stdpp.
Proof.
  intros.
  evar (f : nat -> (sharedR (leibnizO resource))).
  etrans; [|etrans; [apply (lookup_singleton_list (seq 0 z) f (b, lo) loc)|]].
  2: { rewrite seq_length; if_tac; last done.
       destruct loc, H; subst; simpl.
       rewrite lookup_seq_lt /=; last lia.
       subst f; instantiate (1 := fun i => res_of_loc m ge G (b, i + lo)); simpl.
       replace (_ + _) with z0 by lia; done. }
  subst f.
  etrans; [|symmetry; apply (big_opL_seq_index(M := gmapR address _))].
  f_equiv; apply big_opL_ext; intros.
  rewrite (Z.add_comm _ lo) //.
Qed.

Lemma lookup_of_mem : forall m {F} ge G block_bounds loc, (@rmap_of_mem m block_bounds F ge G !! loc ≡ let '(lo, z) := block_bounds (fst loc) in
  if plt (fst loc) (nextblock m) && zle lo (snd loc) && zle (snd loc) (lo + Z.of_nat z) then Some (res_of_loc m ge G loc) else None)%stdpp.
Proof.
  intros; rewrite /rmap_of_mem.
  remember (Pos.to_nat (nextblock m) - 1)%nat as n.
  generalize dependent m; induction n; intros.
  { rewrite /= lookup_empty.
    destruct (block_bounds loc.1).
    destruct (_ && _) eqn: Hin; last done.
    rewrite !andb_true_iff in Hin; destruct Hin as ((? & ?) & ?).
    destruct (plt _ _); try done.
    unfold Plt in *; lia. }
  rewrite seq_S lookup_proper; last apply big_opL_app.
  rewrite /= !lookup_op lookup_empty op_None_right_id.
  rewrite rmap_of_drop_last; last lia.
  rewrite IHn; last by simpl; lia.
  rewrite /= rmap_of_drop_last_block.
  rewrite Heqn Nat2Pos.inj_sub // Pos2Nat.id /= /Pos.of_nat.
  destruct (eq_dec loc.1 (nextblock m - 1)%positive).
  - rewrite -e.
    destruct (block_bounds loc.1) as (lo, z); simpl.
    destruct (plt _ _); first by unfold Plt in *; lia.
    rewrite /= left_id lookup_of_loc.
    destruct (plt _ _); try by unfold Plt in *; lia.
    if_tac.
    + destruct loc as (?, o), H; simpl in *.
      destruct (zle lo o); try lia; destruct (zle o (lo + z)); try lia; done.
    + destruct loc as (?, o); simpl.
      destruct (zle lo o); try done.
      destruct (zle o (lo + z)); try done.
      contradiction H; simpl; auto; lia.
  - destruct (block_bounds (nextblock m - 1)%positive).
    rewrite lookup_of_loc if_false; last by destruct loc; intros [??].
    rewrite right_id.
    destruct (plt _ _), (plt _ _); try done; unfold Plt in *; lia.
Qed.

Lemma perm_of_Lsh : perm_of_sh Share.Lsh = Some Nonempty.
Proof.
  rewrite /perm_of_sh.
  pose proof Lsh_nonreadable.
  rewrite if_false; last auto.
  rewrite if_false // if_false //.
  apply Lsh_bot_neq.
Qed.

Lemma rmap_of_loc_coherent : forall m F (ge : Genv.t (fundef F) type) G loc, coherent_loc m loc (resR_to_resource (Some (res_of_loc m ge G loc))).
Proof.
  intros; rewrite /res_of_loc.
  destruct (access_at m loc Cur) eqn: Hloc; last apply coherent_bot.
  destruct p; try (destruct (funspec_of_loc _ _ _) as [[]|]; last apply coherent_bot); rewrite /= elem_of_to_agree.
  - split.
    + unfold contents_cohere; simpl.
      by inversion 1.
    + rewrite /access_cohere Hloc /=.
      rewrite /perm_of_sh !if_true //; auto.
      constructor.
  - split.
    + unfold contents_cohere; simpl.
      by inversion 1.
    + rewrite /access_cohere Hloc /= perm_of_Ews.
      constructor.
  - split.
    + unfold contents_cohere; simpl.
      by inversion 1.
    + rewrite /access_cohere Hloc /= perm_of_Ers.
      constructor.
  - split.
    + done.
    + rewrite /access_cohere Hloc /=.
      constructor.
Qed.

Lemma rmap_of_mem_coherent : forall m block_bounds {F} ge G loc, (✓ @rmap_of_mem m block_bounds F ge G)%stdpp ->
  coherent_loc m loc (resource_at (@rmap_of_mem m block_bounds F ge G) loc).
Proof.
  intros; rewrite /resource_at.
  specialize (H loc).
  erewrite resR_to_resource_eq; [| done | apply lookup_of_mem].
  rewrite lookup_of_mem in H.
  destruct loc as (b, o); destruct (block_bounds b) eqn: Hbounds; rewrite Hbounds /=.
  destruct (plt _ _); last apply coherent_bot.
  destruct (zle z o); simpl; last apply coherent_bot.
  destruct (zle o (z + n)); last apply coherent_bot; simpl.
  apply rmap_of_loc_coherent.
Qed.

Lemma rmap_of_loc_valid : forall m {F} ge G loc, (✓ (@res_of_loc m F ge G loc))%stdpp.
Proof.
  intros; rewrite /res_of_loc.
  destruct (access_at m loc Cur); try done.
  destruct p; try done; try destruct (funspec_of_loc _ _ _) as [[]|]; try done.
  split; try done.
  eexists; split; eauto.
  intros ?; apply bot_unreadable; auto.
Qed.

Lemma rmap_of_mem_valid : forall m block_bounds {F} ge G, (✓ @rmap_of_mem m block_bounds F ge G)%stdpp.
Proof.
  intros.
  intros i; rewrite lookup_of_mem.
  destruct (block_bounds _).
  simple_if_tac; try done.
  apply rmap_of_loc_valid.
Qed.

Lemma merge_disjoint : forall {K A} `{Merge M} `{∀A, Lookup K A (M A)} `{FinMap K M} (f1 f2 : A -> A -> option A) (m1 m2 : M A)
  (Hdisj : m1 ##ₘ m2), merge (union_with f1) m1 m2 = merge (union_with f2) m1 m2.
Proof.
  intros.
  rewrite -merge_Some //; intros.
  rewrite lookup_merge /diag_None.
  specialize (Hdisj i).
  destruct (m1 !! i)%stdpp, (m2 !! i)%stdpp; done.
Qed.

Lemma big_opM_opL' : forall {A B} (f : _ -> A -> gmapR address B) (g : _ -> _ -> mpred) l
  (Hl : base.NoDup l) (Hf : forall k1 k2 a1 a2, a1 ∈ l -> a2 ∈ l -> a1 ≠ a2 -> f k1 a1 ##ₘ f k2 a2)
  (Hg : forall k y1 y2, (✓ y1)%stdpp -> (y1 ≡ y2)%stdpp -> g k y1 ⊣⊢ g k y2) (Hv : (✓ ([^op list] a↦b ∈ l, f a b))%stdpp),
  ([∗ map] k↦v ∈ ([^op list] a↦b ∈ l, f a b), g k v) ⊣⊢
  [∗ list] a↦b ∈ l, [∗ map] k↦v ∈ f a b, g k v.
Proof.
  intros.
  remember (rev l) as l'; generalize dependent l; induction l'; simpl; intros.
  { destruct l; simpl; last by apply app_cons_not_nil in Heql'.
    apply big_sepM_empty. }
  apply (f_equal (@rev _)) in Heql'; rewrite rev_involutive in Heql'; subst; simpl in *.
  apply NoDup_app in Hl as (? & Hsep & ?).
  rewrite big_sepL_app big_opM_proper_2; [|apply big_opL_app | intros ?????; apply Hg].
  rewrite big_opL_app /= right_id in Hv.
  assert (([^op list] k↦y ∈ rev l', f k y) ##ₘ ([^op list] k↦y ∈ [a], f (length (rev l') + k)%nat y)) as Hdisj.
  { clear -Hf Hsep.
    rewrite /= right_id.
    forget (length (rev l') + 0)%nat as k; revert k.
    induction l'; simpl; intros.
    { rewrite /ε; apply map_disjoint_empty_l. }
    rewrite big_opL_app /=.
    apply map_disjoint_dom_2; rewrite dom_op.
    rewrite disjoint_union_l; split.
    * apply map_disjoint_dom_1, IHl'.
      { intros ???? ?%elem_of_app ?%elem_of_app; apply Hf; simpl; rewrite !elem_of_app; tauto. }
      intros; apply Hsep; simpl.
      rewrite elem_of_app; auto.
    * rewrite right_id.
      apply map_disjoint_dom_1, Hf.
      { simpl; rewrite !elem_of_app !elem_of_list_singleton; auto. }
      { simpl; rewrite !elem_of_app !elem_of_list_singleton; auto. }
      intros ->.
      contradiction (Hsep a); rewrite /= ?elem_of_app elem_of_list_singleton; auto. }
  match goal with |-context[?a ⋅ ?b] => replace (a ⋅ b) with (map_union a b) end.
  rewrite big_opM_union //.
  rewrite IHl' //.
  apply bi.sep_proper; first done.
  rewrite /op /gmapR /ora_op /= /gmap_op_instance fin_maps.RightId_instance_0 bi.sep_emp //.
  * intros; apply Hf; try done; rewrite elem_of_app; auto.
  * eapply cmra_valid_op_l; done.
  * rewrite rev_involutive //.
  * by apply merge_disjoint.
  * specialize (Hv k); rewrite H1 // in Hv.
Qed.

Global Instance disjoint_rel_proper {A B : ofe} : Proper (base.equiv ==> base.equiv ==> base.equiv) (option_relation(A := A)(B := B) (fun _ _ => False%type) (fun _ => True%type) (fun _ => true%type)).
Proof.
  intros ?? Heq1 ?? Heq2.
  inv Heq1; inv Heq2; done.
Qed.

Definition init_funspecs {F} (m : mem) (ge : Genv.t (fundef F) type) (G : funspecs) : gmap address (@funspecO' Σ) :=
  foldl (fun fs b => match funspec_of_loc ge G (Pos.of_nat b, 0) with
    Some f => <[(Pos.of_nat b, 0) := funspec_unfold f]>fs | None => fs end) ∅ (seq 1 (Pos.to_nat (nextblock m) - 1)).

Local Close Scope maps.

Lemma init_funspecs_lookup : forall {F} (m : mem) (ge : Genv.t (fundef F) type) (G : funspecs) l,
  init_funspecs m ge G !! l = if Pos.ltb l.1 (nextblock m) then match funspec_of_loc ge G l with
    Some f => Some (funspec_unfold f) | None => None end else None.
Proof.
  rewrite /init_funspecs; intros.
  replace (nextblock m) with (Pos.of_nat (Pos.to_nat (nextblock m) - 1 + 1)) at 2 by lia.
  induction (Pos.to_nat (nextblock m) - 1)%nat.
  { simpl.
    destruct (Pos.ltb_spec0 l.1 (Pos.of_nat 1)); first lia; done. }
  rewrite seq_S foldl_snoc.
  destruct (funspec_of_loc ge G (Pos.of_nat (1 + n), 0)) eqn: Hfun.
  - destruct (eq_dec l (Pos.of_nat (1 + n), 0)).
    + subst; rewrite lookup_insert /=.
      destruct (Pos.ltb_spec0 (Pos.of_nat (S n)) (Pos.of_nat (S (n + 1)))); last lia.
      rewrite Hfun //.
    + rewrite lookup_insert_ne // IHn.
      destruct (Pos.ltb_spec0 l.1 (Pos.of_nat (n + 1))), (Pos.ltb_spec0 l.1 (Pos.of_nat (S n + 1))); try done; try lia.
      unfold funspec_of_loc.
      if_tac; last done.
      destruct l; simpl in *; contradiction n0; f_equal; lia.
  - rewrite IHn.
    destruct (Pos.ltb_spec0 l.1 (Pos.of_nat (n + 1))), (Pos.ltb_spec0 l.1 (Pos.of_nat (S n + 1))); try done; try lia.
    unfold funspec_of_loc in *.
    if_tac; last done.
    assert (l = (Pos.of_nat (1 + n), 0)) as ->; last by rewrite Hfun.
    destruct l; simpl in *; f_equal; lia.
Qed.

Lemma init_funspecs_over : forall {F} (ge : Genv.t (fundef F) type) G n n' o, (n < n')%nat -> (foldl (fun fs b => match funspec_of_loc ge G (Pos.of_nat b, 0) with
    Some f => <[(Pos.of_nat b, 0) := funspec_unfold f]>fs | None => fs end) ∅ (seq 1 n) : gmap address (@funspecO' Σ)) !! (Pos.of_nat n', o) = None.
Proof.
  induction n.
  { simpl; intros; apply lookup_empty. }
  rewrite seq_S foldl_snoc.
  intros; destruct (funspec_of_loc _ _ _).
  - rewrite lookup_insert_ne; [apply IHn | intros [=]]; lia.
  - apply IHn; lia.
Qed.

Lemma rmap_inflate_equiv : forall m block_bounds {F} (ge : Genv.t (fundef F) type) G
  (Hfun_bounds : forall b f, funspec_of_loc ge G (b, 0) = Some f -> block_bounds b = (0, 0%nat))
  (Hm : forall b, (b < nextblock m)%positive ->
        match funspec_of_loc ge G (b, 0) with
        | Some _ => access_at m (b, 0) Cur = Some Nonempty
        | None => True
        end),
  funspec_auth ∅ ∗ ([∗ map] l ↦ x ∈ rmap_of_mem m block_bounds ge G, match x with
                     | (shared.YES dq _ v) => l ↦{dq} (proj1_sig (elem_of_agree v))
                     | (shared.NO (Share sh) _) => mapsto_no l sh
                     | _ => False
                     end) ⊢ |==> funspec_auth (init_funspecs m ge G) ∗ inflate_initial_mem m block_bounds ge G.
Proof.
  intros.
  assert (∀ (l : address) (y1 y2 : sharedR (leibnizO resource)), (✓ y1)%stdpp → (y1 ≡ y2)%stdpp →
    match y1 with
    | (shared.YES dq _ v) => l ↦{dq} (proj1_sig (elem_of_agree v))
    | (shared.NO (Share sh) _) => mapsto_no l sh
    | _ => False end ⊣⊢ match y2 with
           | (shared.YES dq _ v) => l ↦{dq} (proj1_sig (elem_of_agree v))
           | (shared.NO (Share sh) _) => mapsto_no l sh
           | _ => False end).
  { intros ??? Hv Heq.
    destruct y1, y2; inv Heq; try done.
    destruct Hv.
    match goal with H : (_ ≡ _)%stdpp |- _ => apply (elem_of_agree_ne O) in H as ->%leibniz_equiv; done end. }
  rewrite /rmap_of_mem /init_funspecs /inflate_initial_mem big_opM_opL' //.
  assert (Pos.to_nat (nextblock m) - 1 < Pos.to_nat (nextblock m))%nat as Hlt by lia.
  induction (Pos.to_nat (nextblock m) - 1)%nat.
  { by iIntros. }
  rewrite seq_S /= !big_sepL_app foldl_snoc assoc IHn /=.
  iIntros "(>(Hf & $) & Hm & _)".
  destruct (block_bounds _) eqn: Hbounds.
  rewrite big_opM_opL' //.
  destruct (funspec_of_loc ge G (Pos.of_nat (S n), 0)) eqn: Hfun.
  * iMod (own_update with "Hf") as "($ & Hf)".
    { apply (gmap_view.gmap_view_alloc _ (Pos.of_nat (S n), 0) dfrac.DfracDiscarded); last done.
      apply init_funspecs_over; auto. }
    erewrite Hfun_bounds in Hbounds by done; inv Hbounds; simpl.
    rewrite !big_sepM_singleton /res_of_loc /inflate_loc.
    specialize (Hm (Pos.of_nat (S n)) ltac:(lia)); rewrite Hfun in Hm; rewrite Hm Hfun /func_at elem_of_to_agree.
    iDestruct "Hm" as "($ & _)"; iFrame; done.
  * iFrame.
    assert (forall z, funspec_of_loc ge G (Pos.of_nat (S n), z) = None) as Hfun'.
    { intros; unfold funspec_of_loc in *.
      simpl; if_tac; done. }
    rewrite bi.sep_emp -big_sepL_bupd; iApply (big_sepL_mono with "Hm"); intros ?? [-> ?]%lookup_seq.
    rewrite big_opM_singleton.
    rewrite /res_of_loc /inflate_loc.
    destruct (access_at _ _ _) eqn: Haccess; last apply bupd_intro.
    destruct p; try apply bupd_intro; rewrite ?Hfun' ?elem_of_to_agree; apply bupd_intro.
  * apply NoDup_seq.
  * intros; intros i.
    rewrite /option_relation.
    destruct (eq_dec i (Pos.of_nat (S n), (z + a1)%Z)); last by rewrite lookup_singleton_ne //; destruct (_ !! _).
    destruct (eq_dec i (Pos.of_nat (S n), (z + a2)%Z)); last by rewrite (lookup_singleton_ne (_, (_ + a2)%Z)) //; destruct (_ !! _).
    subst; inv e0; lia.
  * intros i.
    rewrite lookup_of_loc.
    if_tac; try done.
    apply rmap_of_loc_valid.
  * lia.
  * apply NoDup_seq.
  * intros _ _ ?? Ha1%elem_of_seq Ha2%elem_of_seq ?.
    destruct (block_bounds _), (block_bounds _).
    intros i.
    rewrite disjoint_rel_proper; [| apply lookup_of_loc..].
    rewrite /option_relation; if_tac; last by destruct (if adr_range_dec _ _ _ then _ else _).
    if_tac; last done.
    destruct i, H1, H2; lia.
  * apply rmap_of_mem_valid.
Qed.

Lemma inflate_drop_last : forall m block_bounds {F} (ge : Genv.t (fundef F) type) G n, (n < Pos.to_nat (nextblock m) - 1)%nat ->
  ([∗ list] y ∈ seq 1 n, let '(lo, z) := block_bounds (Pos.of_nat y) in
   [∗ list] o ∈ seq 0 z, inflate_loc m ge G (Pos.of_nat y, lo + Z.of_nat o)) =
  ([∗ list] y ∈ seq 1 n, let '(lo, z) := block_bounds (Pos.of_nat y) in
   [∗ list] o ∈ seq 0 z, inflate_loc (drop_last_block m) ge G (Pos.of_nat y, lo + Z.of_nat o)).
Proof.
  intros.
  apply big_opL_ext; intros ??[-> ?]%lookup_seq.
  destruct (block_bounds (Pos.of_nat _)).
  apply big_opL_ext; intros.
  rewrite /inflate_loc /access_at /= Maps.PMap.gso //.
  lia.
Qed.

Local Instance decide_fun_lt m {F} (ge : Genv.t (fundef F) type) : ∀ x : ident * funspec, Decision ((fun '(id, _) => match Genv.find_symbol ge id with Some b => Plt b (nextblock m) | None => False%type end) x).
Proof.
  intros (?, ?); destruct (Genv.find_symbol _ _); last by right; intros ?.
  destruct (plt b (nextblock m)); by [left | right].
Qed.

Lemma filter_all : forall {A} (P : A -> Prop) `(∀x, Decision (P x)) l, Forall P l -> base.filter P l = l.
Proof.
  induction l; simpl; first done.
  inversion 1; subst; simpl.
  rewrite filter_cons_True // IHl //.
Qed.

Lemma list_norepet_filter : forall {A B} P `(∀x, Decision (P x)) (l : list (A * B)), list_norepet (map fst l) -> list_norepet (map fst (base.filter P l)).
Proof.
  induction l; simpl; first done.
  inversion 1 as [|?? Hout]; subst.
  rewrite filter_cons; destruct (decide (P a)); last auto; simpl.
  constructor; auto.
  rewrite !in_map_iff in Hout |- *.
  intros (? & ? & [??%elem_of_list_In]%elem_of_list_In%elem_of_list_filter); eauto.
Qed.

Lemma big_sepL_absorb : ∀ {A} (Φ : nat → A → mpred) l,
  ([∗ list] k↦x ∈ l, <absorb> Φ k x) ⊢ <absorb> [∗ list] k↦x ∈ l, Φ k x.
Proof.
  induction l using rev_ind; simpl.
  - iIntros "$".
  - rewrite !big_sepL_app /= IHl.
    iIntros "(>$ & >$ & _)".
Qed.

Lemma initial_mem_initial_core : forall m block_bounds {F} (ge : Genv.t (fundef F) type) G
  (Hm : forall b, (b < nextblock m)%positive ->
        match funspec_of_loc ge G (b, 0) with
        | Some _ => access_at m (b, 0) Cur = Some Nonempty
        | None => True
        end)
  (Hbounds : forall b, (b < nextblock m)%positive -> (block_bounds b).1 <= 0 <= (block_bounds b).1 + Z.of_nat (block_bounds b).2),
  inflate_initial_mem m block_bounds ge G ⊢ inflate_initial_mem m block_bounds ge G ∗ initial_core m ge G.
Proof.
  intros; rewrite /inflate_initial_mem /initial_core.
  iIntros "H"; iSplit; first done.
  iApply big_sepL_absorb; iApply (big_sepL_mono with "H"); intros ?? (-> & ?)%lookup_seq.
  iIntros "H".
  specialize (Hbounds (Pos.of_nat (1 + k)) ltac:(lia)).
  specialize (Hm (Pos.of_nat (1 + k)) ltac:(lia)).
  destruct (block_bounds _) as (lo, hi); simpl in *.
  iPoseProof (big_sepL_lookup_acc _ _ (Z.to_nat (-lo)) with "H") as "(H & _)".
  { apply lookup_seq; split; first done; lia. }
  replace (lo + _) with 0 by lia.
  rewrite /inflate_loc.
  destruct (funspec_of_loc _ _ _).
  - rewrite Hm //.
  - replace (DfracOwn (Share share_top)) with (ε ⋅ DfracOwn (Share share_top)) by rewrite left_id //.
    replace (DfracOwn (Share Ews)) with (ε ⋅ DfracOwn (Share Ews)) by rewrite left_id //.
    replace (DfracOwn (Share Ers)) with (ε ⋅ DfracOwn (Share Ers)) by rewrite left_id //.
    destruct (access_at _ _ _); last done.
    destruct p; last done; iDestruct (mapsto_split_no with "H") as "($ & _)"; simpl; auto; (apply bot_unreadable || apply readable_Ers).
Qed.

Lemma rmap_of_mem_nextblock : ∀ m block_bounds {F} (ge : Genv.t (fundef F) type) G loc,
  (loc.1 >= nextblock m)%positive → rmap_of_mem m block_bounds ge G !! loc = None.
Proof.
  intros; pose proof (lookup_of_mem m ge G block_bounds loc) as Hlookup.
  destruct (plt _ _).
  { unfold Plt in *; clear - H p. apply Pos.lt_nle in p; contradiction p. apply Pos.ge_le; done. }
  simpl in Hlookup.
  destruct (block_bounds _); inv Hlookup; done.
Qed.

Lemma initialize_mem : forall m block_bounds {F} (ge : Genv.t (fundef F) type) G
  (Hfun_bounds : forall b f, funspec_of_loc ge G (b, 0) = Some f -> block_bounds b = (0, 0%nat))
  (Hm : forall b, (b < nextblock m)%positive ->
        match funspec_of_loc ge G (b, 0) with
        | Some _ => access_at m (b, 0) Cur = Some Nonempty
        | None => True
        end),
  mem_auth Mem.empty ∗ funspec_auth ∅ ⊢ |==> mem_auth m ∗ funspec_auth (init_funspecs m ge G) ∗ inflate_initial_mem m block_bounds ge G.
Proof.
  intros.
  pose proof (rmap_of_mem_valid m block_bounds ge G).
  rewrite mem_auth_set //.
  iIntros "(>(Hm & Hr) & Hf)".
  iCombine "Hf Hr" as "Hr"; iMod (rmap_inflate_equiv with "Hr") as "$"; try done.
  - apply rmap_of_mem_nextblock.
  - intros; by apply rmap_of_mem_coherent.
Qed.

End mpred.

(*Require Import VST.veric.wsat.

(* This is provable, but we probably don't want to use it: we should set up the proof infrastructure
   (heapGS, etc.) first, and then allocate the initial memory in a later step. *)
Lemma alloc_initial_mem `{!wsatGpreS Σ} `{!gen_heapGpreS resource Σ} `{!inG Σ (gmapR address (agreeR (@funspecO' Σ)))} m block_bounds {F} (ge : Genv.t (fundef F) type) G :
  ⊢ |==> ∃ _ : heapGS Σ, wsat ∗ ownE ⊤ ∗ mem_auth m ∗ inflate_initial_mem m block_bounds ge G ∗
 ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  iIntros.
  iMod wsat_alloc as (?) "(? & ?)".
  pose proof (rmap_of_mem_valid m block_bounds ge G).
  iMod (gen_heap_init_names m (rmap_of_mem m block_bounds ge G)) as (??) "(Hm & H & ?)".
  { apply rmap_of_mem_nextblock. }
  { intros; by apply rmap_of_mem_coherent. }
  iMod (own_alloc ∅) as (γ) "?".
  iExists (HeapGS _ _ _ _ γ); iFrame.
  rewrite /mem_auth /= -rmap_inflate_equiv //.
Qed.*)
