Require Import VST.progs.ghost.
Require Import mailbox.verif_ptr_atomics.
Require Import VST.progs.conclib.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.oplistset.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tnode := Tstruct _node noattr.

(* Each thread's share of the head should act as permission to get the same share of any other node in the list.
   In fact, it might need to maintain a list of nodes it knows about (for which it owns a share) and retain the
   right to get a share of any new node it finds. In this model, each time it loads from next it checks whether
   it's finding a new node or one that it already owns, and gains a share or not accordingly. *)
(* Alternatively, it could just have the right to get *some* readable share of any other node. This will make
   it impossible to rejoin the shares or know that they're all recollected, but maybe that's fine. We could even
   try using a token factory. *)

(* A tail element with INT_MAX ensures that we never fall off the end. *)
Definition node_fun gsh1 gsh2 R a := let '(e0, g, p) := a in
  EX sh : share, EX e : Z, EX next : val, EX lock : val, !!(readable_share sh /\ repable_signed e /\ e0 < e /\
    if eq_dec e Int.max_signed then next = nullval else True) &&
    data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
    EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
    if eq_dec e Int.max_signed then emp else atomic_loc sh next (fun v => |>R (e, g', v)).

Definition node gsh1 gsh2 := HORec (node_fun gsh1 gsh2).

Lemma node_eq' : forall gsh1 gsh2,
  node gsh1 gsh2 = node_fun gsh1 gsh2 (node gsh1 gsh2).
Proof.
  intros; apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 ((e0, g), p).
  apply subp_exp; intro sh.
  apply subp_exp; intro e.
  apply subp_exp; intro next.
  apply subp_exp; intro lock.
  apply subp_sepcon; [apply subp_refl|].
  apply subp_exp; intro g'.
  apply subp_sepcon; [apply subp_refl|].
  if_tac; [apply subp_refl|].
  apply subp_andp; [apply subp_refl|].
  apply subp_exp; intro l.
  apply subp_sepcon; [apply subp_refl|].
  eapply derives_trans; [|simpl; apply subtypes.fash_derives, predicates_hered.andp_left1; auto].
  eapply derives_trans; [|apply (nonexpansive_lock_inv sh l)].
  eapply derives_trans; [|simpl; apply (A_inv_nonexpansive next l)].
  apply allp_right; intro v.
  apply allp_left with ((e, g'), v); auto.
Qed.

Corollary node_eq : forall gsh1 gsh2 e0 g p, node gsh1 gsh2 (e0, g, p) =
  EX sh : share, EX e : Z, EX next : val, EX lock : val, !!(readable_share sh /\ repable_signed e /\ e0 < e /\
    if eq_dec e Int.max_signed then next = nullval else True) &&
    data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
    EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
    if eq_dec e Int.max_signed then emp else atomic_loc sh next (fun v => |>node gsh1 gsh2 (e, g', v)).
Proof.
  intros.
  transitivity (node_fun gsh1 gsh2 (node gsh1 gsh2) (e0, g, p)); [|reflexivity].
  rewrite <- node_eq'; auto.
Qed.

Lemma node_isptr : forall gsh1 gsh2 e0 g p, node gsh1 gsh2 (e0, g, p) = !!isptr p && node gsh1 gsh2 (e0, g, p).
Proof.
  intros; eapply local_facts_isptr with (P := fun p => node gsh1 gsh2 (e0, g, p)); eauto.
  rewrite node_eq.
  Intros sh e next lock.
  rewrite data_at_isptr; entailer!.
Qed.
Hint Resolve node_isptr : saturate_local.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0,
             P at level 100, Q at level 100).

Record node_rep := { data : Z; next : val; lock : val; gnext : val }.

Definition node_data gsh1 gsh2 sh rep p :=
  data_at sh tnode (vint (data rep), (next rep, lock rep)) p *
  lock_inv sh (lock rep) (EX p : val, ghost_var gsh2 p (gnext rep)) *
  if eq_dec (data rep) Int.max_signed then emp
  else atomic_loc sh (next rep) (fun v => |>node gsh1 gsh2 (data rep, gnext rep, v)).

Definition node' gsh1 gsh2 rep p := EX sh : share,
  !!(readable_share sh /\ repable_signed (data rep) /\
     if eq_dec (data rep) Int.max_signed then next rep = nullval else True) &&
  node_data gsh1 gsh2 sh rep p.

Definition known_nodes gsh1 gsh2 nodes :=
  fold_right sepcon emp (map (fun '(p, rep) => node' gsh1 gsh2 rep p) nodes).

Definition new_node_spec := DECLARE _new_node
  WITH e : Z, nnext : val, sh : share, rep : node_rep, gsh1 : share, gsh2 : share
  PRE [ _e OF tint, _nnext OF tptr tnode ]
    PROP (repable_signed e; readable_share sh; repable_signed (data rep); e < data rep;
          sepalg.join gsh1 gsh2 Tsh;
          if eq_dec (data rep) Int.max_signed then next rep = nullval else True)
    LOCAL (temp _e (vint e); temp _nnext nnext)
    SEP (node_data gsh1 gsh2 sh rep nnext)
  POST [ tptr tnode ]
   EX p : val, EX rep' : node_rep,
    PROP (data rep' = e)
    LOCAL (temp ret_temp p)
    SEP (node_data gsh1 gsh2 Tsh rep' p;
         malloc_token Tsh (sizeof tnode) p; malloc_token Tsh (sizeof tlock) (lock rep')).

Definition validate_spec := DECLARE _validate
  WITH hp : val, head : val, e : Z, pred : val, curr : val, sh : share, gsh1 : share, gsh2 : share,
    reph : node_rep, repp : node_rep, pn : val, repc : node_rep, nodes : _
  PRE [ _e OF tint, _pred OF tptr tnode, _curr OF tptr tnode ]
    PROP (Int.min_signed < e < Int.max_signed; Int.min_signed <= data repp < e;
          readable_share sh; readable_share gsh1; readable_share gsh2; sepalg.join gsh1 gsh2 Tsh;
          e <= data repc <= Int.max_signed; data reph = Int.min_signed;
          In (head, reph) nodes; In (pred, repp) nodes;
          In (curr, repc) nodes; curr <> pred; curr <> head)
    LOCAL (gvar _head hp; temp _e (vint e); temp _pred pred; temp _curr curr)
    SEP (data_at sh (tptr tnode) head hp; ghost_var gsh2 pn (gnext repp); known_nodes gsh1 gsh2 nodes)
  POST [ tint ]
   EX b : bool, EX nodes' : _,
    PROP (incl nodes nodes'; b = true -> pn = curr)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tptr tnode) head hp; ghost_var gsh2 pn (gnext repp); known_nodes gsh1 gsh2 nodes';
         valid_pointer pn).

Definition tnode_pair := Tstruct _node_pair noattr.

Definition locate_spec := DECLARE _locate
  WITH hp : val, head : val, e : Z, sh : share, gsh1 : share, gsh2 : share, reph : node_rep, nodes : _
  PRE [ _e OF tint ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; data reph = Int.min_signed; In (head, reph) nodes)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes)
  POST [ tptr tnode_pair ]
   EX r : val, EX pred : val, EX repp : node_rep, EX curr : val, EX repc : node_rep, EX cn : val, EX nodes' : _,
    PROP (data repp < e <= data repc; repable_signed (data repp); repable_signed (data repc);
          incl nodes nodes'; In (pred, repp) nodes'; In (curr, repc) nodes')
    LOCAL (temp ret_temp r)
    SEP (data_at Tsh tnode_pair (pred, curr) r; malloc_token Tsh (sizeof tnode_pair) r;
         data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes';
         ghost_var gsh2 curr (gnext repp); ghost_var gsh2 cn (gnext repc)).

(* Could we prove at least simple linearization points after all, e.g. by abstracting the list of nodes into a set
   and then showing that some atomic step in the function body has the abstract pre and postcondition? This
   wouldn't be part of a funspec as such, but it's part of RGSep methodology. (See the marked steps in Figure 2
   of Proving Correctness of Highly-Concurrent Linearisable Objects, Vafeiadis et al, PPoPP 2006. *)
(* Without such an approach, we don't get much useful information out of the return value, unless we use
   histories to say that writes occur only on a successful add (which we can, along the lines of hashtable1). *)
Definition add_spec := DECLARE _add
  WITH hp : val, head : val, e : Z, sh : share, gsh1 : share, gsh2 : share, reph : node_rep, nodes : _
  PRE [ _e OF tint ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; NoDup (map fst nodes); data reph = Int.min_signed; In (head, reph) nodes)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes)
  POST [ tint ]
   EX b : bool, EX rep' : node_rep, EX n' : val, EX nodes' : _,
    PROP (data rep' = e; incl nodes nodes'; b = true -> ~In n' (map fst nodes); In (n', rep') nodes')
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes').

(* A useful spec for remove is even more unclear. How do we know the removed node is no longer in the list? *)
Definition remove_spec := DECLARE _remove
  WITH hp : val, head : val, e : Z, sh : share, gsh1 : share, gsh2 : share, reph : node_rep, nodes : _
  PRE [ _e OF tint ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; data reph = Int.min_signed; In (head, reph) nodes)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes)
  POST [ tint ]
   EX b : bool, EX n' : val, EX nodes' : _,
    PROP (incl nodes nodes'; b = true -> exists rep', In (n', rep') nodes' /\ data rep' = e)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes').

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; acquire_spec; release_spec;
  makelock_spec; make_atomic_spec; load_SC_spec; store_SC_spec;
  validate_spec; locate_spec; new_node_spec; add_spec; remove_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Lemma node_lock_inv_positive : forall gsh2 g, positive_mpred (EX p : val, ghost_var gsh2 p g).
Admitted. (* probably not actually positive *)
Hint Resolve node_lock_inv_positive.

Lemma node_precise : forall gsh1 gsh2 e g v, precise (|> node gsh1 gsh2 (e, g, v)).
Admitted.
Hint Resolve node_precise.

Lemma body_new_node : semax_body Vprog Gprog f_new_node new_node_spec.
Proof.
  start_function.
  forward_call (sizeof tnode).
  { simpl; computable. }
  Intros r.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  forward_call (sizeof tlock).
  { simpl; computable. }
  Intros l.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  apply ghost_alloc with (g := (Tsh, nnext)); auto with init; Intro g.
  forward_call (l, Tsh, EX p : val, ghost_var gsh2 p g).
  forward.
  forward_call (l, Tsh, EX p : val, ghost_var gsh2 p g).
  { lock_props.
    fold (ghost_var Tsh nnext g).
    rewrite <- (ghost_var_share_join _ _ _ _ _ SH0).
    Exists nnext; cancel. }
  forward_call (nnext, ghost_var gsh1 nnext g * node_data gsh1 gsh2 sh rep nnext,
    fun v => |>node gsh1 gsh2 (e, g, v), emp).
  { repeat intro.
    eapply semax_pre; [|eauto].
    go_lowerx; cancel.
    unfold node_data; rewrite node_eq.
    rewrite <- sepcon_emp at 1; apply sepcon_derives.
    apply andp_right.
    - eapply derives_trans, now_later.
      rewrite node_eq; Exists sh (data rep) (next rep) (lock rep) (gnext rep); entailer!.
    - eapply derives_trans, now_later; entailer!.
    - apply andp_right; auto.
      eapply derives_trans, precise_weak_precise; auto.
      rewrite <- node_eq; auto. }
  Intro n.
  repeat forward.
  Exists r {| data := e; next := n; lock := l; gnext := g |}; unfold node_data; simpl;
    destruct (eq_dec e Int.max_signed); [unfold repable_signed in *; omega|]; entailer!.
  { exists 2; auto. }
  { exists 2; auto. }
Qed.

Lemma node_contents_eq : forall sh1 sh2 e1 e2 n1 n2 l1 l2 p, readable_share sh1 -> readable_share sh2 ->
  repable_signed e1 -> repable_signed e2 -> n1 <> Vundef -> n2 <> Vundef -> l1 <> Vundef -> l2 <> Vundef ->
  data_at sh1 tnode (vint e1, (n1, l1)) p * data_at sh2 tnode (vint e2, (n2, l2)) p |--
  !!(e1 = e2 /\ n1 = n2 /\ l1 = l2).
Proof.
  intros; simpl in *; do 2 unfold_data_at 1%nat.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (field_at _ _ [StructField _val] _ _)), <- !sepcon_assoc.
  unfold field_at, at_offset; rewrite !data_at_rec_eq; unfold unfold_reptype; simpl; Intros.
  rewrite 3sepcon_assoc; apply saturate_aux20.
  { eapply derives_trans; [apply mapsto_value_eq; auto; discriminate|].
    apply prop_left; intro; apply prop_right, repr_inj_signed; auto; congruence. }
  rewrite <- !sepcon_assoc, (sepcon_comm _ (mapsto _ _ _ n2)), <- sepcon_assoc.
  rewrite sepcon_assoc, (sepcon_comm (mapsto _ _ _ _)); apply saturate_aux20; apply mapsto_value_eq; auto.
Qed.

Lemma node_val_eq : forall sh1 sh2 e1 e2 n1 n2 l1 l2 p, readable_share sh1 -> readable_share sh2 ->
  repable_signed e1 -> repable_signed e2 ->
  data_at sh1 tnode (vint e1, (n1, l1)) p * data_at sh2 tnode (vint e2, (n2, l2)) p |-- !!(e1 = e2).
Proof.
  intros; simpl in *; do 2 unfold_data_at 1%nat.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (field_at _ _ [StructField _val] _ _)), <- !sepcon_assoc.
  do 4 apply sepcon_derives_prop.
  unfold field_at, at_offset; rewrite !data_at_rec_eq; simpl; Intros.
  eapply derives_trans; [apply mapsto_value_eq; auto; discriminate|].
  unfold unfold_reptype; simpl; apply prop_left; intro; apply prop_right, repr_inj_signed; auto; congruence.
Qed.

Corollary node_data_eq : forall gsh1 gsh2 sh1 sh2 rep1 rep2 p, readable_share sh1 -> readable_share sh2 ->
  repable_signed (data rep1) -> repable_signed (data rep2) ->
  node_data gsh1 gsh2 sh1 rep1 p * node_data gsh1 gsh2 sh2 rep2 p |-- !!(data rep1 = data rep2).
Proof.
  intros; unfold node_data; Intros.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
  do 4 apply sepcon_derives_prop; rewrite sepcon_comm; apply node_val_eq; auto.
Qed.

Lemma node_data_valid_pointer : forall gsh1 gsh2 sh rep p, readable_share sh ->
  node_data gsh1 gsh2 sh rep p |-- valid_pointer p.
Proof.
  intros; unfold node_data; Intros.
  rewrite sepcon_assoc; apply sepcon_valid_pointer1, data_at_valid_ptr; auto; simpl; computable.
Qed.

Lemma node_data_isptr : forall gsh1 gsh2 sh rep p,
  node_data gsh1 gsh2 sh rep p = !!isptr p && node_data gsh1 gsh2 sh rep p.
Proof.
  intros.
  eapply local_facts_isptr; [|eauto].
  unfold node_data; entailer!.
Qed.
Hint Resolve node_data_isptr : saturate_local.

Lemma node_data_share_join : forall gsh1 gsh2 sh1 sh2 sh rep p, readable_share sh1 -> readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  node_data gsh1 gsh2 sh1 rep p * node_data gsh1 gsh2 sh2 rep p = node_data gsh1 gsh2 sh rep p.
Proof.
  intros; unfold node_data.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)).
  erewrite <- !sepcon_assoc, (sepcon_comm (data_at _ _ _ _)), data_at_share_join by eauto.
  rewrite (sepcon_comm _ (lock_inv _ _ _)), <- !sepcon_assoc.
  erewrite (sepcon_comm _ (lock_inv _ _ _)), <- !sepcon_assoc, lock_inv_share_join by eauto.
  if_tac; [rewrite !sepcon_emp, sepcon_comm; auto|].
  rewrite (sepcon_comm _ (atomic_loc sh2 _ _)), <- !sepcon_assoc.
  erewrite (sepcon_comm _ (atomic_loc _ _ _)), <- !sepcon_assoc, atomic_loc_join by eauto.
  apply mpred_ext; cancel.
Qed.

(*Corollary node'_persistent : forall gsh1 gsh2 p,
  node' gsh1 gsh2 p * node' gsh1 gsh2 p = node' gsh1 gsh2 p.
Proof.
  intros; unfold node'; apply mpred_ext.
  - Intros sh1 rep1 sh2 rep2.
    assert_PROP (rep1 = rep2).

Qed.*)

Lemma known_nodes_cons : forall gsh1 gsh2 rep p nodes,
  known_nodes gsh1 gsh2 ((p, rep) :: nodes) = node' gsh1 gsh2 rep p * known_nodes gsh1 gsh2 nodes.
Proof.
  auto.
Qed.

Lemma known_nodes_join : forall gsh1 gsh2 nodes1 nodes2,
  known_nodes gsh1 gsh2 nodes1 * known_nodes gsh1 gsh2 nodes2 = known_nodes gsh1 gsh2 (nodes1 ++ nodes2).
Proof.
  intros; unfold known_nodes; rewrite map_app, sepcon_app; auto.
Qed.

Corollary known_node : forall gsh1 gsh2 nodes1 rep p nodes2,
  known_nodes gsh1 gsh2 (nodes1 ++ (p, rep) :: nodes2) =
  node' gsh1 gsh2 rep p * known_nodes gsh1 gsh2 (nodes1 ++ nodes2).
Proof.
  intros; rewrite <- !known_nodes_join, known_nodes_cons; apply mpred_ext; cancel.
Qed.

Instance EqDec_node_rep : EqDec node_rep.
Proof.
  repeat intro.
  decide equality; try apply EqDec_val.
  apply Z.eq_dec.
Qed.

Instance EqDec_node : EqDec (val * node_rep).
Proof.
  repeat intro.
  decide equality; [apply EqDec_node_rep | apply EqDec_val].
Qed.

Lemma in_nodes_eq : forall gsh1 gsh2 sh rep rep' p nodes (Hsh : readable_share sh)
  (Hin : In (p, rep') nodes) (Hrep : repable_signed (data rep)),
  node_data gsh1 gsh2 sh rep p * known_nodes gsh1 gsh2 nodes |-- !!(data rep = data rep').
Proof.
  intros.
  apply in_split in Hin; destruct Hin as (? & ? & ?); subst.
  rewrite <- known_nodes_join; unfold known_nodes; simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (node' _ _ _ _)), <- sepcon_assoc.
  unfold node'; Intros sh'.
  rewrite (sepcon_comm _ (node_data _ _ _ _ _)); do 2 apply sepcon_derives_prop.
  apply node_data_eq; auto.
Qed.

Corollary nodes_inj : forall gsh1 gsh2 rep1 rep2 p nodes
  (Hin1 : In (p, rep1) nodes) (Hin2 : In (p, rep2) nodes),
  known_nodes gsh1 gsh2 nodes |-- !!(data rep1 = data rep2).
Proof.
  intros.
  destruct (eq_dec (p, rep1) (p, rep2)); [inv e; entailer!|].
  apply in_split in Hin1; destruct Hin1 as (? & ? & ?); subst.
  unfold known_nodes; rewrite map_app, sepcon_app; simpl.
  unfold node' at 2; Intros sh.
  rewrite <- sepcon_assoc, (sepcon_comm _ (node_data _ _ _ _ _)).
  rewrite sepcon_assoc; setoid_rewrite known_nodes_join.
  apply in_nodes_eq; auto.
  rewrite in_app in *; destruct Hin2 as [|[|]]; auto; contradiction.
Qed.

Lemma node_valid : forall gsh1 gsh2 e g p, |> node gsh1 gsh2 (e, g, p) |-- |> valid_pointer p.
Proof.
  intros; apply later_derives.
  rewrite node_eq.
  Intros sh1 e1 next1 lock1; entailer!.
Qed.

Lemma body_validate : semax_body Vprog Gprog f_validate validate_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS, abbreviate.
  assert (repable_signed (data repp)) by (split; omega).
  assert (repable_signed (data repc)) by (split; omega).
  assert (repable_signed (data reph)) by (replace (data reph) with Int.min_signed; split; computable).
  assert_PROP (pred = head -> data repp = data reph).
  { destruct (eq_dec pred head); [|apply prop_right; contradiction].
    subst; assert_PROP (data repp = data reph); [|apply prop_right; auto].
    focus_SEP 2; go_lower; eapply sepcon_derives_prop, nodes_inj; eauto. }
  match goal with H : In (head, _) nodes |- _ => apply in_split in H; destruct H as (nodes1 & nodes2 & ?); subst end.
  unfold known_nodes; rewrite map_app, sepcon_app; simpl; unfold node' at 2; unfold node_data; Intros shh.
  gather_SEP 2 6; replace_SEP 0 (known_nodes gsh1 gsh2 (nodes1 ++ nodes2)) by (rewrite <- known_nodes_join; entailer!).
  forward.
  forward.
  forward_while (EX succ : val, EX shs : share, EX reps : node_rep, EX nodes' : _,
    PROP (readable_share shs; repable_signed (data reps); incl (nodes1 ++ nodes2) nodes';
          succ = head /\ reps = reph \/ In (head, reph) nodes';
          if eq_dec (data reps) Int.max_signed then next reps = nullval else True)
    LOCAL (temp _v (vint (data reps)); temp _succ succ; gvar _head hp; temp _e (vint e); temp _pred pred;
           temp _curr curr)
    SEP (node_data gsh1 gsh2 shs reps succ; data_at sh (tptr tnode) head hp;
         ghost_var gsh2 pn (gnext repp); known_nodes gsh1 gsh2 nodes')).
  - Exists head shh reph (nodes1 ++ nodes2); entailer!.
    apply incl_refl.
  - entailer!.
  - unfold node_data; Intros.
    destruct (eq_dec (data reps) Int.max_signed); [omega|].
    rewrite atomic_loc_isptr; Intros.
    repeat forward.
    forward_call (shs, next reps, emp,
      fun v => |>node gsh1 gsh2 (data reps, gnext reps, v),
      fun v => |>(EX shs' : share, EX reps' : node_rep,
          !!(readable_share shs' /\ repable_signed (data reps') /\ data reps < data reps' /\
             if eq_dec (data reps') Int.max_signed then next reps' = nullval else True) &&
          node_data gsh1 gsh2 shs' reps' v)).
    { split; auto.
      intro.
      rewrite valid_same by (apply node_valid).
      rewrite sepcon_emp, <- later_sepcon; apply derives_view_shift, later_derives.
      rewrite node_eq; Intros sh' e' next' lock' g'.
      exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
      Exists sh1 e' next' lock' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |} g'.
      erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
      unfold node_data; simpl; entailer!.
      if_tac; [entailer!|].
      erewrite atomic_loc_join; eauto. }
    Intros succ'.
    rewrite (later_exp' _ Share.bot); Intro shs'.
    rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro reps'.
    hoist_later_in_pre.
    focus_SEP 1.
    erewrite extract_prop_in_SEP with (n := 0%nat); [|simpl; eauto].
    simpl replace_nth.
    unfold node_data at 1; rewrite !flatten_sepcon_in_SEP.
    apply assert_later_PROP with (P1 := readable_share shs'); [entailer!; tauto | intro].
    forward.
    Exists (succ', shs', reps', (succ, reps) :: nodes'); unfold node_data; entailer!.
    + split; [apply incl_tl; auto|].
      match goal with H : _ \/ _ |- _ => destruct H as [[]|]; auto end.
    + unfold known_nodes; simpl; cancel.
      unfold node', node_data; Exists shs; entailer!; if_tac; auto; omega.
  - eapply semax_pre with (P' := EX shp : share, EX nodes2 : _,
      PROP (readable_share shp; incl nodes' ((pred, repp) :: nodes2))
      LOCAL (temp _v (vint (data reps)); temp _succ succ; gvar _head hp;
             temp _e (vint e); temp _pred pred; temp _curr curr)
      SEP (node_data gsh1 gsh2 shp repp pred;
           if in_dec EqDec_node (pred, repp) nodes' then node_data gsh1 gsh2 shs reps succ
           else !!(pred = head /\ succ = head /\ reps = reph /\ repp = reph) && emp;
           data_at sh (tptr tnode) head hp; ghost_var gsh2 pn (gnext repp); known_nodes gsh1 gsh2 nodes2)).
    { destruct (in_dec EqDec_node (pred, repp) nodes').
      + apply in_split in i; destruct i as (nodes1' & nodes2' & ?); subst.
        rewrite known_node; unfold node'; Intros shp.
        Exists shp (nodes1' ++ nodes2'); entailer!.
        intros ? Hin; simpl; rewrite in_app in *; simpl in *; destruct Hin as [|[|]]; auto.
      + match goal with H : In (pred, repp) _ |- _ => rewrite in_app in H; destruct H as [|[X|]];
          try solve [match goal with H : incl _ nodes' |- _ =>
            specialize (H (pred, repp)); rewrite in_app in H; contradiction n; auto end] end.
        inv X.
        match goal with H : _ \/ _ |- _ => destruct H as [[]|]; [|contradiction] end.
        subst; Exists shs nodes'; entailer!.
        apply incl_tl, incl_refl. }
    unfold node_data at 1; Intros shp nodes''.
    destruct (eq_dec (data repp) Int.max_signed); [omega|].
    rewrite atomic_loc_isptr; Intros.
    forward.
    forward_call (shp, next repp, ghost_var gsh2 pn (gnext repp),
      fun v => |>node gsh1 gsh2 (data repp, gnext repp, v),
      fun v => |>(!!(v = pn /\ isptr pn) && ghost_var gsh2 pn (gnext repp) * valid_pointer pn)).
    { split; auto.
      intro.
      rewrite valid_same by (apply node_valid).
      etransitivity; [apply view_shift_sepcon, derives_view_shift, now_later; reflexivity|].
      rewrite <- !later_sepcon.
      apply view_shift_later.
      rewrite node_eq.
      rewrite exp_sepcon1; apply view_shift_exists; intro sh'.
      rewrite exp_sepcon1; apply view_shift_exists; intro e'.
      rewrite exp_sepcon1; apply view_shift_exists; intro next'.
      rewrite exp_sepcon1; apply view_shift_exists; intro lock'.
      rewrite !exp_sepcon1, !exp_sepcon2, exp_sepcon1; apply view_shift_exists; intro g'.
      rewrite !sepcon_andp_prop'; apply view_shift_prop; intros (? & ? & ? & ?).
      rewrite (sepcon_comm _ (ghost_var gsh2 _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var _ _ _)), <- !sepcon_assoc.
      erewrite ghost_var_share_join' by eauto.
      rewrite !sepcon_andp_prop'; apply view_shift_prop; intro; subst.
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift.
      exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
      Exists sh1 e' next' lock' g'.
      erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
      entailer!.
      rewrite !sepcon_assoc; eapply derives_trans; [apply sepcon_derives;
        [apply data_at_valid_ptr; auto; simpl; computable | apply derives_refl]|].
      if_tac.
      { rewrite sepcon_emp, emp_sepcon; apply sepcon_valid_pointer1; auto. }
      erewrite <- atomic_loc_join by eauto.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_loc sh1 _ _)).
      rewrite !sepcon_assoc; apply sepcon_derives; auto; entailer!. }
    Intros n'.
    assert (In (curr, repc) nodes'') as Hcurr.
    { assert (In (curr, repc) nodes') as Hin.
      + match goal with H : incl _ nodes' |- _ => apply H end.
        match goal with H : In (curr, repc) _ |- _ =>
          rewrite in_app in *; destruct H as [|[X|]]; auto end.
        inv X; contradiction.
      + match goal with H : incl nodes' _ |- _ => specialize (H _ Hin); destruct H as [X|]; auto end.
        inv X; contradiction. }
    apply in_split in Hcurr; destruct Hcurr as (nodesa & nodesb & ?); subst.
    rewrite known_node; unfold node'; Intros shc.
    rewrite data_at_isptr, (node_data_isptr _ _ shc); Intros.
    assert_PROP (isptr succ).
    { if_tac; [|Intros; entailer!].
      rewrite node_data_isptr; entailer!. }
    hoist_later_in_pre; apply assert_later_PROP with (P1 := isptr pn).
    { entailer!. }
    intro; forward.
    { entailer!.
      apply denote_tc_test_eq_split.
      + destruct (in_dec EqDec_node (pred, repp) nodes').
        * rewrite (sepcon_comm _ (node_data _ _ _ _ succ)), !sepcon_assoc.
          apply sepcon_valid_pointer1, node_data_valid_pointer; auto.
        * Intros; subst.
          rewrite (sepcon_comm _ (data_at _ _ _ head)), !sepcon_assoc.
          apply sepcon_valid_pointer1, data_at_valid_ptr; auto; simpl; computable.
      + rewrite (sepcon_comm _ (node_data _ _ _ _ curr)), !sepcon_assoc.
        apply sepcon_valid_pointer1, node_data_valid_pointer; auto. }
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP ()(LOCALx (temp _t'3 (Val.of_bool
        (if eq_dec succ curr then if eq_dec n' curr then true else false else false)) :: Q) (SEPx R))) end.
    { forward.
      { entailer!.
        apply denote_tc_test_eq_split; [entailer!|].
        rewrite (sepcon_comm _ (node_data _ _ _ _ curr)), !sepcon_assoc.
        apply sepcon_valid_pointer1, node_data_valid_pointer; auto. }
      entailer!; simpl.
      rewrite force_sem_cmp_pp in * by auto.
      if_tac; [|discriminate].
      if_tac; auto. }
    { forward.
      entailer!.
      rewrite force_sem_cmp_pp in * by auto.
      if_tac; [discriminate | auto]. }
    forward.
    forward.
    Exists (if eq_dec succ curr then if eq_dec pn curr then true else false else false)
      ((if in_dec EqDec_node (pred, repp) nodes' then [(succ, reps)] else []) ++
       (pred, repp) :: nodesa ++ (curr, repc) :: nodesb).
    rewrite <- !known_nodes_join, known_nodes_cons, known_node, <- !known_nodes_join.
    unfold node_data; entailer!.
    + split.
      * assert (In (pred, repp) nodes' \/ (pred, repp) = (head, reph)) as Hpred.
        { match goal with H : In (pred, repp) _ |- _ => rewrite in_app in H; destruct H as [|[|]]; auto end;
            match goal with H : incl _ nodes' |- _ => left; apply H; rewrite in_app; auto end. }
        intros a Hin; repeat match goal with H : incl _ _ |- _ => specialize (H a) end.
        rewrite in_app in *; simpl in *.
        destruct Hin as [|[X|]]; auto; inv X.
        destruct Hpred; auto.
        match goal with H : _ \/ _ |- _ => destruct H as [[]|]; auto; subst end.
        destruct (in_dec _ _ _); simpl; auto.
      * if_tac; [|discriminate].
        if_tac; [subst; auto | discriminate].
    + unfold node'.
      Exists shc shp; unfold node_data; destruct (eq_dec (data repp) Int.max_signed); [omega|].
      entailer!.
      unfold known_nodes; if_tac; simpl; entailer!.
      unfold node', node_data; Exists shs; entailer!.
Qed.

Lemma body_locate : semax_body Vprog Gprog f_locate locate_spec.
Proof.
  start_function.
  eapply semax_pre with (P' := EX nodes0 : _,
    PROP (incl nodes nodes0)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; known_nodes gsh1 gsh2 nodes0)).
  { Exists nodes; entailer!.
    apply incl_refl. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply ENTAIL_refl].
  Intros nodes0.
  forward.
  assert (In (head, reph) nodes0) as Hin by auto.
  apply in_split in Hin; destruct Hin as (nodes1 & nodes2 & ?); subst.
  rewrite known_node; unfold node', node_data; Intros shh.
  if_tac; [omega|].
  rewrite atomic_loc_isptr; Intros.
  repeat forward.
  forward_call (shh, next reph, emp,
    fun v => |>node gsh1 gsh2 (data reph, gnext reph, v),
    fun v => |>(EX shc : share, EX repc : node_rep,
      !!(readable_share shc /\ repable_signed (data repc) /\ data reph < data repc /\
         if eq_dec (data repc) Int.max_signed then next repc = nullval else True) &&
      node_data gsh1 gsh2 shc repc v)).
  { split; auto; intro.
    apply derives_view_shift.
    rewrite valid_same by (apply node_valid).
    rewrite <- later_sepcon.
    eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
    rewrite node_eq.
    Intros sh' e' next' lock' g'.
    exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
    Exists sh1 e' next' lock' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |} g'.
    erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
    unfold node_data; simpl; entailer!.
    if_tac; [entailer!|].
    erewrite atomic_loc_join; eauto. }
  Intros curr0.
  rewrite (later_exp' _ Share.bot); Intro shc0.
  rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro repc0.
  hoist_later_in_pre.
  focus_SEP 1.
  erewrite extract_prop_in_SEP with (n := O); [|simpl; eauto].
  simpl replace_nth.
  unfold node_data at 1; rewrite !flatten_sepcon_in_SEP.
  apply assert_later_PROP with (P1 := readable_share shc0); [entailer!; tauto | intro].
  forward.
  assert (repable_signed (data reph)) by (replace (data reph) with Int.min_signed; split; computable).
  destruct (eq_dec curr0 head).
  { subst; gather_SEP 0 5.
    assert_PROP (data repc0 = data reph); [|omega].
    go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
  forward_while (EX pred : val, EX repp : node_rep, EX curr : val, EX shc : share, EX repc : node_rep, EX nodes' : _,
    PROP (readable_share shc; repable_signed (data repp); repable_signed (data repc);
          pred <> curr; curr <> head; data repp < e; data repp < data repc;
          incl (nodes1 ++ (head, reph) :: nodes2) nodes'; In (pred, repp) nodes';
          if eq_dec (data repc) Int.max_signed then next repc = nullval else True)
    LOCAL (temp _v (vint (data repc)); temp _curr curr; temp _pred pred;
           gvar _head hp; temp _e (vint e))
    SEP (node_data gsh1 gsh2 shc repc curr; known_nodes gsh1 gsh2 nodes';
         data_at sh (tptr tnode) head hp)).
  - Exists head reph curr0 shc0 repc0 (nodes1 ++ (head, reph) :: nodes2).
    rewrite known_node; unfold node', node_data.
    destruct (eq_dec (data reph) Int.max_signed); [omega|]; Exists shh; entailer!.
    split; [omega | apply incl_refl].
  - entailer!.
  - (* loop body *)
    unfold node_data; Intros.
    destruct (eq_dec (data repc) Int.max_signed); [omega|].
    rewrite atomic_loc_isptr; Intros.
    repeat forward.
    forward_call (shc, next repc, emp,
      fun v => |>node gsh1 gsh2 (data repc, gnext repc, v),
      fun v => |>(EX sh' : share, EX rep' : node_rep,
        !!(readable_share sh' /\ repable_signed (data rep') /\ data repc < data rep' /\
           if eq_dec (data rep') Int.max_signed then next rep' = nullval else True) &&
        node_data gsh1 gsh2 sh' rep' v)).
    { split; auto; intro.
      apply derives_view_shift.
      rewrite valid_same by (apply node_valid).
      rewrite <- later_sepcon.
      eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
      rewrite node_eq; unfold node'.
      Intros sh' e' next' lock' g'.
      exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
      Exists sh1 e' next' lock' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |} g'.
      erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
      unfold node_data; simpl; entailer!.
      if_tac; [entailer!|].
      erewrite atomic_loc_join; eauto. }
    Intros curr'.
    rewrite (later_exp' _ Share.bot); Intro sh'.
    rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro rep'.
    hoist_later_in_pre.
    focus_SEP 1.
    erewrite extract_prop_in_SEP with (n := 0%nat); [|simpl; eauto].
    simpl replace_nth.
    assert_PROP (curr' <> head).
    { destruct (eq_dec curr' head); [|apply prop_right; auto].
      Intros; assert_PROP (data rep' = data reph); [|unfold repable_signed in *; omega].
      gather_SEP 0 4.
      subst; go_lower; apply sepcon_derives_prop, in_nodes_eq; auto. }
    unfold node_data; rewrite !flatten_sepcon_in_SEP.
    apply assert_later_PROP with (P1 := readable_share sh'); [entailer!; tauto | intro].
    forward.
    destruct (eq_dec curr' curr).
    { gather_SEP 0 4; assert_PROP (data rep' = data repc); [|omega].
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    Exists (curr, repc, curr', sh', rep', (curr, repc) :: nodes').
    simpl SEPx; rewrite known_nodes_cons; unfold node', node_data.
    Exists shc; destruct (eq_dec (data repc) Int.max_signed); [omega | entailer!].
    apply incl_tl; auto.
  - match goal with H : In (pred, repp) _ |- _ => apply in_split in H; destruct H as (nodesa & nodesb & ?); subst end.
    rewrite known_node; unfold node'; Intros shp.
    unfold node_data; rewrite (lock_inv_isptr shp), (lock_inv_isptr shc); Intros; repeat forward.
    forward_call (lock repp, shp, EX p : val, ghost_var gsh2 p (gnext repp)).
    forward_call (lock repc, shc, EX p : val, ghost_var gsh2 p (gnext repc)).
    Intros cn pn.
    forward_call (hp, head, e, pred, curr, sh, gsh1, gsh2, reph, repp, pn, repc,
      (curr, repc) :: nodesa ++ (pred, repp) :: nodesb).
    { rewrite known_nodes_cons, known_node; cancel.
      unfold node', node_data; Exists shc shp; entailer!. }
    { split; [auto|].
      split; [unfold repable_signed in *; tauto|].
      simpl; repeat (split; [auto|]); unfold repable_signed in *; try tauto; try omega.
      rewrite in_app; simpl; auto. }
    Intros x; destruct x as (b & nodes'').
    gather_SEP 1 4.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx R))) end.
    { subst; match goal with H : _ = _ -> _ |- _ => specialize (H eq_refl); subst end.
      forward_call (sizeof tnode_pair).
      { simpl; computable. }
      Intros r.
      rewrite malloc_compat; auto; Intros.
      rewrite memory_block_data_at_; auto.
      repeat forward.
      Exists r pred repp curr repc cn nodes''; entailer!.
      simpl in *.
      split; [eapply incl_tran | split]; try match goal with H : incl _ nodes'' |- _ => apply H end.
      + eapply incl_tl, incl_tran; eauto.
      + simpl; rewrite in_app; simpl; auto.
      + simpl; auto.
      + admit. (* more or less *)
      + exists 2; auto. }
    { simpl in *; assert (In (pred, repp) nodes'') as Hpred.
      { match goal with H : incl _ nodes'' |- _ => apply H end.
        simpl; rewrite in_app; simpl; auto. }
      apply in_split in Hpred; destruct Hpred as (nodesa' & nodesb' & ?); subst.
      rewrite known_node; unfold node', node_data; Intros shp'.
      forward_call (lock repp, shp', EX p : val, ghost_var gsh2 p (gnext repp)).
      { unfold node_data; lock_props.
        Exists pn; cancel. }
      assert (In (curr, repc) (nodesa' ++ nodesb')) as Hcurr.
      { match goal with H : incl _ _ |- _ => specialize (H _ (or_introl eq_refl)); rewrite in_app in *;
          destruct H as [|[X|]]; auto; inv X; contradiction end. }
      apply in_split in Hcurr; destruct Hcurr as (nodesa'' & nodesb'' & Heq).
      rewrite Heq, known_node; unfold node', node_data; Intros shc'.
      forward_call (lock repc, shc', EX p : val, ghost_var gsh2 p (gnext repc)).
      { unfold node_data; Intros; lock_props.
        Exists cn; cancel. }
      rewrite known_node, Heq, known_node.
      unfold node', node_data; Exists shp' shc'; entailer!. }
    intros; unfold overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
    unfold POSTCONDITION, abbreviate, loop1_ret_assert; Intros.
    Exists nodes''; entailer!.
    eapply incl_tran, incl_tran, incl_cons_inv; eauto.
    { admit. }
Admitted.

Lemma body_add : semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward_call (hp, head, e, sh, gsh1, gsh2, reph, nodes).
  { unfold tnode; cancel. }
  { tauto. }
  Intros x; destruct x as ((((((r, pred), repp), curr), repc), cn), nodes1); simpl in *.
  match goal with H : In (pred, _) _ |- _ => apply in_split in H; destruct H as (nodesa & nodesb & ?); subst end.
  rewrite known_node.
  assert (In (curr, repc) (nodesa ++ nodesb)) as Hinc.
  { match goal with H : In (curr, _) _ |- _ => rewrite in_app in * ; destruct H as [|[X|]]; auto end.
    inv X; omega. }
  apply in_split in Hinc; destruct Hinc as (nodesa' & nodesb' & Heq); rewrite Heq, known_node.
  unfold node'; Intros shp shc.
  rewrite node_data_isptr with (p := pred), node_data_isptr with (p := curr).
  unfold node_data at 2; Intros.
  repeat forward.
  forward_call (r, sizeof (tnode_pair)).
  { apply sepcon_derives; [apply  data_at_memory_block | cancel_frame]. }
  forward.
  assert (incl nodes ((pred, repp) :: (curr, repc) :: nodesa' ++ nodesb')) as Hincl.
  { eapply incl_tran; eauto.
    intros a Hin; destruct (in_dec EqDec_node a (nodesa ++ nodesb)).
    + rewrite Heq in i.
      destruct (in_dec EqDec_node a (nodesa' ++ nodesb')); [simpl; auto|].
      rewrite in_app in *; simpl in *; destruct i as [|[|]]; auto; contradiction n; auto.
    + rewrite in_app in *; simpl in *; destruct Hin as [|[|]]; auto; contradiction n; auto. }
  gather_SEP 2 3 4 5 6; rewrite <- !sepcon_assoc; fold (node_data gsh1 gsh2 shc repc curr).
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    forward_if (EX shc' : share, EX n' : val, EX rep' : node_rep, EX nodes' : _,
      PROP (data rep' = e; readable_share shc'; incl (nodesa' ++ nodesb') nodes';
            if eq_dec (data repc) e then n' = curr /\ rep' = repc
            else In (n', rep') nodes' /\ ~In n' (map fst nodes))
      (LOCALx (temp _result (Val.of_bool (if eq_dec (data repc) e then false else true)) :: Q)
      (SEPx (node_data gsh1 gsh2 shc' repc curr :: ghost_var gsh2 n' (gnext repp) ::
             known_nodes gsh1 gsh2 nodes' :: R)))) end.
  { destruct (split_readable_share shc) as (shc1 & shc2 & ? & ? & Hshc); auto.
    rewrite <- (node_data_share_join _ _ shc1 shc2 shc) by auto.
    forward_call (e, curr, shc2, repc, gsh1, gsh2).
    { split; [unfold repable_signed; omega|].
      split; [auto|].
      split; [auto|].
      split; [omega | auto]. }
    Intro x; destruct x as (n' & rep').
    destruct (in_dec EqDec_val n' (map fst nodes)).
    { rewrite in_map_iff in i; destruct i as ((n'', rep'') & ? & Hin); subst.
      apply Hincl in Hin; destruct Hin as [X|[X|Hin]]; try inv X; simpl.
      - unfold node_data at 1 3; Intros.
        gather_SEP 0 9.
        eapply semax_pre, semax_ff.
        go_lower; eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; auto].
        apply data_at_Tsh_conflict; auto; simpl; computable.
      - unfold node_data at 1 2; Intros.
        gather_SEP 0 5.
        eapply semax_pre, semax_ff.
        go_lower; eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; auto].
        apply data_at_Tsh_conflict; auto; simpl; computable.
      - apply in_split in Hin; destruct Hin as (? & ? & ->).
        rewrite known_node; unfold node'.
        unfold node_data at 1 3; Intros sh'.
        gather_SEP 0 6.
        eapply semax_pre, semax_ff.
        go_lower; eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; auto].
        apply data_at_Tsh_conflict; auto; simpl; computable. }
    unfold node_data at 3; Intros.
    destruct (eq_dec (data repp) Int.max_signed); [omega|].
    rewrite node_data_isptr, atomic_loc_isptr; Intros.
    forward.
    rewrite <- (node_data_share_join _ _ gsh1 gsh2 Tsh) by auto.
    forward_call (shp, next repp, n',
      node_data gsh1 gsh2 gsh2 rep' n' * ghost_var gsh2 curr (gnext repp),
      fun v => |>node gsh1 gsh2 (data repp, gnext repp, v),
      |>(ghost_var gsh2 n' (gnext repp) *
         EX shc' : share, EX repc' : node_rep, !!(readable_share shc' /\ repable_signed (data repc') /\
           if eq_dec (data repc') Int.max_signed then next repc' = nullval else True) &&
           node_data gsh1 gsh2 shc' repc' curr)).
    { split; auto; intro.
      rewrite sepcon_comm; etransitivity;
        [apply view_shift_sepcon; [apply derives_view_shift, now_later | reflexivity]|].
      rewrite !valid_same by (apply node_valid).
      rewrite (sepcon_comm _ (|>(_ * _))), <- sepcon_assoc, <- !later_sepcon.
      rewrite <- sepcon_emp at 1; apply view_shift_sepcon.
      apply view_shift_later.
      rewrite node_eq.
      rewrite exp_sepcon2; apply view_shift_exists; intro sh'.
      rewrite exp_sepcon2; apply view_shift_exists; intro e'.
      rewrite exp_sepcon2; apply view_shift_exists; intro next'.
      rewrite exp_sepcon2; apply view_shift_exists; intro lock'.
      rewrite !exp_sepcon2; apply view_shift_exists; intro g'.
      rewrite !sepcon_andp_prop', sepcon_andp_prop; apply view_shift_prop; intros (? & ? & ? & ?).
      rewrite (sepcon_comm _ (ghost_var gsh2 _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var _ _ _)), <- !sepcon_assoc.
      erewrite ghost_var_share_join' by eauto.
      rewrite !sepcon_andp_prop'; apply view_shift_prop; intro; subst.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon;
        [apply ghost_var_update with (v' := n') | reflexivity]|].
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift; rewrite node_eq.
      Exists sh' gsh2 (data rep') (next rep') (lock rep') (gnext rep')
        {| data := e'; next := next'; lock := lock'; gnext := g' |}.
      unfold node_data; simpl; entailer!.
      simpl in *; split; [unfold repable_signed; omega|].
      split; [omega|].
      if_tac; auto; omega.
      { apply derives_view_shift, andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. } }
    forward.
    Intros x; destruct x as (shc', repc').
    Exists shc1 n' rep' ((n', rep') :: (curr, repc') :: nodesa' ++ nodesb'); rewrite !known_nodes_cons.
    unfold node', node_data; Exists gsh1 shc'; entailer!.
    - simpl in *; if_tac; [contradiction|].
      split; split; auto; [do 2 apply incl_tl; apply incl_refl|].
      split; [unfold repable_signed; omega|].
      if_tac; auto; omega.
    - if_tac; [omega | cancel].
      admit. (* We need to carry malloc_tokens around in all of the node assertions. *) }
  { forward.
    Exists shc curr repc (nodesa' ++ nodesb'); subst; rewrite !eq_dec_refl; entailer!.
    apply incl_refl. }
  unfold node_data at 2; rewrite lock_inv_isptr; Intros shc' n' rep' nodes'.
  forward.
  forward_call (lock repp, shp, EX p : val, ghost_var gsh2 p (gnext repp)).
  { lock_props.
    Exists n'; cancel. }
  unfold node_data; rewrite (lock_inv_isptr shc'); Intros.
  forward.
  forward_call (lock repc, shc', EX p : val, ghost_var gsh2 p (gnext repc)).
  { lock_props.
    Exists cn; cancel. }
  forward.
  Exists (if eq_dec (data repc) (data rep') then false else true) rep' n'
    ((pred, repp) :: (curr, repc) :: nodes'); rewrite !known_nodes_cons.
  unfold node', node_data; Exists shp shc'; entailer!.
  split.
  - eapply incl_tran; eauto.
    do 2 apply incl_same_head; auto.
  - if_tac; simpl.
    + split; [discriminate|].
      match goal with H : _ /\ _ |- _ => destruct H; subst; auto end.
    + split; tauto.
Admitted.
