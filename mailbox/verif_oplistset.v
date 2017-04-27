Require Import progs.ghost.
Require Import mailbox.verif_ptr_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.oplistset.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(*Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.*)

Definition tnode := Tstruct _node noattr.

(* Each thread's share of the head should act as permission to get the same share of any other node in the list.
   In fact, it might need to maintain a list of nodes it knows about (for which it owns a share) and retain the
   right to get a share of any new node it finds. In this model, each time it loads from next it checks whether
   it's finding a new node or one that it already owns, and gains a share or not accordingly. *)
(* Alternatively, it could just have the right to get *some* readable share of any other node. This will make
   it impossible to rejoin the shares or know that they're all recollected, but maybe that's fine. We could even
   try using a token factory. *)

(*(* A PCM for rights to a specific share of a data structure of unknown extent. *)
(* Can this be simplified? *)
Instance shares_PCM : PCM (option (list val) * option (val * bool)) :=
  { join a b c := match a, b with
    | (Some l, None), (None, Some (v, t)) | (None, Some (v, t)), (Some l, None) =>
        c = (Some l, Some (v, t)) /\ if t then ~In v l else In v l
    | _, _ => False end }.
Proof.
  - intros (la, va) (lb, vb) (lc, vc).
    destruct la, va as [(?, ?)|]; try contradiction; destruct lb; try contradiction; auto.
  - intros (la, va) (lb, vb) (lc, vc) (ld, vd) (le, ve).
    destruct la, va as [(?, ?)|]; try contradiction; destruct lb; try contradiction; destruct vb as [(?, ?)|];
      try contradiction; intros (X & ?); inv X; contradiction.
Defined.
(* This approach requires us to know the number of simultaneous clients in advance (so we can allocate enough
   share lists). Unfortunately, I don't know how else to provide predictable shares. *)

Definition ghost_list (l : list val) p := ghost (Some l, @None (option val)) p.
Definition ghost_this (d : option val) p := ghost (@None (list val), Some d) p.*)

(*
(* Holding the other half of the ghost var gives permission to write to next/know that it won't change. *)
Definition node_fun gsh1 gsh2 (shares : list (share * val)) R a := let '(sh, g, p) := a in
  EX e : Z, EX next : val, EX lock : val, data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
  EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
  if eq_dec next (vint 0) then emp
  else atomic_loc sh next (fun (v : val) => fold_right sepcon emp
    (map (fun '(sh', gs) => EX d : option val, !!(match d with Some v' => v' = v | _ => True end) &&
    ghost_this d gs * match d with Some _ => |>R (sh', g', v) | None => emp end) shares)).

Definition node gsh1 gsh2 shares := HORec (node_fun gsh1 gsh2 shares).

Lemma node_eq' : forall gsh1 gsh2 shares,
  node gsh1 gsh2 shares = node_fun gsh1 gsh2 shares (node gsh1 gsh2 shares).
Proof.
  intros; apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 ((sh, g), p).
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
  eapply derives_trans, fold_right_sepcon_nonexpansive; [|rewrite !Zlength_map; auto].
  apply allp_right; intro i.
  destruct (zlt i 0).
  { rewrite !Znth_underflow by auto; apply eqp_refl. }
  destruct (zlt i (Zlength shares)).
  rewrite !Znth_map with (d' := (Share.bot, Vundef)) by (split; auto; omega).
  destruct (Znth i shares (Share.bot, Vundef)) eqn: Hshare.
  setoid_rewrite Hshare.
  apply eqp_exp; intro d.
  destruct d; [|apply eqp_refl].
  apply eqp_sepcon; [apply eqp_refl|].
  apply allp_left with (s, g', v); auto.
  { rewrite !Znth_overflow by (rewrite Zlength_map; auto); apply eqp_refl. }
Qed.

Corollary node_eq : forall gsh1 gsh2 shares sh g p, node gsh1 gsh2 shares (sh, g, p) =
  EX e : Z, EX next : val, EX lock : val, data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
    EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
    if eq_dec next (vint 0) then emp
    else atomic_loc sh next (fun (v : val) => fold_right sepcon emp
      (map (fun '(sh', gs) => EX d : option val, !!(match d with Some v' => v' = v | _ => True end) &&
      ghost_this d gs * match d with Some _ => |>node gsh1 gsh2 shares (sh', g', v) | None => emp end) shares)).
Proof.
  intros.
  transitivity (node_fun gsh1 gsh2 shares (node gsh1 gsh2 shares) (sh, g, p)); [|reflexivity].
  rewrite <- node_eq'; auto.
Qed.

Lemma node_isptr : forall sh gsh1 gsh2 shares g p,
  node gsh1 gsh2 shares (sh, g, p) = !!isptr p && node gsh1 gsh2 shares (sh, g, p).
Proof.
  intros; eapply local_facts_isptr with (P := fun p => node gsh1 gsh2 shares (sh, g, p)); eauto.
  rewrite node_eq.
  Intros e next lock.
  rewrite data_at_isptr; entailer!.
Qed.*)

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

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

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

Definition node_data gsh1 gsh2 sh rep p := data_at sh tnode (vint (data rep), (next rep, lock rep)) p *
  lock_inv sh (lock rep) (EX p : val, ghost_var gsh2 p (gnext rep)) *
  if eq_dec (data rep) Int.max_signed then emp
  else atomic_loc sh (next rep) (fun v => |>node gsh1 gsh2 (data rep, gnext rep, v)).

Definition node' gsh1 gsh2 p := EX sh : share, EX rep : node_rep,
  !!(readable_share sh /\ repable_signed (data rep)) && node_data gsh1 gsh2 sh rep p.

Definition new_node_spec := DECLARE _new_node
  WITH e : Z, nnext : val, sh : share, rep : node_rep, gsh1 : share, gsh2 : share
  PRE [ _e OF tint ]
    PROP (repable_signed e; readable_share sh; repable_signed (data rep); e < data rep;
          if eq_dec (data rep) Int.max_signed then next rep = nullval else True; sepalg.join gsh1 gsh2 Tsh)
    LOCAL (temp _e (vint e); temp _nnext nnext)
    SEP (node_data gsh1 gsh2 sh rep nnext)
  POST [ tptr tnode ]
   EX p : val, EX rep' : node_rep,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (node_data gsh1 gsh2 Tsh rep' p; ghost_var gsh1 nnext (gnext rep')).

Definition validate_spec := DECLARE _validate
  WITH hp : val, head : val, e : Z, pred : val, curr : val, sh : share, gsh1 : share, gsh2 : share,
    reph : node_rep, shp : share, repp : node_rep, pn : val, shc : share, repc : node_rep, nodes : list val
  PRE [ _e OF tint, _pred OF tptr tnode, _curr OF tptr tnode ]
    PROP (Int.min_signed < e < Int.max_signed; Int.min_signed <= data repp < e;
          readable_share sh; readable_share shp; readable_share shc;
          readable_share gsh1; readable_share gsh2; sepalg.join gsh1 gsh2 Tsh;
          NoDup nodes; ~In head nodes; ~In pred nodes; ~In curr nodes; e <= data repc <= Int.max_signed;
          if eq_dec pred head then shp = sh /\ repp = reph else True; data reph = Int.min_signed)
    LOCAL (gvar _head hp; temp _e (vint e); temp _pred pred; temp _curr curr)
    SEP (data_at sh (tptr tnode) head hp; if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         node_data gsh1 gsh2 shp repp pred; ghost_var gsh2 pn (gnext repp); node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes))
  POST [ tint ]
   EX b : bool, EX nodes' : list val,
    PROP (NoDup nodes'; incl nodes nodes'; ~In head nodes'; ~In pred nodes'; ~In curr nodes';
          b = true -> pn = curr)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tptr tnode) head hp; if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         node_data gsh1 gsh2 shp repp pred; ghost_var gsh2 pn (gnext repp); node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes')).

Definition locate_spec := DECLARE _locate
  WITH hp : val, head : val, e : Z, r1 : val, r2 : val, sh : share, gsh1 : share, gsh2 : share,
    reph : node_rep, nodes : list val
  PRE [ _e OF tint, _r1 OF tptr (tptr tnode), _r2 OF tptr (tptr tnode) ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; NoDup nodes; ~In head nodes; data reph = Int.min_signed)
    LOCAL (gvar _head hp; temp _e (vint e); temp _r1 r1; temp _r2 r2)
    SEP (data_at sh (tptr tnode) head hp; data_at_ Tsh (tptr tnode) r1; data_at_ Tsh (tptr tnode) r2;
         node_data gsh1 gsh2 sh reph head; fold_right sepcon emp (map (node' gsh1 gsh2) nodes))
  POST [ tvoid ]
   EX pred : val, EX shp : share, EX repp : node_rep, EX curr : val, EX shc : share, EX repc : node_rep,
   EX pc : val, EX nodes' : list val,
    PROP (readable_share shp; readable_share shc;
          data repp < e <= data repc; repable_signed (data repp); repable_signed (data repc);
          NoDup nodes'; incl nodes (pred :: curr :: nodes'); ~In head nodes'; ~In pred nodes'; ~In curr nodes';
          if eq_dec pred head then shp = sh /\ repp = reph else True)
    LOCAL ()
    SEP (data_at sh (tptr tnode) head hp; data_at Tsh (tptr tnode) pred r1; data_at Tsh (tptr tnode) curr r2;
         if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         node_data gsh1 gsh2 shp repp pred; ghost_var gsh2 curr (gnext repp);
         node_data gsh1 gsh2 shc repc curr; ghost_var gsh2 pc (gnext repc);
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes')).

(* Could we prove at least simple linearization points after all, e.g. by abstracting the list of nodes into a set
   and then showing that some atomic step in the function body has the abstract pre and postcondition? This
   wouldn't be part of a funspec as such, but it's part of RGSep methodology. (See the marked steps in Figure 2
   of Proving Correctness of Highly-Concurrent Linearisable Objects, Vafeiadis et al, PPoPP 2006. *)
(* Without such an approach, we don't get much useful information out of the return value, unless we use
   histories to say that writes occur only on a successful add (which we can, along the lines of hashtable1). *)
Definition add_spec := DECLARE _add
  WITH hp : val, head : val, e : Z, sh : share, gsh1 : share, gsh2 : share, reph : node_rep, nodes : list val
  PRE [ _e OF tint ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; NoDup nodes; ~In head nodes; data reph = Int.min_signed)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; node_data gsh1 gsh2 sh reph head;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes))
  POST [ tint ]
   EX b : bool, EX sh' : share, EX rep' : node_rep, EX n' : val, EX nodes' : list val,
    PROP (readable_share sh'; data rep' = e; if b then incl nodes nodes' else incl nodes (n' :: nodes');
          ~In head nodes'; ~In n' nodes)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (node_data gsh1 gsh2 sh' rep' n';
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes')).

(* A useful spec for remove is even more unclear. How do we know the removed node is no longer in the list? *)
Definition remove_spec := DECLARE _remove
  WITH hp : val, head : val, e : Z, sh : share, gsh1 : share, gsh2 : share, reph : node_rep, nodes : list val
  PRE [ _e OF tint ]
    PROP (Int.min_signed < e < Int.max_signed; readable_share sh; readable_share gsh1; readable_share gsh2;
          sepalg.join gsh1 gsh2 Tsh; NoDup nodes; ~In head nodes; data reph = Int.min_signed)
    LOCAL (gvar _head hp; temp _e (vint e))
    SEP (data_at sh (tptr tnode) head hp; node_data gsh1 gsh2 sh reph head;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes))
  POST [ tint ]
   EX b : bool, EX n' : val, EX nodes' : list val,
    PROP (if b then incl nodes (n' :: nodes') else incl nodes nodes'; ~In head nodes';
          if b then ~In n' nodes else True)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (if b then EX sh' : share, EX rep' : node_rep, EX n' : val, !!(readable_share sh' /\ data rep' = e) &&
           node_data gsh1 gsh2 sh' rep' n' else emp;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes')).

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; load_SC_spec;
  validate_spec; locate_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

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
  intros; unfold node_data.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
  do 4 apply sepcon_derives_prop; rewrite sepcon_comm; apply node_val_eq; auto.
Qed.

Lemma node_data_valid_pointer : forall gsh1 gsh2 sh rep p, readable_share sh ->
  node_data gsh1 gsh2 sh rep p |-- valid_pointer p.
Proof.
  intros; unfold node_data.
  rewrite sepcon_assoc; apply sepcon_valid_pointer1, data_at_valid_ptr; auto; simpl; computable.
Qed.

Lemma node_data_isptr : forall gsh1 gsh2 sh rep p,
  node_data gsh1 gsh2 sh rep p = !!isptr p && node_data gsh1 gsh2 sh rep p.
Proof.
  intros.
  eapply local_facts_isptr; [|eauto].
  unfold node_data; entailer!.
Qed.

Lemma body_validate : semax_body Vprog Gprog f_validate validate_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS, abbreviate.
  assert (repable_signed (data repp)) by (split; omega).
  assert (repable_signed (data repc)) by (split; omega).
  assert (repable_signed (data reph)) by (replace (data reph) with Int.min_signed; split; computable).
  destruct (eq_dec pred curr).
  { gather_SEP 2 4; assert_PROP (data repp = data repc); [|omega].
    go_lower; subst; apply sepcon_derives_prop, node_data_eq; auto. }
  destruct (eq_dec head curr).
  { subst; destruct (eq_dec pred curr); [contradiction|].
    gather_SEP 1 4; assert_PROP (data reph = data repc); [|omega].
    go_lower; apply sepcon_derives_prop, node_data_eq; auto. }
  rewrite seq_assoc; eapply semax_seq with
  (Q := EX succ : val, EX shs : share, EX reps : node_rep, EX nodes1 : list val,
    PROP (readable_share shs; repable_signed (data reps); NoDup nodes1; ~In head nodes1; ~In succ nodes1;
          ~In pred nodes1; ~In curr nodes1; incl nodes (succ :: nodes1);
          if eq_dec succ curr then shs = shc /\ reps = repc
          else if eq_dec succ pred then shs = shp /\ reps = repp
          else if eq_dec succ head then shs = sh /\ reps = reph else True)
    LOCAL (temp _v (vint (data reps)); temp _succ succ; gvar _head hp; temp _e (vint e); temp _pred pred;
           temp _curr curr)
    SEP (node_data gsh1 gsh2 shs reps succ; data_at sh (tptr tnode) head hp;
         if eq_dec pred head then emp else if eq_dec succ head then emp else node_data gsh1 gsh2 sh reph head;
         if eq_dec succ pred then emp else node_data gsh1 gsh2 shp repp pred; ghost_var gsh2 pn (gnext repp);
         if eq_dec succ curr then emp else node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes1))).
  destruct (eq_dec pred head).
  { match goal with H : _ /\ _ |- _ => destruct H; subst end.
    unfold node_data at 1; Intros; repeat forward.
    Exists head sh reph nodes; rewrite !eq_dec_refl; destruct (eq_dec head curr); [contradiction | entailer!].
    apply incl_tl, incl_refl. }
  { unfold node_data at 1; Intros; repeat forward.
    Exists head sh reph nodes; rewrite !eq_dec_refl.
    destruct (eq_dec head pred); [subst; contradiction|].
    destruct (eq_dec head curr); [contradiction | entailer!].
    apply incl_tl, incl_refl. }
  unfold Swhile.
  eapply semax_seq' with (P' := EX succ : val, EX shs : share, EX reps : node_rep, EX nodes1 : list val,
    PROP (readable_share shs; repable_signed (data reps); NoDup nodes1; ~In head nodes1; ~In succ nodes1;
          ~In pred nodes1; ~In curr nodes1; incl nodes (succ :: nodes1); succ <> head;
          if eq_dec succ curr then shs = shc /\ reps = repc
          else if eq_dec succ pred then shs = shp /\ reps = repp else True; e <= data reps)
    LOCAL (temp _v (vint (data reps)); temp _succ succ; gvar _head hp; temp _e (vint e); temp _pred pred;
           temp _curr curr)
    SEP (node_data gsh1 gsh2 shs reps succ; data_at sh (tptr tnode) head hp;
         if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         if eq_dec succ pred then emp else node_data gsh1 gsh2 shp repp pred; ghost_var gsh2 pn (gnext repp);
         if eq_dec succ curr then emp else node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes1))).
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  - (* loop body *)
    Intros succ shs reps nodes1.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (data reps < e) (LOCALx Q (SEPx R))) end.
    { forward; entailer!. }
    { forward.
      destruct (eq_dec succ head).
      { destruct (eq_dec succ curr); [subst; contradiction|].
        destruct (eq_dec succ pred); [|match goal with H : _ /\ _ |- _ => destruct H; subst; omega end].
        subst; rewrite eq_dec_refl in *.
        repeat match goal with H : _ /\ _ |- _ => destruct H; subst end; omega. }
      Exists succ shs reps nodes1; entailer!. }
    Intros; destruct (eq_dec succ curr).
    { match goal with H : _ /\ _ |- _ => destruct H; subst; omega end. }
    unfold node_data at 1.
    Intros; destruct (eq_dec (data reps) Int.max_signed); [omega|].
    rewrite atomic_loc_isptr; Intros.
    forward.
    forward_call (shs, next reps, data_at shs tnode (vint (data reps), (next reps, lock reps)) succ *
      (if eq_dec succ pred then emp else node_data gsh1 gsh2 shp repp pred) *
      node_data gsh1 gsh2 shc repc curr * fold_right sepcon emp (map (node' gsh1 gsh2) nodes1),
      fun v => |>node gsh1 gsh2 (data reps, gnext reps, v),
      fun v => |>(data_at shs tnode (vint (data reps), (next reps, lock reps)) succ *
        (if eq_dec succ pred then emp else if eq_dec v pred then emp else node_data gsh1 gsh2 shp repp pred) *
        (if eq_dec v curr then emp else node_data gsh1 gsh2 shc repc curr) *
        fold_right sepcon emp (map (node' gsh1 gsh2) (remove EqDec_val v nodes1)) *
        EX shs' : share, EX reps' : node_rep,
          !!(readable_share shs' /\ repable_signed (data reps') /\ data reps < data reps' /\
             if eq_dec v pred then shs' = shp /\ reps' = repp
             else if eq_dec v curr then shs' = shc /\ reps' = repc else True) && node_data gsh1 gsh2 shs' reps' v)).
    { split; auto.
      intros ??????? Ha.
      eapply semax_pre; try apply Ha; go_lowerx.
      apply sepcon_derives; [|auto].
      rewrite <- add_andp by admit.
      rewrite <- later_sepcon.
      eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
      rewrite node_eq; unfold node'.
      Intros sh' e' next' lock' g'.
      destruct (in_dec EqDec_val vx nodes1).
      + destruct (eq_dec vx pred); [subst; contradiction|].
        destruct (eq_dec vx curr); [subst; contradiction|].
        apply in_split in i; destruct i as (? & ? & ?); subst.
        rewrite map_app, sepcon_app; simpl.
        Intros sh'' rep'; unfold node_data.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
        assert_PROP (data rep' = e').
        { do 12 apply sepcon_derives_prop; apply node_val_eq; auto. }
        rewrite remove_from_NoDup, map_app, sepcon_app by auto.
        Exists sh' e' next' lock' sh'' rep' g'; entailer!.
      + rewrite remove_out by auto.
        destruct (eq_dec vx pred); [|destruct (eq_dec vx curr)].
        * destruct (eq_dec succ pred); subst.
          { rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
            assert_PROP (data reps = e'); [|omega].
            do 6 apply sepcon_derives_prop; apply node_val_eq; auto. }
          assert_PROP (data repp = e').
          { unfold node_data at 1; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ pred)),
              <- !sepcon_assoc.
            do 8 apply sepcon_derives_prop; apply node_val_eq; auto. }
          Exists sh' e' next' lock' g' shp repp; entailer!.
          if_tac; auto; contradiction.
        * subst; assert_PROP (data repc = e').
          { unfold node_data at 2; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ curr)),
              <- !sepcon_assoc.
            do 8 apply sepcon_derives_prop; apply node_val_eq; auto. }
          Exists sh' e' next' lock' g' shc repc; entailer!.
        * exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
          Exists sh1 e' next' lock' g' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |}.
          erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
          unfold node_data; simpl; entailer!.
          if_tac; [entailer!|].
          erewrite atomic_loc_join; eauto. }
    Intros succ'.
    rewrite !later_sepcon, (later_exp' _ Share.bot); Intro shs'.
    rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro reps'.
    hoist_later_in_pre.
    focus_SEP 5.
    erewrite extract_prop_in_SEP with (n := 0%nat); [|simpl; eauto].
    simpl replace_nth.
    unfold node_data at 1; rewrite !flatten_sepcon_in_SEP.
    apply assert_later_PROP with (P1 := readable_share shs'); [entailer!; tauto | intro].
    forward.
    Exists succ' shs' reps' (if eq_dec succ pred then remove EqDec_val succ' nodes1
      else if eq_dec succ head then remove EqDec_val succ' nodes1 else succ :: remove EqDec_val succ' nodes1).
    destruct (eq_dec succ' succ).
    { gather_SEP 0 4.
      assert_PROP (data reps' = data reps); [|omega].
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    destruct (eq_dec succ' head).
    { destruct (eq_dec succ head); [subst; contradiction|].
      assert_PROP (data reps' = data reph); [|unfold repable_signed in *; omega].
      destruct (eq_dec pred head).
      { subst; match goal with H : if eq_dec head head then _ else _ |- _ => rewrite eq_dec_refl in H end.
        repeat match goal with H : _ /\ _ |- _ => destruct H; subst end; apply prop_right; auto. }
      unfold node_data; Intros.
      gather_SEP 0 10.
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    unfold node_data; entailer!.
    + destruct (eq_dec succ pred); [|destruct (eq_dec succ head)].
      * split; [apply remove_NoDup; auto|].
        repeat (split; [try apply remove_In; intro X; apply In_remove in X; destruct X; contradiction|]).
        subst; split; [match goal with H : incl nodes _ |- _ =>
          apply incl_cons_out in H; auto; apply incl_remove_add; auto end|].
        destruct (eq_dec succ' pred); [contradiction|].
        if_tac; auto.
      * split; [apply remove_NoDup; auto|].
        repeat (split; [try apply remove_In; intro X; apply In_remove in X; destruct X; contradiction|]).
        subst; split; [match goal with H : incl nodes _ |- _ =>
          apply incl_cons_out in H; auto; apply incl_remove_add; auto end|].
        destruct (eq_dec succ' curr), (eq_dec succ' pred); subst; auto; contradiction.
      * split; [constructor; [rewrite In_remove | apply remove_NoDup]; auto; tauto|].
        repeat (split; [simpl; intros [|X]; subst; [contradiction|]; try apply remove_In in X; auto;
          apply In_remove in X; destruct X; contradiction|]).
        split.
        { match goal with H : incl nodes _ |- _ => apply (@incl_remove_add _ EqDec_val succ') in H;
            simpl in H end.
          destruct (EqDec_val succ' succ); [contradiction | auto]. }
        destruct (eq_dec succ' curr), (eq_dec succ' pred); subst; auto; contradiction.
    + destruct (eq_dec succ pred); [|destruct (eq_dec succ head)].
      * destruct (eq_dec succ' pred); [subst; contradiction|].
        destruct (eq_dec (data repp) Int.max_signed); [omega | cancel].
        match goal with H : _ /\ _ |- _ => destruct H; subst end.
        if_tac; cancel.
      * destruct (eq_dec pred head); [subst; contradiction|].
        match goal with H : _ /\ _ |- _ => destruct H; subst end.
        destruct (eq_dec (data reph) Int.max_signed); [omega | cancel].
      * simpl; cancel.
        unfold node', node_data.
        Exists shs reps; if_tac; [contradiction | entailer!].
  - abbreviate_semax.
    Intros succ shs reps nodes'.
    destruct (eq_dec succ pred).
    { destruct (eq_dec succ curr); [subst; contradiction|].
      match goal with H : _ /\ _ |- _ => destruct H; subst; omega end. }
    unfold node_data at 3; Intros.
    destruct (eq_dec (data repp) Int.max_signed); [omega|].
    rewrite (atomic_loc_isptr shp); Intros.
    forward.
    forward_call (shp, next repp, ghost_var gsh2 pn (gnext repp) * node_data gsh1 gsh2 shs reps succ *
      (if eq_dec succ curr then emp else node_data gsh1 gsh2 shc repc curr) *
      fold_right sepcon emp (map (node' gsh1 gsh2) nodes'),
      fun v => |>node gsh1 gsh2 (data repp, gnext repp, v),
      fun v => |>(!!(v = pn) && ghost_var gsh2 pn (gnext repp) *
        (if eq_dec v succ then emp else node_data gsh1 gsh2 shs reps succ) *
        (if eq_dec v curr then emp else if eq_dec succ curr then emp else node_data gsh1 gsh2 shc repc curr) *
        fold_right sepcon emp (map (node' gsh1 gsh2) (remove EqDec_val v nodes')) *
        EX shn : share, EX repn : node_rep,
          !!(readable_share shn /\ repable_signed (data repn) /\ data repp < data repn /\
          if eq_dec v succ then shn = shs /\ repn = reps else if eq_dec v curr then shn = shc /\ repn = repc
          else True) && node_data gsh1 gsh2 shn repn v)).
    { split; auto.
      repeat intro.
      eapply semax_pre; [|eauto].
      rewrite node_eq; go_lowerx.
      apply sepcon_derives; [|auto].
      rewrite <- add_andp by admit.
      eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
      rewrite <- !later_sepcon; apply later_derives.
      Intros sh' e' next' lock' g'.
      apply andp_right.
      { rewrite sepcon_comm, <- !sepcon_assoc; do 2 apply sepcon_derives_prop.
        rewrite sepcon_comm, <- !sepcon_assoc; do 4 apply sepcon_derives_prop.
        apply ghost_var_inj; auto. }
      destruct (in_dec EqDec_val vx nodes').
      + destruct (eq_dec vx succ); [subst; contradiction|].
        destruct (eq_dec vx curr); [subst; contradiction|].
        apply in_split in i; destruct i as (? & ? & ?); subst.
        rewrite map_app, sepcon_app; simpl.
        unfold node' at 2; Intros sh'' rep'; unfold node_data.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
        assert_PROP (data rep' = e').
        { do 12 apply sepcon_derives_prop; apply node_val_eq; auto. }
        rewrite remove_from_NoDup, map_app, sepcon_app by auto.
        Exists sh' e' next' lock' sh'' rep' g'; entailer!.
      + rewrite remove_out by auto.
        destruct (eq_dec vx succ); [|destruct (eq_dec vx curr)]; subst.
        * assert_PROP (data reps = e').
          { unfold node_data at 1; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ succ)),
              <- !sepcon_assoc.
            do 8 apply sepcon_derives_prop; apply node_val_eq; auto. }
          Exists sh' e' next' lock' g' shs reps; entailer!.
          if_tac; auto; contradiction.
        * destruct (eq_dec succ curr); [subst; contradiction|].
          assert_PROP (data repc = e').
          { unfold node_data at 2; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ curr)),
              <- !sepcon_assoc.
            do 8 apply sepcon_derives_prop; apply node_val_eq; auto. }
          Exists sh' e' next' lock' g' shc repc; entailer!.
        * exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
          Exists sh1 e' next' lock' g' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |}.
          erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
          unfold node_data; simpl; entailer!.
          if_tac; [entailer!|].
          erewrite atomic_loc_join; eauto. }
    Intros n'.
    hoist_later_in_pre; apply assert_later_PROP with (P1 := isptr pn).
    { Intros shn repn; rewrite (node_data_isptr _ _ shn); entailer!. }
    intro; apply assert_later_PROP with (P1 := isptr succ).
    { Intros; subst.
      destruct (eq_dec pn succ); [apply prop_right; subst; auto|].
      rewrite node_data_isptr; entailer!. }
    intro; apply assert_later_PROP with (P1 := isptr curr).
    { Intros; subst.
      destruct (eq_dec pn curr); [apply prop_right; subst; auto|].
      destruct (eq_dec succ curr); [apply prop_right; subst; auto|].
      rewrite (node_data_isptr _ _ shc); entailer!. }
    intro; forward.
    { entailer!.
      destruct (eq_dec pn succ).
      + rewrite (sepcon_comm _ (node_data _ _ _ _ _)), !sepcon_assoc; eapply derives_trans;
          [apply sepcon_derives, derives_refl; apply node_data_valid_pointer; auto|].
        subst; apply denote_tc_test_eq_split; [entailer!|].
        destruct (eq_dec succ curr); [entailer!|].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (node_data _ _ _ _ _)), !sepcon_assoc.
        apply sepcon_valid_pointer1, node_data_valid_pointer; auto.
      + rewrite (sepcon_comm _ (node_data _ _ _ _ succ)), !sepcon_assoc; eapply derives_trans;
          [apply sepcon_derives, derives_refl; apply node_data_valid_pointer; auto|].
        subst; apply denote_tc_test_eq_split; [entailer!|].
        destruct (eq_dec succ curr); [entailer!|].
        destruct (eq_dec pn curr); subst;
          rewrite <- !sepcon_assoc, (sepcon_comm _ (node_data _ _ _ _ curr)), !sepcon_assoc;
          apply sepcon_valid_pointer1, node_data_valid_pointer; auto. }
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP ()(LOCALx (temp _t'3 (Val.of_bool
        (if eq_dec succ curr then if eq_dec n' curr then true else false else false)) :: Q) (SEPx R))) end.
    { forward.
      { entailer!.
        rewrite (sepcon_comm _ (node_data _ _ _ _ _)), !sepcon_assoc; eapply derives_trans;
          [apply sepcon_derives, derives_refl; apply node_data_valid_pointer; auto|].
        apply denote_tc_test_eq_split; [entailer!|].
        destruct (eq_dec pn curr); [entailer!|].
        destruct (eq_dec succ curr); [destruct (eq_dec pn succ); [subst; contradiction|]|]; subst;
          rewrite <- !sepcon_assoc, (sepcon_comm _ (node_data _ _ _ _ curr)), !sepcon_assoc;
          apply sepcon_valid_pointer1, node_data_valid_pointer; auto. }
      entailer!.
      simpl; rewrite force_sem_cmp_pp in * by auto.
      destruct (eq_dec succ curr); [|discriminate].
      if_tac; auto. }
    { forward.
      entailer!.
      rewrite force_sem_cmp_pp in * by auto.
      if_tac; [discriminate | auto]. }
    repeat forward.
    Exists (if eq_dec succ curr then if eq_dec pn curr then true else false else false)
      ((if eq_dec pn curr then [] else [pn]) ++
       (if eq_dec succ curr then [] else if eq_dec pn succ then [] else [succ]) ++ remove EqDec_val pn nodes').
    destruct (eq_dec pn curr).
    + subst; rewrite remove_out by auto.
      destruct (eq_dec succ curr).
      * subst.
        match goal with H : if eq_dec ?a ?a then _ else _ |- _ => rewrite eq_dec_refl in H; destruct H end.
        match goal with H : _ /\ _ |- _ => destruct H; subst end.
        match goal with H : incl nodes _ |- _ => apply incl_cons_out in H; auto end.
        unfold node_data; simpl.
        destruct (eq_dec (data repp) Int.max_signed); [omega|].
        rewrite eq_dec_refl; entailer!.
      * destruct (eq_dec curr succ); subst; [contradiction|].
        repeat match goal with H : _ /\ _ |- _ => destruct H; subst end.
        unfold node_data; simpl; entailer!.
        { split; [constructor; auto | tauto]. }
        unfold node', node_data; simpl.
        destruct (eq_dec (data repp) Int.max_signed); [omega|].
        Exists shs reps; entailer!.
    + destruct (eq_dec pn pred).
      { destruct (eq_dec pn succ); [subst; contradiction|].
        rewrite (sepcon_comm _ (node_data _ _ shn _ _)), (sepcon_comm _ (data_at shp _ _ _)).
        assert_PROP (data repp = data repn); [|omega].
        unfold node_data; rewrite <- !sepcon_assoc; do 12 apply sepcon_derives_prop.
        subst; apply node_val_eq; auto. }
      destruct (eq_dec pn head).
      { destruct (eq_dec pn succ); [subst; contradiction|].
        destruct (eq_dec pred head); [subst; contradiction|].
        rewrite (sepcon_comm _ (node_data _ _ shn _ _)), (sepcon_comm _ (node_data _ _ sh _ _)).
        assert_PROP (data reph = data repn); [|omega].
        rewrite <- !sepcon_assoc; do 8 apply sepcon_derives_prop.
        subst; apply node_data_eq; auto. }
      destruct (eq_dec succ curr).
      * match goal with H : _ /\ _ |- _ => destruct H; subst end.
        destruct (eq_dec pn curr); [subst; contradiction|].
        match goal with H : incl nodes _ |- _ => apply incl_cons_out in H; auto end.
        unfold node', node_data; simpl.
        destruct (eq_dec (data repp) Int.max_signed); [omega|].
        destruct (eq_dec pn curr); [subst; contradiction|].
        entailer!.
        { split; [constructor; [apply remove_In | apply remove_NoDup]; auto|].
          split; [apply incl_remove_add; auto|].
          repeat (split; [intros [|X]; [subst; contradiction|]; apply In_remove in X; destruct X; contradiction|]).
          discriminate. }
        Exists shn repn; entailer!.
      * destruct (eq_dec pn succ); simpl; [subst; rewrite remove_out by auto|]; entailer!.
        -- split; [constructor; auto|].
           repeat (split; [tauto|]); discriminate.
        -- unfold node', node_data; destruct (eq_dec (data repp) Int.max_signed); [omega|].
           match goal with H : _ /\ _ |- _ => destruct H; subst end.
           Exists shs reps; entailer!.
        -- split.
           { repeat constructor; try apply remove_NoDup; auto.
             { simpl; intros [|X]; [subst; contradiction|].
               apply remove_In in X; auto. }
             { intro X; apply In_remove in X; destruct X; contradiction. } }
           split.
           { match goal with H : incl nodes _ |- _ => apply (@incl_remove_add _ EqDec_val pn) in H;
               simpl in H end.
             destruct (EqDec_val pn succ); [contradiction | auto]. }
           repeat (split; [intros [|[|X]]; subst; try contradiction; apply In_remove in X; destruct X;
             contradiction|]); discriminate.
        -- unfold node', node_data; destruct (eq_dec (data repp) Int.max_signed); [omega|].
           Exists shs reps shn repn; entailer!.
Admitted.

Lemma body_locate : semax_body Vprog Gprog f_locate locate_spec.
Proof.
  start_function.
  eapply semax_pre with (P' := EX nodes0 : list val, PROP (NoDup nodes0; incl nodes nodes0; ~In head nodes0)
   LOCAL (gvar _head hp; temp _e (vint e); temp _r1 r1; temp _r2 r2)
   SEP (data_at sh (tptr tnode) head hp; data_at_ Tsh (tptr tnode) r1;
        data_at_ Tsh (tptr tnode) r2; node_data gsh1 gsh2 sh reph head;
        fold_right sepcon emp (map (node' gsh1 gsh2) nodes0))).
  { Exists nodes; entailer!.
    apply incl_refl. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intros nodes0.
  forward.
  unfold node_data.
  destruct (eq_dec (data reph) Int.max_signed); [omega|].
  rewrite data_at_isptr, atomic_loc_isptr; Intros.
  repeat forward.
  forward_call (sh, next reph, fold_right sepcon emp (map (node' gsh1 gsh2) nodes0),
    fun v => |>node gsh1 gsh2 (data reph, gnext reph, v),
    fun v => |>(fold_right sepcon emp (map (node' gsh1 gsh2) (remove EqDec_val v nodes0)) *
      EX shc : share, EX repc : node_rep,
        !!(readable_share shc /\ repable_signed (data repc) /\ data reph < data repc) &&
        node_data gsh1 gsh2 shc repc v)).
  { split; auto.
    intros ??????? Ha.
    eapply semax_pre; try apply Ha; go_lowerx.
    apply sepcon_derives; [|auto].
    rewrite <- add_andp by admit.
    rewrite <- later_sepcon.
    eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
    rewrite node_eq; unfold node'.
    Intros sh' e' next' lock' g'.
    destruct (in_dec EqDec_val vx nodes0).
    + apply in_split in i; destruct i as (? & ? & ?); subst.
      rewrite map_app, sepcon_app; simpl.
      Intros sh'' rep'; unfold node_data.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
      assert_PROP (data rep' = e').
      { do 7 apply sepcon_derives_prop; apply node_val_eq; auto. }
      rewrite remove_from_NoDup, map_app, sepcon_app by auto.
      Exists sh' e' next' lock' sh'' rep' g'; entailer!.
    + rewrite remove_out by auto.
      exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
      Exists sh1 e' next' lock' g' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |}.
      erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
      unfold node_data; simpl; entailer!.
      if_tac; [entailer!|].
      erewrite atomic_loc_join; eauto. }
  Intros curr.
  rewrite later_sepcon, (later_exp' _ Share.bot); Intro shc.
  rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro repc.
  hoist_later_in_pre.
  focus_SEP 2.
  erewrite extract_prop_in_SEP with (n := O); [|simpl; eauto].
  simpl replace_nth.
  unfold node_data at 1; rewrite !flatten_sepcon_in_SEP.
  apply assert_later_PROP with (P1 := readable_share shc); [entailer!; tauto | intro].
  forward.
  assert (repable_signed (data reph)) by (replace (data reph) with Int.min_signed; split; computable).
  destruct (eq_dec head curr).
  { subst; gather_SEP 0 8.
    assert_PROP (data repc = data reph); [|omega].
    go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
  eapply semax_pre with (P' := EX pred : val, EX shp : share, EX repp : node_rep,
    EX curr : val, EX shc : share, EX repc : node_rep, EX nodes1 : list val,
    PROP (readable_share shp; readable_share shc; repable_signed (data repp); repable_signed (data repc);
          pred <> curr; curr <> head; data repp < e; data repp < data repc; NoDup nodes1;
          ~In head nodes1; ~In pred nodes1; ~In curr nodes1; incl nodes (pred :: curr :: nodes1);
          if eq_dec pred head then shp = sh /\ repp = reph else data reph < data repp)
    LOCAL (temp _v (vint (data repc)); temp _curr curr; temp _pred pred;
           gvar _head hp; temp _e (vint e); temp _r1 r1; temp _r2 r2)
    SEP (data_at sh (tptr tnode) head hp; data_at_ Tsh (tptr tnode) r1; data_at_ Tsh (tptr tnode) r2;
         if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         node_data gsh1 gsh2 shp repp pred; node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes1))).
  { Exists head sh reph curr shc repc (remove EqDec_val curr nodes0); rewrite !eq_dec_refl; unfold node_data;
      entailer!.
    { split; [omega|].
      split; [apply remove_NoDup; auto|].
      repeat (split; [intro X; apply In_remove in X; destruct X; contradiction|]).
      apply incl_tl, incl_remove_add; auto. }
    if_tac; auto; omega. }
  abbreviate_semax.
  clear dependent curr; clear dependent shc; clear dependent repc.
  eapply semax_seq' with (P' := EX pred : val, EX shp : share, EX repp : node_rep,
    EX curr : val, EX shc : share, EX repc : node_rep, EX nodes1 : list val,
    PROP (readable_share shp; readable_share shc; repable_signed (data repp); repable_signed (data repc);
          pred <> curr; curr <> head; data repp < e <= data repc; NoDup nodes1;
          ~In head nodes1; ~In pred nodes1; ~In curr nodes1; incl nodes (pred :: curr :: nodes1);
          if eq_dec pred head then shp = sh /\ repp = reph else data reph < data repp)
    LOCAL (temp _v (vint (data repc)); temp _curr curr; temp _pred pred;
           gvar _head hp; temp _e (vint e); temp _r1 r1; temp _r2 r2)
    SEP (data_at sh (tptr tnode) head hp; data_at_ Tsh (tptr tnode) r1; data_at_ Tsh (tptr tnode) r2;
         if eq_dec pred head then emp else node_data gsh1 gsh2 sh reph head;
         node_data gsh1 gsh2 shp repp pred; node_data gsh1 gsh2 shc repc curr;
         fold_right sepcon emp (map (node' gsh1 gsh2) nodes1))).
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  - (* loop body *)
    Intros pred shp repp curr shc repc nodes1.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (data repc < e) (LOCALx Q (SEPx R))) end.
    { forward; entailer!. }
    { forward.
      Exists pred shp repp curr shc repc nodes1; entailer!. }
    forward.
    unfold node_data at 3; Intros.
    destruct (eq_dec (data repc) Int.max_signed); [omega|].
    rewrite atomic_loc_isptr; Intros.
    forward.
    forward_call (shc, next repc, fold_right sepcon emp (map (node' gsh1 gsh2) nodes1),
      fun v => |>node gsh1 gsh2 (data repc, gnext repc, v),
      fun v => |>(fold_right sepcon emp (map (node' gsh1 gsh2) (remove EqDec_val v nodes1)) *
        EX sh' : share, EX rep' : node_rep,
          !!(readable_share sh' /\ repable_signed (data rep') /\ data repc < data rep') &&
          node_data gsh1 gsh2 sh' rep' v)).
    { split; auto.
      intros ??????? Ha.
      eapply semax_pre; try apply Ha; go_lowerx.
      apply sepcon_derives; [|auto].
      rewrite <- add_andp by admit.
      rewrite <- later_sepcon.
      eapply derives_trans, later_derives; [rewrite later_sepcon; apply sepcon_derives, now_later; auto|].
      rewrite node_eq; unfold node'.
      Intros sh' e' next' lock' g'.
      destruct (in_dec EqDec_val vx nodes1).
      + apply in_split in i; destruct i as (? & ? & ?); subst.
        rewrite map_app, sepcon_app; simpl.
        Intros sh'' rep'; unfold node_data.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ _)), <- !sepcon_assoc.
        assert_PROP (data rep' = e').
        { do 7 apply sepcon_derives_prop; apply node_val_eq; auto. }
        rewrite remove_from_NoDup, map_app, sepcon_app by auto.
        Exists sh' e' next' lock' sh'' rep' g'; entailer!.
      + rewrite remove_out by auto.
        exploit split_readable_share; eauto; intros (sh1 & sh2 & ? & ? & Hsh).
        Exists sh1 e' next' lock' g' sh2 {| data := e'; next := next'; lock := lock'; gnext := g' |}.
        erewrite <- data_at_share_join, <- lock_inv_share_join; try apply Hsh; auto.
        unfold node_data; simpl; entailer!.
        if_tac; [entailer!|].
        erewrite atomic_loc_join; eauto. }
    Intros curr'.
    rewrite !later_sepcon, (later_exp' _ Share.bot); Intro sh'.
    rewrite (later_exp' _ {| data := 0; next := Vundef; lock := Vundef; gnext := Vundef|}); Intro rep'.
    hoist_later_in_pre.
    focus_SEP 2.
    erewrite extract_prop_in_SEP with (n := 0%nat); [|simpl; eauto].
    simpl replace_nth.
    unfold node_data at 1; rewrite !flatten_sepcon_in_SEP.
    apply assert_later_PROP with (P1 := readable_share sh'); [entailer!; tauto | intro].
    forward.
    Exists curr shc repc curr' sh' rep' (if eq_dec pred head then remove EqDec_val curr' nodes1
      else pred :: remove EqDec_val curr' nodes1).
    destruct (eq_dec curr' curr).
    { gather_SEP 0 10.
      assert_PROP (data rep' = data repc); [|omega].
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    destruct (eq_dec curr' pred).
    { unfold node_data; Intros; gather_SEP 0 9.
      assert_PROP (data rep' = data repp); [|omega].
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    destruct (eq_dec curr' head).
    { destruct (eq_dec pred head); subst; [contradiction|].
      unfold node_data; Intros; gather_SEP 0 8.
      assert_PROP (data rep' = data reph); [|omega].
      subst; go_lower; apply sepcon_derives_prop, node_val_eq; auto. }
    destruct (eq_dec curr head); [contradiction|].
    unfold node_data; entailer!.
    + if_tac.
      * split; [apply remove_NoDup; auto|].
        repeat (split; [try apply remove_In; intro X; apply In_remove in X; destruct X; contradiction|]).
        subst; split.
        { intros ? Hin.
          match goal with H : incl nodes _ |- _ => apply incl_cons_out in H; auto; specialize (H _ Hin);
            destruct H; simpl; auto end.
          rewrite In_remove; destruct (eq_dec a curr'); auto. }
        match goal with H : _ /\ _ |- _ => destruct H; subst; omega end.
      * split; [constructor; [rewrite In_remove | apply remove_NoDup]; auto; tauto|].
        repeat (split; [simpl; intros [|X]; subst; [contradiction|]; try apply remove_In in X; auto;
          apply In_remove in X; destruct X; contradiction|]).
        split.
        { intros ? Hin.
          match goal with H : incl nodes _ |- _ => specialize (H _ Hin); destruct H as [|[|]]; simpl; auto end.
          rewrite In_remove; destruct (eq_dec a curr'); auto. }
        omega.
    + destruct (eq_dec (data repc) Int.max_signed); [omega|].
      if_tac.
      * match goal with H : _ /\ _ |- _ => destruct H; subst; cancel end.
      * simpl; cancel.
        unfold node', node_data.
        Exists shp repp; if_tac; [omega | entailer!].
  - abbreviate_semax.
    Intros pred shp repp curr shc repc nodes1.
    unfold node_data at 2 3; rewrite (lock_inv_isptr shp), (lock_inv_isptr shc); Intros; repeat forward.
    forward_call (lock repp, shp, EX p : val, ghost_var gsh2 p (gnext repp)).
    forward_call (lock repc, shc, EX p : val, ghost_var gsh2 p (gnext repc)).
    Intros cn pn.
    forward_call (hp, head, e, pred, curr, sh, gsh1, gsh2, reph, shp, repp, pn, shc, repc, nodes1).
    { unfold node_data; entailer!. }
    { split; [auto|].
      split; [unfold repable_signed in *; tauto|].
      repeat (split; auto); unfold repable_signed in *; try tauto.
      if_tac; auto. }
    Intros x; destruct x as (b & nodes').
    gather_SEP 3 6.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx R))) end.
    { subst; match goal with H : _ = _ -> _ |- _ => specialize (H eq_refl); subst end.
      repeat forward.
      Exists pred shp repp curr shc repc cn nodes'; entailer!.
      split; [|if_tac; auto].
      eapply incl_tran; eauto.
      intros ? [|[|]]; simpl; auto. }
    { forward_call (lock repp, shp, EX p : val, ghost_var gsh2 p (gnext repp)).
      { unfold node_data; lock_props.
        { admit. (* probably not actually positive *) }
        Exists pn; cancel. }
      forward_call (lock repc, shc, EX p : val, ghost_var gsh2 p (gnext repc)).
      { unfold node_data; lock_props.
        { admit. (* probably not actually positive *) }
        Exists cn; cancel. }
      unfold node_data; entailer!. }
    intros; unfold overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    unfold POSTCONDITION, abbreviate, loop1_ret_assert.
    Intros.
    Exists (if eq_dec pred head then curr :: nodes' else pred :: curr :: nodes'); entailer!.
    + if_tac.
      * split; [constructor; auto|].
        split; [|simpl; tauto].
        match goal with H : _ /\ _ |- _ => destruct H; subst end.
        match goal with H : incl nodes _ |- _ => apply incl_cons_out in H; auto;
          intros ? Hin; specialize (H _ Hin); destruct H; simpl; auto end.
      * split; [repeat constructor; auto; simpl in *; intros [|]; subst; contradiction|].
        split; [|simpl; tauto].
        match goal with H : incl nodes _ |- _ => intros ? Hin; specialize (H _ Hin); destruct H as [|[|]];
          simpl; auto end.
    + if_tac; [match goal with H : _ /\ _ |- _ => destruct H; subst end|]; simpl; cancel; unfold node'.
      * Exists shc repc; entailer!.
      * Exists shp repp shc repc; entailer!.
Admitted.

Lemma body_add : semax_body Vprog Gprog f_add add_spec.
Proof.
  name r1 _n1; name r3 _n3.
  start_function.
  forward_call (hp, head, e, r1, r3, sh, gsh1, gsh2, reph, nodes).
  { unfold tnode; cancel. }
  { tauto. }
  Intros x; destruct x as (((((((pred, shp), repp), curr), shc), repc), cn), nodes1); simpl in *.
  unfold node_data at 3; Intros.
  forward.
  forward_if ().
  unfold node_data at 2; Intros.
  forward.
  forward_call ().
  forward.
  forward_call ().
  forward.
  Exists; entailer!.
Qed.
  