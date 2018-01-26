Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
(*Require Import VST.progs.list_dt. Import LsegSpecial.*)
Require Import VST.floyd.library.
Require Import VST.progs.lock_coupling.
Require Import Sorting.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition tnode := Tstruct _node noattr.

Module ZOrder <: Orders.TotalLeBool.
  Definition t := Z.
  Definition leb x y := Z.leb x y.
  Theorem leb_total : forall x y, leb x y = true \/ leb y x = true.
  Proof. intros; destruct (Zle_bool_total x y); auto. Qed.
End ZOrder.

Module Import ZSort := Sort ZOrder.

Lemma StronglySorted_imp : forall (R R' : Z -> Z -> Prop) l (HR' : forall x y, R x y -> R' x y)
  (HR : StronglySorted R l), StronglySorted R' l.
Proof.
  intros; induction HR; constructor; auto.
  eapply Forall_impl, H; auto.
Qed.

Notation sorted := (StronglySorted Z.le).

Lemma sort_sorted : forall l, sorted (sort l).
Proof.
  intro; eapply StronglySorted_imp, StronglySorted_sort.
  - intros.
    rewrite <- Z.leb_le; auto.
  - intros ???; apply Zle_bool_trans.
Qed.

Inductive set_op := Add (e : Z) | Remove (e : Z).

Fixpoint apply_hist S h :=
  match h with
  | [] => S
  | Add e :: h' => if in_dec Z_eq_dec e S then apply_hist S h' else apply_hist (sort (e :: S)) h'
  | Remove e :: h' => apply_hist (remove Z_eq_dec e S) h'
  end.

Lemma apply_hist_app : forall h1 S h2, apply_hist S (h1 ++ h2) = apply_hist (apply_hist S h1) h2.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; auto.
  destruct (in_dec _ _ _); auto.
Qed.

(* up *)
Lemma In_remove : forall A (a : A) dec l, incl (remove dec a l) l.
Proof.
  induction l; simpl; auto.
  destruct (dec a a0).
  - apply incl_tl; auto.
  - apply incl_same_head; auto.
Qed.

Lemma remove_sorted : forall a l, sorted l -> sorted (remove Z_eq_dec a l).
Proof.
  induction l; auto; simpl; intro.
  inv H.
  destruct (Z.eq_dec a a0); auto.
  constructor; auto.
  rewrite Forall_forall in *; intros ? Hin.
  apply In_remove in Hin; auto.
Qed.

Lemma apply_hist_sorted : forall h S, sorted S -> sorted (apply_hist S h).
Proof.
  induction h; auto; simpl; intros.
  destruct a.
  - destruct (in_dec _ _ _); auto.
    apply IHh, sort_sorted.
  - apply IHh, remove_sorted; auto.
Qed.

Definition hist := hist_part set_op.

(*Definition q_lock_pred' (t : type) P p (vals : list (val * reptype t)) head (addc remc : val) lock gsh h :=
  !!(Zlength vals <= MAX /\ 0 <= head < MAX /\ consistent h [] vals) &&
  (data_at Tsh tqueue (rotate (complete MAX (map fst vals)) head MAX, (vint (Zlength vals),
                      (vint head, (vint ((head + Zlength vals) mod MAX), (addc, remc))))) p *
   cond_var Tsh addc * cond_var Tsh remc * malloc_token Tsh (sizeof tqueue_t) p *
   malloc_token Tsh (sizeof tcond) addc * malloc_token Tsh (sizeof tcond) remc *
   malloc_token Tsh (sizeof tlock) lock * ghost gsh (Tsh, h) p *
   fold_right sepcon emp (map (fun x => let '(p, v) := x in 
     !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals)).

Definition q_lock_pred A P p lock gsh := EX vals : list (val * reptype A), EX head : Z,
  EX addc : val, EX remc : val, EX h : hist _, q_lock_pred' A P p vals head addc remc lock gsh h.*)

Definition node_lock_inv e p := EX n : val, EX l : val,(*EX h : list set_op,*)
  field_at Tsh tnode [StructField _val] (vint e) p *
  field_at Tsh tnode [StructField _next] n p * field_at Tsh tnode [StructField _lock] l n *
  node_lock_inv.

Definition node_pred sh e p := EX l : val,
  !!((*sepalg.join gsh1 gsh2 Tsh /\*) repable_signed e /\ field_compatible tnode [] p) &&
  (field_at sh tnode [StructField _lock] l p *
   lock_inv sh l (node_lock_inv e p) (* * ghost gsh1 (lsh, h) p*)).

Definition new_node_spec :=
 DECLARE _new_node
  WITH e : Z
  PRE [ _e OF tint ]
   PROP (repable_signed e)
   LOCAL (temp _e (vint e))
   SEP ()
  POST [ tptr tnode ]
   EX p : val,
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (node_pred Tsh e p).

Definition del_node_spec :=
 DECLARE _new_node
  WITH e : Z, p : val
  PRE [ _n OF tptr tnode ]
   PROP ()
   LOCAL (temp _n p)
   SEP (node_pred Tsh e p)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP ().

Definition tnode_pair := Tstruct _node_pair noattr.

Definition list_inv sh H h := node_pred sh Int.min_signed H * ghost_hist h H.

Definition locate_spec :=
 DECLARE _locate
  WITH e : Z, sh : share, H : val, h : hist
  PRE [ _e OF tint ]
   PROP (repable_signed e)
   LOCAL (temp _e (vint e); gvar _head H)
   SEP (list_inv sh H h)
  POST [ tptr tnode_pair ]
   EX h' : hist, EX p : val, EX n1 : val, EX n2 : val, EX e1 : Z, EX e2 : Z, EX sh : share,
   PROP (incl h h'; e1 < e <= e2)
   LOCAL ()
   SEP (list_inv H h'; data_at Tsh tnode_pair (n1, n2) p; node_pred sh e1 n1;
        field_at Tsh tnode [StructField _val] (vint e1) n1; field_at Tsh tnode [StructField _next] n2 n1;
        node_pred sh e2 n2; node_lock_inv e2 n2).

Definition add_spec :=
 DECLARE _add
  WITH e : Z, H : val, h : hist
  PRE [ _e OF tint ]
   PROP (repable_signed e)
   LOCAL (temp _e (vint e); gvar _head H)
   SEP (list_inv H h)
  POST [ tint ]
   EX h' : hist, EX S : list Z, EX t' : nat,
   PROP (incl h h'; apply_hist [] h' = S)
   LOCAL (temp ret_temp (if in_dec Z_eq_dec e S then 0 else 1))
   SEP (list_inv H (h' ++ [(t', Add e)]).

Definition remove_spec :=
 DECLARE _remove
  WITH e : Z, H : val, h : hist
  PRE [ _e OF tint ]
   PROP (repable_signed e)
   LOCAL (temp _e (vint e); gvar _head H)
   SEP (list_inv H h)
  POST [ tint ]
   EX h' : hist, EX S : list Z, EX t' : nat,
   PROP (incl h h'; apply_hist [] h' = S)
   LOCAL (temp ret_temp (if in_dec Z_eq_dec e S then 1 else 0))
   SEP (list_inv H (h' ++ [(t', Remove e)]).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; surely_malloc_spec; new_node_spec; del_node_spec; locate_spec; add_spec; remove_spec; main_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function. 
  forward_call (* p = malloc(n); *)
     n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. inv H0.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma ctr_inv_precise : forall p,
  precise (cptr_lock_inv p).
Proof.
  intro; eapply derives_precise, data_at__precise with (sh := Ews)(t := tint); auto.
  intros ? (? & H); apply data_at_data_at_ in H; eauto.
Qed.
Hint Resolve ctr_inv_precise.

Lemma ctr_inv_positive : forall ctr,
  positive_mpred (cptr_lock_inv ctr).
Proof.
  intro; apply ex_positive; auto.
Qed.
Hint Resolve ctr_inv_positive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (lock, sh, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  unfold cptr_lock_inv at 2; simpl.
  Intro z.
  forward.
  forward.
  rewrite field_at_isptr; Intros.
  forward_call (lock, sh, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1); entailer!. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (lock, sh, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  unfold cptr_lock_inv at 2; simpl.
  Intro z.
  forward.
  rewrite data_at_isptr; Intros.
  forward_call (lock, sh, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { lock_props.
    unfold cptr_lock_inv; Exists z; entailer!. }
  forward.
  Exists z; entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (ctr, sh, lock).
  forward_call (lockt, sh, lock_inv sh lock (cptr_lock_inv ctr), thread_lock_inv sh ctr lock lockt).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { unfold thread_lock_inv; lock_props.
    rewrite selflock_eq at 2; cancel.
    eapply derives_trans; [apply lock_inv_later | cancel]. }
  forward.
Qed.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name ctr _ctr; name lockt _thread_lock; name lock _ctr_lock.
  start_function.
  forward.
  forward.
  forward.
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  rewrite field_at_isptr; Intros.
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { lock_props.
    unfold cptr_lock_inv; Exists 0; cancel. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 ctr lock lockt).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  apply extract_exists_pre; intros f_.
  forward_spawn (val * share * val * val)%type (f_, Vint (Int.repr 0), (ctr, sh1, lock, lockt),
    fun (x : (val * share * val * val)) (_ : val) => let '(ctr, sh, lock, lockt) := x in
         !!readable_share sh && emp * lock_inv sh lock (cptr_lock_inv ctr) *
         lock_inv sh lockt (thread_lock_inv sh ctr lock lockt)).
  { simpl spawn_pre; entailer!.
    Exists _args (fun x : val * share * val * val => let '(ctr, sh, lock, lockt) := x in
      [(_ctr, ctr); (_ctr_lock, lock); (_thread_lock, lockt)]); entailer.
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'. f_equal.
      unfold NDmk_funspec.
      apply mk_funspec_congr; auto.
      apply eq_JMeq.
      extensionality x x0.
      destruct x0 as (?, (((?, ?), ?), ?)); simpl.
      rewrite <- !sepcon_assoc; reflexivity.  }
    erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    entailer!. }
  forward_call (ctr, sh2, lock).
  forward_call (lockt, sh2, thread_lock_inv sh1 ctr lock lockt).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  forward_call (ctr, sh2, lock).
  Intro z.
  forward_call (lock, sh2, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  forward_call (lockt, Ews, sh1, |>lock_inv sh1 lock (cptr_lock_inv ctr), |>thread_lock_inv sh1 ctr lock lockt).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { unfold thread_lock_inv; lock_props.
    - apply later_positive; auto.
    - unfold rec_inv.
      rewrite selflock_eq at 1.
      rewrite later_sepcon; f_equal.
      apply lock_inv_later_eq.
    - rewrite selflock_eq at 2.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel.
      rewrite sepcon_comm, <- !sepcon_assoc, sepcon_comm.
      apply sepcon_derives; [apply lock_inv_later | cancel]. }
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
  { lock_props.
    erewrite sepcon_assoc, lock_inv_share_join; eauto; cancel. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
