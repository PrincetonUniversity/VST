(** * verif_hash.v: Correctness proof of hash.c *)

Require Import VST.floyd.new_tactics.
Require Import VST.floyd.library.
Require Import  hash.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import hashfun.

(*  IMPORTS FROM THE C STRING LIBRARY *)

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH str1 : val, s1 : string, str2 : val, s2 : string
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP ()
    LOCAL (temp 1 str1; temp 2 str2)
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring Tsh s1 str1; cstring Tsh s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH dest : val, n : Z, src : val, s : string
  PRE [ 1 OF tptr tschar, 2 OF tptr tschar ]
    PROP (Zlength s < n)
    LOCAL (temp 1 dest; temp 2 src)
    SEP (data_at_ Tsh (tarray tschar n) dest; cstring Tsh s src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn Tsh s n dest; cstring Tsh s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH s : string, str: val
  PRE [ 1 OF tptr tschar ]
    PROP ( )
    LOCAL (temp 1 str)
    SEP (cstring Tsh s str)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring Tsh s str).

(*  STRING FUNCTIONS:  COPY, HASH *)

Definition copy_string_spec : ident * funspec :=
 DECLARE _copy_string
 WITH s: val, sigma : string
 PRE [ _s OF tptr tschar ] 
    PROP ( ) LOCAL (temp _s s) SEP (cstring Tsh sigma s)
 POST [ tptr tschar ] 
    EX p: val, PROP ( ) LOCAL (temp ret_temp p) 
    SEP (cstring Tsh sigma s; cstring Tsh sigma p).

Definition hash_spec : ident * funspec :=
  DECLARE _hash
  WITH s: val, sh : share, contents : string
  PRE [ _s OF (tptr tschar) ]
          PROP  (readable_share sh)
          LOCAL (temp _s s)
          SEP   (cstring Tsh contents s)
  POST [ tuint ]
        PROP ()
	LOCAL(temp ret_temp  (Vint (Int.repr (hashfun contents))))
        SEP (cstring Tsh contents s).

(** ** DATA STRUCTURES FOR HASHTABLE *)

Definition tcell := Tstruct _cell noattr.
Definition thashtable := Tstruct _hashtable noattr.

Definition list_cell (key: string) (count: Z) (next: val) (p: val): mpred :=
 EX kp: val, cstring Tsh key kp * data_at Tsh tcell (kp,(Vint (Int.repr count), next)) p 
                     * malloc_token Tsh tcell p.

Definition list_cell_local_facts: 
  forall key count next p, list_cell key count next p |-- !! isptr p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_local_facts: saturate_local.

Definition list_cell_valid_pointer:
  forall key count next p, list_cell key count next p |-- valid_pointer p.
Proof. intros. unfold list_cell. Intros kp. entailer!. Qed.
Hint Resolve list_cell_valid_pointer: valid_pointer.

Lemma listcell_fold: forall key kp count p' p,
  cstring Tsh key kp * data_at Tsh tcell (kp, (Vint (Int.repr count), p')) p * malloc_token Tsh tcell p 
         |-- list_cell key count p' p.
Proof. intros. unfold list_cell. Exists kp. auto. Qed.

Fixpoint listrep (sigma: list (string * Z)) (x: val) : mpred :=
 match sigma with
 | (s,c)::hs => EX y: val, list_cell s c y x * listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Lemma listrep_local_prop: forall sigma p, listrep sigma p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> sigma=nil)).
Proof.
  intros. destruct sigma.
  * (* sigma = [] *)
    unfold listrep.
    entailer!.
    split; auto.
  * (* sigma = .. *)
    unfold listrep. destruct p0. Intros y.
    entailer!. split; intros. subst. inversion Pp.
    inversion H.
Qed.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof. intros. destruct sigma; unfold listrep.
  * (* sigma = [] *)
    entailer!.
  * (* sigma = .. *)
    destruct p0. Intros y.
    entailer!.
Qed.
Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_fold: forall key count p' p al, 
  list_cell key count p' p * listrep al p' |-- listrep ((key,count)::al) p.
Proof. intros. simpl. Exists p'. cancel. Qed.

Definition listboxrep al r :=
 EX p:val, data_at Tsh (tptr tcell) p r * listrep al p.

Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C :=
  f (fst xy) (snd xy).

Definition hashtable_rep (contents: hashtable_contents) (p: val) : mpred :=
  EX bl: list (list (string * Z) * val),
    !! (contents = map fst bl) &&
    malloc_token Tsh thashtable p * 
    field_at Tsh thashtable [StructField _buckets] (map snd bl) p 
    * iter_sepcon (uncurry listrep) bl.

(*Eval compute in (reptype (Tarray tint 10 noattr)).

Lemma unfold_reptype_Zlength : forall (cs : compspecs) (t0 : type) (n : Z) (a : attr)
  (al : reptype (Tarray t0 n a)),
  Zlength (unfold_reptype al) = n.
Proof. intros. simpl. auto.*)

Lemma hashtable_rep_local_facts: forall contents p,
 hashtable_rep contents p |-- !! (isptr p /\ Zlength contents = N).
Proof. intros. unfold hashtable_rep. Intros bl. entailer.
  destruct H2; simpl in *.
  unfold unfold_reptype in H. simpl in H.
  entailer!.
  rewrite Zlength_map in *. auto.
Qed.
Hint Resolve hashtable_rep_local_facts : saturate_local.

Lemma hashtable_rep_valid_pointer: forall contents p,
 hashtable_rep contents p |-- valid_pointer p.
Proof.
intros.
unfold hashtable_rep.
Intros bl.
subst.
auto with valid_pointer.
Qed.
Hint Resolve hashtable_rep_valid_pointer : valid_pointer.

(*  FUNCTION SPECIFICATIONS FOR HASHTABLE *)

Definition new_table_spec : ident * funspec :=
 DECLARE _new_table
 WITH u: unit
 PRE [ ] 
   PROP()
   LOCAL()
   SEP()
 POST [ tptr thashtable ] 
   EX p:val, PROP() 
      LOCAL(temp ret_temp p) 
      SEP(hashtable_rep empty_table p).

Definition new_cell_spec : ident * funspec :=
 DECLARE _new_cell
 WITH s: val, key: string, count: Z, next: val
 PRE [ _key OF tptr tschar, _count OF tint, _next OF tptr tcell ] 
   PROP()
   LOCAL(temp _key s; temp _count (Vint (Int.repr count)); temp _next next)
   SEP(cstring Tsh key s)
 POST [ tptr tcell ] 
   EX p:val, PROP() 
      LOCAL(temp ret_temp p) 
      SEP(list_cell key count next p; cstring Tsh key s).

Definition get_spec : ident * funspec :=
 DECLARE _get
 WITH p: val, contents: hashtable_contents, s: val, sigma : string
 PRE [ _table OF tptr (Tstruct _hashtable noattr), _s OF tptr tschar ] 
    PROP () 
    LOCAL (temp _table p; temp _s s)
    SEP (hashtable_rep contents p; cstring Tsh sigma s)
 POST [ tuint ]
      PROP ( ) LOCAL (temp ret_temp (Vint (Int.repr (hashtable_get sigma contents))))
      SEP (hashtable_rep contents p; cstring Tsh sigma s).

Definition incr_list_spec : ident * funspec :=
 DECLARE _incr_list
 WITH r0: val, al: list (string * Z), s: val, sigma : string
 PRE [ _r0 OF tptr (tptr tcell), _s OF tptr tschar ] 
    PROP (list_get sigma al < Int.max_unsigned) 
    LOCAL (temp _r0 r0; temp _s s)
    SEP (listboxrep al r0; cstring Tsh sigma s)
 POST [ tvoid ]
      PROP ( ) LOCAL ()
      SEP (listboxrep (list_incr sigma al) r0; cstring Tsh sigma s).

Definition incr_spec : ident * funspec :=
 DECLARE _incr
 WITH p: val, contents: hashtable_contents, s: val, sigma : string
 PRE [ _table OF tptr (Tstruct _hashtable noattr), _s OF tptr tschar ] 
    PROP (hashtable_get sigma contents < Int.max_unsigned) 
    LOCAL (temp _table p; temp _s s)
    SEP (hashtable_rep contents p; cstring Tsh sigma s)
 POST [ tvoid ]
      PROP ( ) LOCAL ()
      SEP (hashtable_rep (hashtable_incr sigma  contents) p; cstring Tsh sigma s).

(*  PUTTING ALL THE FUNSPECS TOGETHER *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   strcmp_spec; strcpy_spec; strlen_spec; hash_spec;
                   new_cell_spec; copy_string_spec; get_spec; incr_spec; 
                   incr_list_spec
 ]).

(* AUXILIARY LEMMAS ABOUT DATA-STRUCTURE PREDICATES *)

Lemma iter_sepcon_listrep_local_facts:
 forall bl, iter_sepcon (uncurry listrep) bl
                    |-- !! Forall is_pointer_or_null (map snd bl).
Proof.
(* Hint: use [induction] and [sep_apply].
  Also: when you have an mpred like  !! P * Q,
  where P is a proposition and Q is an mpred,
   [rewrite prop_sepcon]  will turn it into    !! P && (TT * Q)
  which is an easier kind of formula to handle.
 *)
  intros. induction bl.
  * (* bl = [] *)
    entailer!.
  * (* bl = .. *)
     simpl. unfold uncurry in *. sep_apply IHbl.
     entailer.
     (* rewrite <- (and_True (Forall is_pointer_or_null (snd a :: map snd bl))).
     rewrite <- sepcon_prop_prop.
     apply sepcon_derives.
     apply prop_derives. intros. apply Forall_cons; auto.
     entailer. *)
Qed.
Hint Resolve iter_sepcon_listrep_local_facts : saturate_local.

Lemma iter_sepcon_split3: 
  forall {A}{d: Inhabitant A} (i: Z) (al: list A) (f: A -> mpred),
   0 <= i < Zlength al   ->
  iter_sepcon f al =
  iter_sepcon f (sublist 0 i al) * f (Znth i al) * iter_sepcon f (sublist (i+1) (Zlength al) al).
Proof.
intros.
rewrite <- (sublist_same 0 (Zlength al) al) at 1 by auto.
(* Hint: [rewrite (sublist_split LO MID HI) by omega], where you choose values for LO MID HI. 
  Also useful:  [rewrite sublist_len_1]    and    [iter_sepcon_app].
*)
rewrite (sublist_split 0 i (Zlength al)) by omega.
rewrite (sublist_split i (i+1) (Zlength al)) by omega.
rewrite sublist_len_1 by omega.
do 2 rewrite iter_sepcon_app. simpl. rewrite sepcon_emp.
rewrite sepcon_assoc. auto.
Qed.

Lemma thashtable_local_facts: forall sh contents p,
  data_at sh thashtable contents p |-- !! (isptr p /\ Zlength contents = N).
Proof.
  intros. entailer!. destruct H0. unfold unfold_reptype in H0. simpl in H0.
  rep_omega.
Qed.
Hint Resolve thashtable_local_facts : saturate_local.

(* BEGINNING OF THE PROOFS OF THE FUNCTION BODIES. *)

(* This lemma demonstrates how to handle "strings", that is,
   null-terminated arrays of characters. *)
Lemma demonstrate_cstring1: 
 forall i contents,
   ~ In Byte.zero contents ->
   Znth i (contents ++ [Byte.zero]) <> Byte.zero  ->
   0 <= i <= Zlength contents ->
   0 <= i + 1 < Zlength (contents ++ [Byte.zero]).
Proof.
intros.
(* When processing a C null-terminated string, you will want to
   maintain the three kinds of assumptions above the line.
   A string is an array of characters with three parts:
   (1) The "contents" of the string, none of which is the '\0' character;
   (2) The null termination character, equal to Byte.zero;
   (3) the remaining garbage in the array, after the null.
  The first assumption above the line says that none of the
  contents is the null character. 
  Now suppose we are in a loop where variable [_i] (with value [i])
  is traversing the array.  We expect that loop to go up to but 
  no farther than the null character, that is, one past the contents.
  Therefore [0 <= i <= Zlength contents].
  Furthermore, suppose we have determined (by an if-test) that
  s[i] is not zero, then we have the hypothesis H0 above.

  The [cstring Tsh] tactic processes all three of them to conclude
  that [i < Zlength contents]. *)
assert (H7: i < Zlength contents) by cstring.

(* But actually, [cstring Tsh] tactic will prove any rep_omega consequence
   of that fact.  For example: *)
clear H7.
autorewrite with sublist.
cstring.
Fail idtac.  (* demonstrates that there are "No more subgoals." *)
Abort. (* Throw this away.  Don't apply this lemma in the
    body_hash proof, instead, use [autorewrite with sublist] and
    [cstring Tsh] directly, where appropriate. *)

Lemma demonstrate_cstring2: 
 forall i contents,
   ~ In Byte.zero contents ->
   Znth i (contents ++ [Byte.zero]) = Byte.zero  ->
   0 <= i <= Zlength contents ->
   i = Zlength contents.
Proof.
intros.
(* Here is another demonstration.  When you loop on the
   string contents reaches the end, so that s[i] is the zero byte,
   you'll have the an assumption like [H0] above the line.
   The [cstring Tsh] tactic handles this case too, to prove 
   [i = Zlength contents].   *)
cstring.
Fail idtac. (* No more subgoals. *)
Abort.  (* Use the method, not the lemma. *)


Lemma body_hash: semax_body Vprog Gprog f_hash hash_spec.
Proof.
start_function.
unfold cstring ,hashfun in *.
(* Before doing this proof, study some of the proofs in VST/progs/verif_strlib.v.
  In the PROP part of your loop invariant, you'll want to maintain [0 <= i <= Zlength contents].

  In the LOCAL part of your loop invariant, try to use something like
   [temp _c (Vbyte (Znth i (contents ++ [Byte.zero]))]
  instead of 
   [temp _c (Znth 0 (map Vbyte (...)))]
  The reason is that (temp _c (Vint x)) or (temp _c (Vbyte y)) is much easier
  for Floyd to handle than (temp _c X) where X is a general formula of type [val].
 
  Late in the proof of the loop body, the lemma [hashfun_snoc] will be useful. *)
forward.
forward.
forward. entailer!.
forward_while
 (EX i: Z,
   PROP  (0 <= i <= Zlength contents)
   LOCAL (temp _c (Vbyte (Znth i (contents ++ [Byte.zero])));
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr (hashfun (sublist 0 i contents))));
          temp _s s)
   SEP   (data_at Tsh (tarray tschar (Zlength contents + 1)) (map Vbyte (contents ++ [Byte.zero])) s)).
* (* current state *)
EExists. entailer!. rep_omega.
* (* type check *)
entailer!.
* (* loop *)
forward.
forward.
assert (Hi : 0 <= i < Zlength contents) by cstring.
forward.
EExists.
entailer!.
split. rep_omega.
unfold hashfun. rewrite hashfun_snoc by omega.
rewrite app_Znth1 by omega. auto.
* (* after loop *)
forward.
assert (Hi: i = Zlength contents) by cstring.
subst i.
autorewrite with sublist. unfold hashfun.
entailer.
Qed.

Lemma body_new_table_helper: 
 (* This lemma is useful as the very last thing to do in body_new_table *)
 forall p, 
  data_at Tsh thashtable (list_repeat (Z.to_nat N) nullval) p
  |-- field_at Tsh thashtable [StructField _buckets]
       (list_repeat (Z.to_nat N) nullval) p *
         iter_sepcon (uncurry listrep) (list_repeat (Z.to_nat N) ([], nullval)).
Proof.
intros.
unfold_data_at 1%nat.
cancel.
unfold listrep, uncurry.
rewrite N_eq. simpl.
repeat rewrite sepcon_andp_prop', emp_sepcon.
entailer.
Qed.

Lemma Znth_eq_list_eq : forall {A} {d : Inhabitant A} (al bl : list A),
  Zlength al = Zlength bl ->
  (forall i, 0 <= i < Zlength al -> Znth i al = Znth i bl) ->
  al = bl.
Proof.
  intros A d al. induction al; intros.
  * (* al = [] *)
    rewrite Zlength_nil in H.
    symmetry. apply Zlength_nil_inv. auto.
  * (* al = .. *)
    destruct bl as [ | b bl].
    autorewrite with sublist in H. rep_omega.
    f_equal.
    (* a = b *)
    apply (H0 0). autorewrite with sublist. rep_omega.
    (* al = bl *)
    apply IHal. autorewrite with sublist in H. rep_omega.
    intros. specialize (H0 (i+1)).
    do 2 rewrite Znth_pos_cons in H0 by omega.
    autorewrite with sublist in H0.
    apply H0. rep_omega.
Qed.

Hint Resolve compute_in_members_e.

Lemma body_new_table: semax_body Vprog Gprog f_new_table new_table_spec.
Proof.
(* The loop invariant in this function describes a partially initialized array.
   The best way to do that is with something like,
  [data_at Tsh thashtable 
      (list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat (N-i)) Vundef) p].
  Then at some point you'll have to prove something about,
  [data_at Tsh thashtable
      (list_repeat (Z.to_nat (i + 1)) nullval ++ list_repeat (Z.to_nat (N - (i + 1))) Vundef) p]
  In particular, you'll have to split up [list_repeat (Z.to_nat (i + 1)) nullval]
   into [list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat 1) nullval].
  The best way to do that is [rewrite <- list_repeat_app'.]
*)
start_function.
forward_call thashtable.
(* verify precondition of calling malloc *)
unfold sizeof. simpl. repeat split; rep_omega.
Intros vret.
forward_if
  (PROP ( )
   LOCAL (temp _p vret)
   SEP (malloc_token Tsh thashtable vret * data_at_ Tsh thashtable vret)).
destruct (Memory.EqDec_val vret nullval); entailer.
forward_call tt.
entailer.
forward.
entailer.
destruct (Memory.EqDec_val vret nullval); entailer.
(* after if *)
forward_for_simple_bound N (EX i:Z, EX contents : list val,
    PROP (forall j, 0 <= j < i -> Znth j contents = nullval)
    LOCAL (temp _p vret)
    SEP (malloc_token Tsh thashtable vret * data_at Tsh thashtable contents vret))%assert.
EExists.
entailer!.
intros. omega.
sep_apply data_at__data_at. apply derives_refl.

assert_PROP ( field_compatible thashtable (DOT _buckets SUB i) vret). {
  entailer!. rewrite <- app_nil_r with (l := [ArraySubsc i; StructField _buckets]).
  apply field_compatible_app_inv'; auto.
  repeat split; simpl; auto; rep_omega.
}
assert_PROP (Zlength contents = N) by entailer.
Intros.
forward.
EExists.
entailer!.
intros.
{ destruct (dec_eq i j).
  * (* i = j *) 
    subst. apply upd_Znth_same. rep_omega.
  * (* i <> j *)
    rewrite upd_Znth_diff; auto. apply H2. all: rep_omega.
}
(* after loop *)
Intro x. rename x into contents.
forward.
EExists. entailer!.
assert (contents = (list_repeat (Z.to_nat N) nullval)). {
  apply Znth_eq_list_eq.
  autorewrite with sublist. auto.
  intros. autorewrite with sublist. apply H. all: rep_omega.
}
subst contents.
sep_apply body_new_table_helper.
unfold hashtable_rep.
EExists.
ecancel.
entailer!.
(* can't figure why entailer! works *)
Qed.

(* The [get] function traverses a linked list.  We will reason about linked-list traversal
   in separation logic using "Magic Wand as Frame" http://www.cs.princeton.edu/~appel/papers/wand-frame.pdf
   When the loop is partway down the linked list, we can view the original list
   up to the current position as a "linked-list data structure with a hole";
   and the current position points to a linked-list data structure that fills the hole.
   The "data-structure-with-a-hole" we reason about with separating implication,
    called "magic wand":   (hole -* data-structure)
    which says, if you can conjoin this data-structure-with-a-hole 
    with something-to-fill-the-hole, then you get the original data structure:
     hole * (hole -* data-structure) |--   data-structure.
    The lemma [listrep_traverse] is useful in moving one linked-list cell
    out of the hole and into the data-structure-with-a-(smaller)-hole.
*)

Lemma listrep_traverse:  (* useful in body_get lemma*)
  forall key count p' p, 
  list_cell key count p' p |-- 
  ALL al:list (string * Z), listrep al p' -* (EX y : val, list_cell key count y p * listrep al y).
Proof.
intros.
apply allp_right; intro al.
rewrite <- wand_sepcon_adjoint.
Exists p'. auto.
Qed.

Definition sublistrep al ap bp : mpred :=
  ALL bl : list (string * Z), listrep bl bp -* listrep (al ++ bl) ap.

Lemma sublistrep_nil: forall ap,
  emp |-- sublistrep [] ap ap.
Proof.
  intros. unfold sublistrep. simpl.
  apply allp_right. intros al. apply wand_refl_cancel_right.
Qed.

Lemma sublistrep_one: forall key count ap bp,
  list_cell key count bp ap |-- sublistrep [(key, count)] ap bp.
Proof.
  intros. apply listrep_traverse.
Qed.

Lemma list_get_unfold: forall s al bl,
  ~ In s (map fst al) ->
  list_get s (al ++ bl) = list_get s bl.
Proof.
  intros. induction al; auto.
  assert (s <> fst a). {
    intro.
    destruct H. constructor. auto.
  }
  assert (~ In s (map fst al)). {
    intro.
    destruct H. constructor 2. auto.
  }
  destruct a.
  simpl.
  destruct (EqDec_string s s0); try contradiction; auto.
Qed.

Lemma list_get_unfold': forall s c al bl,
  ~ In s (map fst al) ->
  list_get s (al ++ (s, c) :: bl) = c.
Proof.
  intros.
  rewrite list_get_unfold; auto.
  simpl. destruct (EqDec_string s s); try contradiction; auto.
Qed.

Lemma sublistrep_unfold: forall al ap bp bl,
  sublistrep al ap bp |-- listrep bl bp -* listrep (al ++ bl) ap.
Proof.
  intros. unfold sublistrep.
  apply allp_instantiate with (x := bl).
Qed.

Lemma sublistrep_app: forall al bl ap bp cp,
  sublistrep al ap bp * sublistrep bl bp cp |-- sublistrep (al ++ bl) ap cp.
Proof.
  intros. unfold sublistrep at 3.
  apply allp_right. intros cl.
  sep_eapply sublistrep_unfold.
  sep_eapply sublistrep_unfold.
  rewrite <- app_assoc.
  apply wand_frame_ver.
  (* easier, but maybe confusing *)
Qed.

Lemma listrep_nil:
  listrep [] nullval = emp.
Proof.
  simpl; apply pred_ext; entailer.
Qed.

Lemma sublistrep_nullval_listrep: forall al ap,
  sublistrep al ap nullval = listrep al ap.
Proof.
  intros.
  apply pred_ext; unfold sublistrep.
  * (* LHS |-- RHS *)
    (* sep_apply (allp_instantiate (B := list (string * Z))). *)
    (* why not work ? *)
    eapply derives_trans.
    eapply (allp_instantiate _ []).
    rewrite listrep_nil.
    rewrite app_nil_r.
    rewrite emp_wand. auto.
  * (* RHS |-- LHS *)
    apply allp_right. intros bl.
    apply wand_sepcon_adjoint. entailer.
    assert (bl = []) by (apply H0; auto).
    subst bl. rewrite listrep_nil.
    rewrite app_nil_r.
    rewrite sepcon_emp. auto.
Qed.

Lemma listrep_app: forall al bl ap bp,
  sublistrep al ap bp * listrep bl bp |-- listrep (al ++ bl) ap.
Proof.
  intros. do 2 rewrite <- sublistrep_nullval_listrep. apply sublistrep_app.
Qed.

Lemma body_get: semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
rename p into table.
forward_call (s, Tsh, sigma).
forward.
pose proof (hashfun_inrange sigma).
rewrite modu_repr by rep_omega.
set (b := (hashfun sigma) mod 109).
assert (0 <= b < 109). {
  subst b. apply Z.mod_pos_bound. omega.
}
assert_PROP (Zlength contents = 109). {
  entailer!.
}
unfold hashtable_rep.
Intros bl.
assert_PROP (Zlength bl = 109). {
  entailer!. rewrite Zlength_map in *. auto.
}
forward. entailer!. apply Forall_Znth; auto. autorewrite with sublist. omega.
set (entry_list :=  fst (Znth b bl)).
forward_while (EX p : val, EX cl : list (string * Z), EX dl : list (string * Z),
      PROP ( ~ In sigma (map fst cl); cl ++ dl = entry_list)
      LOCAL (temp _p p; temp _s s)
      SEP (cstring Tsh sigma s; malloc_token Tsh thashtable table;
          field_at Tsh thashtable [StructField _buckets] (map snd bl) table;
          iter_sepcon (uncurry listrep) (sublist 0 b bl) *
          iter_sepcon (uncurry listrep) (sublist (b+1) (Zlength bl) bl) *
          sublistrep cl (snd (Znth b bl)) p *
          listrep dl p))%assert.
rewrite iter_sepcon_split3 with (i := b) by omega.
simpl (uncurry listrep (Znth b bl)).
do 3 EExists.
entailer!.
2 : {
  unfold uncurry. rewrite Znth_map by omega. ecancel.
  instantiate (1 := nil).
  unfold sublistrep. apply allp_right. intros bl0.
  simpl. apply wand_refl_cancel_right.
}
auto.
entailer.
destruct dl as [ | [dsigma dc] dl].
{
  assert_PROP (p = nullval) by entailer.
  subst p. inversion HRE.
}
simpl.
unfold list_cell. Intros p' ds.
forward.
forward_call (ds, dsigma, s, sigma).
Intros intcmp.
forward_if (
   PROP ( dsigma <> sigma )
   LOCAL (temp _t'2 (Vint intcmp); temp _t'4 ds; temp _p p; temp _s s)
   SEP (cstring Tsh sigma s; malloc_token Tsh thashtable table;
   field_at Tsh thashtable [StructField _buckets] (map snd bl) table; iter_sepcon (uncurry listrep) (sublist 0 b bl);
   iter_sepcon (uncurry listrep) (sublist (b + 1) (Zlength bl) bl); sublistrep cl (snd (Znth b bl)) p;
   cstring Tsh dsigma ds; data_at Tsh tcell (ds, (Vint (Int.repr dc), p')) p; malloc_token Tsh tcell p; listrep dl p')).
(* if ds = sigma *)
forward.
forward.
unfold hashtable_rep.
EExists.
entailer!.
do 2 f_equal. rewrite hashtable_get_unfold.
rewrite H3. replace (hashfun sigma mod 109) with b; auto. rewrite Znth_map by omega.
rewrite <- H5. simpl in H6. subst dsigma. rewrite list_get_unfold'; auto.
rewrite (iter_sepcon_split3 b bl) by omega.
sep_apply (listcell_fold). unfold uncurry. rewrite <- H5.
sep_apply (sublistrep_one). cancel.
do 2 sep_apply listrep_app. apply derives_refl'. reflexivity.
(* if ds <> sigma *)
forward.
entailer!. destruct (Int.eq_dec intcmp Int.zero); contradiction.
(* after if *)
forward.
(* end of loop *)
EExists. simpl (fst _); simpl (snd _).
sep_apply listcell_fold.
sep_apply sublistrep_one.
sep_apply (fun al bl ap => sublistrep_app al bl ap p).
entailer!.
2: ecancel.
split.
rewrite map_app. rewrite in_app_iff. simpl. intros [? | [? | ?] ]; contradiction.
rewrite <- app_assoc. simpl. apply H5.
(* after loop *)
forward.
replace dl with (@nil (string * Z))  in * by (symmetry; apply H11; auto).
entailer!.
do 2 f_equal. rewrite hashtable_get_unfold. rewrite H3. replace (hashfun sigma mod 109) with b by auto.
rewrite Znth_map by omega. rewrite <- H5.
rewrite list_get_unfold; auto.
unfold hashtable_rep.
EExists. entailer!.
rewrite (iter_sepcon_split3 b bl) by omega.
cancel.
unfold uncurry. rewrite listrep_nil, sepcon_emp, sublistrep_nullval_listrep.
rewrite app_nil_r in H5. subst. auto.
Qed.

Lemma listboxrep_traverse:
  forall p kp key count r, 
          field_compatible tcell [] p ->
            cstring Tsh key kp * 
            field_at Tsh tcell [StructField _key] kp p *
            field_at Tsh tcell [StructField _count] (Vint (Int.repr count)) p *
            malloc_token Tsh tcell p *
            data_at Tsh (tptr tcell) p r |-- 
            ALL dl: list (string * Z), 
              listboxrep dl (field_address tcell [StructField _next] p)
                -* listboxrep ((key, count) :: dl) r.
Proof.
  intros.
  apply allp_right; intro dl.
  apply -> wand_sepcon_adjoint.
   (* Sometime during the proof below, you will have
       data_at Tsh tcell ... p
     that you want to expand into 
       field_at Tsh tcell [StructField _key] ... p * field_at Tsh tcell [StructField _count] ... p 
       * field_at Tsh tcell [StructField _next] ... p.
     You can do this with   [unfold_data_at x%nat] where x is the number
     indicating _which_ of the data_at or field_at conjucts you want to expand.
*)
  unfold listboxrep. Intros p'. EExists. simpl. EExists. ecancel.
  unfold list_cell. EExists. ecancel. unfold_data_at 2%nat. ecancel.
Qed.

Lemma list_incr_unfold: forall s al bl,
  ~ In s (map fst al) ->
  list_incr s (al ++ bl) = al ++ list_incr s bl.
Proof.
  intros. induction al; auto.
  assert (s <> fst a). {
    intro.
    destruct H. constructor. auto.
  }
  assert (~ In s (map fst al)). {
    intro.
    destruct H. constructor 2. auto.
  }
  destruct a.
  simpl.
  destruct (EqDec_string s s0); try contradiction.
  rewrite IHal; auto.
Qed.

Lemma list_incr_unfold': forall s c al bl,
  ~ In s (map fst al) ->
  list_incr s (al ++ (s, c) :: bl) = al ++ (s, c+1) :: bl.
Proof.
  intros.
  rewrite list_incr_unfold; auto.
  simpl. destruct (EqDec_string s s); try contradiction; auto.
Qed.

Definition sublistrep_p al ap bpp : mpred :=
  ALL bp:val, data_at Tsh (tptr tcell) bp bpp -* sublistrep al ap bp.

Lemma sepcon_prop_TT: forall P,
  !! P = !! P * TT.
Proof.
  intros. apply pred_ext.
  * (* LHS |-- RHS *)
    rewrite <- sepcon_emp at 1. entailer!.
  * (* RHS |-- LHS *)
    unfold TT. rewrite sepcon_prop_prop. entailer.
Qed.

Lemma body_incr_list: semax_body Vprog Gprog f_incr_list incr_list_spec.
Proof.
(* This proof uses "magic wand as frame" to traverse _and update_ 
   a (linked list) data structure.   This pattern is a bit more complex than
   the wand-as-frame pattern used in body_get, which did not update
   the data structure.   You will still use "data-structure-with-a-hole"
   and "what-is-in-the-hole"; but now the "data-structure-with-a-hole"
   must be able to accept the _future_ hole-filler, not the one that is
   in the hole right now.

  The key lemmas to use are, [wand_refl_cancel_right], [wand_frame_elim'],
   and [wand_frame_ver].   When using [wand_frame_ver], you will find
   [listboxrep_traverse] to be useful.
*)
start_function.
forward.
unfold listboxrep.
Intros p0.
(* before loop *)
forward_loop (EX r:val, EX p:val, EX bl:list (string * Z), EX cl:list (string * Z),
    PROP  (~ In sigma (map fst bl) /\ al = bl ++ cl)
    LOCAL (temp _r r; temp _s s)
    SEP   (cstring Tsh sigma s; data_at Tsh (tptr tcell) p r; listrep cl p;
            (if (Val.eq r r0) then !! (p = p0) && !! (bl = []) && emp
                else data_at Tsh (tptr tcell) p0 r0 * sublistrep_p bl p0 r)))%assert.
{
  do 4 EExists. instantiate (2 := []).
  entailer!. destruct (Val.eq r0 r0); try contradiction. entailer.
}
Intros r p bl cl.
forward.
forward_if.
  forward_call (s, sigma, 1, nullval). Intros pnew.
  forward.
  forward.
  unfold listboxrep, sublistrep_p.
  rewrite list_incr_unfold; auto.
  assert (cl = []) by (apply H5; auto); subst.
  destruct (Val.eq r r0); subst; cancel.
  (* r = r0 *)
  Exists pnew. cancel.
  assert_PROP (bl = []) by entailer. subst.
  simpl. EExists. entailer.
  (* r <> r0 *)
  EExists. ecancel.
  sep_eapply (allp_instantiate' (B := val)).
  sep_apply wand_frame_elim''.
  sep_apply sublistrep_one.
  sep_apply listrep_app.
  sep_apply listrep_app.
  apply derives_refl'. f_equal.
(* else (if (!p)) *)
destruct cl as [ | [csigma cc] cl].
  (* if cl = [] *)
  assert_PROP (p = nullval) by entailer. contradiction.
simpl. unfold list_cell. Intros p' cs.
forward.
forward_call (cs, csigma, s, sigma).
Intros rcmp.
forward_if.
(* if (cmp = 0) *)
forward.
forward.
forward.
unfold listboxrep, sublistrep_p.
rewrite list_incr_unfold; auto.
EExists. ecancel.
eapply derives_trans. 2: apply cancel_left; apply listrep_app with (bp := p).
simpl in H3. simpl; destruct (EqDec_string sigma csigma); [ | symmetry in H3; contradiction]; simpl.
sep_apply listcell_fold. EExists. ecancel.
destruct (Val.eq r r0); subst.
(* r = r0 *)
Intros. subst p bl. instantiate (1 := p0). ecancel. apply sublistrep_nil.
(* r <> r0 *)
sep_eapply (allp_instantiate' (B := val)).
sep_apply wand_frame_elim''.
cancel.
(* else (if (cmp = 0)) *)
forward.
(* end of loop *)
simpl offset_val.
assert_PROP (offset_val 8 p = field_address tcell [StructField _next] p).
assert_PROP (field_compatible tcell [StructField _next] p). {
  unfold_data_at 2%nat. entailer!.
}
rewrite field_compatible_field_address; auto.
simpl offset_val. entailer!.
do 2 EExists.
Exists (bl ++ [(csigma, cc)]) cl.
entailer!.
{
  split.
  rewrite map_app. rewrite in_app_iff. simpl.
  destruct (Int.eq_dec rcmp Int.zero); try contradiction.
  tauto.
  rewrite <- app_assoc. reflexivity.
}

assert_PROP (field_address tcell [StructField _next] p <> r0).
unfold_data_at 2%nat. rewrite field_at_data_at with (gfs := [StructField _next]).
destruct (Val.eq r r0); entailer!.

rewrite H5.
destruct (Val.eq (field_address tcell [StructField _next] p) r0); try contradiction.

assert (forall p s c next,
  field_at Tsh tcell [StructField _key] s p *
  field_at Tsh tcell [StructField _count] c p *
  field_at Tsh tcell [StructField _next] next p
  |-- data_at Tsh tcell (s, (c, next)) p).
{
  intros. unfold_data_at 1%nat. cancel.
}

destruct (Val.eq r r0).

Intros.
subst bl p r. unfold_data_at 2%nat. ecancel.
simpl sublistrep_p.
unfold sublistrep_p.
apply allp_right. intros p0'. apply -> wand_sepcon_adjoint.
sep_apply H13.
sep_apply listcell_fold.
apply sublistrep_one.

unfold_data_at 2%nat. ecancel.
unfold sublistrep_p.
apply allp_right. clear dependent p'. intros p'. apply -> wand_sepcon_adjoint.
sep_apply H13.
sep_apply listcell_fold.
sep_eapply (allp_instantiate' (B := val)).
sep_apply wand_frame_elim''.
sep_apply sublistrep_one.
sep_apply (sublistrep_app bl).
apply derives_refl.
Qed.


Lemma field_at_data_at':
      forall {cs: compspecs} (sh : Share.t) (t : type) (gfs : list gfield)
         (v : reptype (nested_field_type t gfs)) 
         (p : val),
       field_at sh t gfs v p =
       !! field_compatible t gfs p  && data_at sh (nested_field_type t gfs) v (field_address t gfs p).
Proof.
intros.
apply pred_ext.
entailer!. rewrite field_at_data_at; auto.
entailer!. rewrite field_at_data_at; auto.
Qed.

Ltac wand_slice_array_spec t :=
  let spec :=
   constr:(forall lo hi n sh (al' : list (reptype t)) p,
           0 <= lo <= hi ->
           hi <= n ->
           Zlength al' = n ->
           data_at sh (tarray t n) al' p =
           data_at sh (tarray t (hi - lo)) (sublist lo hi al') (field_address0 (tarray t n) [ArraySubsc lo] p) *
           (!! field_compatible (tarray t n) [] p &&
            (ALL cl : list (reptype t) ,
             data_at sh (tarray t (hi - lo)) cl (field_address0 (tarray t n) [ArraySubsc lo] p) -*
             data_at sh (tarray t n) (sublist 0 lo al' ++ cl ++ sublist hi n al') p)))
  in
  exact
  spec.


Lemma wand_slice_array_tptr_tcell: ltac:(wand_slice_array_spec (tptr tcell)).
Proof. Admitted.

(* Examine this carefully: *)
Check wand_slice_array_tptr_tcell.
(* It is a specialization of the [wand_slice_array] lemma that is easier to use,
   because it does not use John Major equality (JMeq) *)

Lemma upd_Znth_split3: forall {A} {d: Inhabitant A} (i: Z) (al: list A) (a: A),
  0 <= i < Zlength al ->
  upd_Znth i al a = sublist 0 i al ++ [a] ++ sublist (i+1) (Zlength al) al.
Proof.
  intros.
  apply Znth_eq_list_eq.
  1: list_solve.
  intros.
  rewrite upd_Znth_Zlength in H0 by auto.
  pose proof (Z.compare_spec i i0).
  destruct (i ?= i0) eqn:?; inversion H1.
  * (* i = i0 *)
    subst i0.
    rewrite upd_Znth_same by auto.
    rewrite app_Znth2 by list_solve.
    rewrite Zlength_sublist by omega.
    replace (i-(i-0)) with 0 by omega.
    simpl app.
    rewrite Znth_0_cons; auto.
  * (* i < i0 *)
    rewrite upd_Znth_diff by omega.
    rewrite app_Znth2 by list_solve.
    rewrite app_Znth2 by list_solve.
    rewrite Zlength_sublist by omega.
    rewrite Znth_sublist by list_solve.
    replace (Zlength [a]) with 1 by auto.
    f_equal. omega.
  * (* i > i0 *)
    rewrite upd_Znth_diff by omega.
    rewrite app_Znth1 by list_solve.
    rewrite Znth_sublist by list_solve.
    f_equal. omega.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
start_function.
rename p into table.
rename H into Hmax.
assert_PROP (isptr table) as Htable by entailer!.

(* The next two lines would not be part of an ordinary Verifiable C proof, 
   they are here only to guide you through the bigger proof. *)
match goal with |- semax _ _ (Ssequence (Ssequence ?c1 (Ssequence ?c2 ?c3)) ?c4) _ => apply (semax_unfold_seq (Ssequence (Ssequence c1 c2) (Ssequence c3 c4))); [ reflexivity | ] end.

pose (j := EX cts:list (list (string * Z) * val),
  (PROP (contents = map fst cts; 0 <= hashfun sigma mod N < N; Zlength cts = N)
  LOCAL (temp _b (Vint (Int.repr (hashfun sigma mod N)));
         temp _h (Vint (Int.repr (hashfun sigma)));
         temp _table table; temp _s s)
  SEP (cstring Tsh sigma s; malloc_token Tsh thashtable table;
       data_at Tsh (tarray (tptr tcell) N) (map snd cts) (field_address thashtable [StructField _buckets] table);
       iter_sepcon (uncurry listrep) cts))%assert).
apply semax_seq' with j; subst j; abbreviate_semax.
{
  forward_call (s, Tsh, sigma).
  forward.
  assert_PROP (Zlength contents = N) by entailer.
  unfold hashtable_rep. Intros bl. EExists.
  entailer!. split.
  apply Z.mod_pos_bound. rep_omega.
  split.
  autorewrite with sublist in *. auto.
  f_equal. symmetry. apply modu_repr. apply hashfun_inrange. rep_omega.
  ecancel.
}

Intros cts.
subst contents.
unfold hashtable_get in Hmax.
rewrite Zlength_map, H1 in Hmax.
set (h := hashfun sigma mod N) in *.
erewrite (wand_slice_array_tptr_tcell h (h+1) N)
  by first [apply JMeq_refl | rep_omega | list_solve ].

 (* For the remainder of the proof, here are some useful lemmas:
    [sublist_len_1] [sublist_same] [sublist_map]
    [data_at_singleton_array_eq]
    [iter_sepcon_split3]  [iter_sepcon_app] [sublist_split]
    [field_at_data_at]
    [wand_slice_array_tptr_tcell]
*)

assert_PROP (
   field_address0 (tarray (tptr tcell) N) [ArraySubsc h] (field_address thashtable [StructField _buckets] table)
      = field_address thashtable [ArraySubsc h; StructField _buckets] table). {
  assert_PROP (is_pointer_or_null
      (field_address0 (tarray (tptr tcell) N) [ArraySubsc h] (field_address thashtable [StructField _buckets] table))) by entailer.
  rewrite field_address0_clarify; auto.
  assert_PROP (is_pointer_or_null (field_address thashtable [StructField _buckets] table)) by entailer.
  rewrite field_address_clarify; auto.
  assert_PROP (is_pointer_or_null (field_address thashtable [ArraySubsc h; StructField _buckets] table)). {
    entailer!.
    replace ([ArraySubsc h; StructField _buckets]) with ([ArraySubsc h; StructField _buckets] ++ []) by auto.
    eapply field_compatible_app_inv'; auto.
    simpl. split; auto; split; auto.
  }
  rewrite field_address_clarify; auto.
  entailer.
}



forward_call ((field_address thashtable (DOT _buckets SUB h) table),
      fst (Znth h cts), s, sigma).
3: rewrite Znth_map in Hmax by rep_omega; auto.
rewrite H.
assert_PROP (is_pointer_or_null (field_address thashtable [ArraySubsc h; StructField _buckets] table)). {
  entailer!.
}
rewrite field_address_clarify with (path := [ArraySubsc h; StructField _buckets]) by auto.
entailer.

unfold listboxrep.
EExists.
replace (h + 1 - h) with 1 by omega.
rewrite sublist_one with (lo := h) by (autorewrite with sublist; rep_omega).

rewrite H at 1.
sep_apply data_at_singleton_array_eq.
cancel.
rewrite iter_sepcon_split3 with (i := h) by omega.
unfold uncurry at 2.
rewrite Znth_map by omega.
fold fold_right_sepcon.
cancel.
forward.
cancel.
unfold hashtable_rep.
unfold listboxrep. Intros ap.
erewrite <- data_at_singleton_array_eq by auto.
sep_eapply (allp_instantiate' (B := list val)).
rewrite H.
sep_apply wand_frame_elim''.
set (al := list_incr sigma (fst (Znth h cts))).
Exists (upd_Znth h cts (al, ap)).
entailer!.

2 : {
  rewrite iter_sepcon_split3 with (i := h) (al0 := (upd_Znth h cts (al, ap))) by list_solve.
  rewrite <- upd_Znth_map.
  simpl snd.
  replace N with (Zlength (map snd cts)) at 2 by list_solve.
  rewrite <- upd_Znth_split3 by list_solve.
  unfold uncurry at 4.
  rewrite upd_Znth_same by omega. simpl fst. simpl snd.
  ecancel.
  rewrite upd_Znth_Zlength by omega.
  rewrite sublist_upd_Znth_l by omega.
  rewrite sublist_upd_Znth_r by omega.
  cancel.
}
unfold hashtable_incr.
rewrite Zlength_map.
rewrite H1.
fold h.
rewrite <- upd_Znth_map.
f_equal.
rewrite Znth_map by rep_omega.
auto.
Qed.
