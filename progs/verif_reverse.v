(** Heavily annotated for a tutorial introduction.
 ** See the Makefile for how to strip the annotations
 **)

(** First, import the entire Floyd proof automation system, which
 ** includes the VeriC program logic and the MSL theory of separation logic
 **)
Require Import VST.floyd.proofauto.

(** Import the theory of list segments.  This is not, strictly speaking,
 ** part of the Floyd system.  In principle, any user of Floyd can build
 ** theories of new data structures (list segments, trees, doubly linked
 ** lists, trees with cross edges, etc.).  We emphasize this by putting
 ** list_dt in the progs directory.   "dt" stands for "dependent types",
 ** as the theory uses Coq's dependent types to handle user-defined
 ** record fields.
 **)
Require Import VST.progs.list_dt. Import LsegSpecial.

(** Import the [reverse.v] file, which is produced by CompCert's clightgen
 ** from reverse.c.   The file reverse.v defines abbreviations for identifiers
 ** (variable names, etc.) of the C program, such as _head, _reverse.
 ** It also defines "prog", which is the entire abstract syntax tree
 ** of the C program in the reverse.c file.
 **)
Require Import VST.progs.reverse.

(* The C programming language has a special namespace for struct
** and union identifiers, e.g., "struct foo {...}".  Some type-based operators
** in the program logic need access to an interpretation of this namespace,
** i.e., the meaning of each struct-identifier such as "foo".  The next
** line (which looks identical for any program) builds this
** interpretation, called "CompSpecs" *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The reverse.c program uses the linked list structure [struct list].
 ** This satisfies the linked-list pattern, in that it has one self-reference
 ** field (in this case, called [tail]) and arbitrary other fields.  The [Instance]
 ** explains (and proves) how [struct list] satisfies the [listspec] pattern.
 **)
Instance LS: listspec _list _tail (fun _ _ => emp).
Proof. eapply mk_listspec; reflexivity. Defined.

(**  An auxiliary definition useful in the specification of [sumlist] *)
Definition sum_int := fold_right Int.add Int.zero.

Definition t_struct_list := Tstruct _list noattr.

(** Specification of the [sumlist] function from reverse.c.  All the functions
 ** defined in the file, AND extern functions imported by the .c file,
 ** must be declared in this way.
 **)
Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sh : share, contents : list int, p: val
  PRE [ _p OF (tptr t_struct_list) ]
     PROP(readable_share sh)
     LOCAL (temp _p p)
     SEP (lseg LS sh (map Vint contents) p nullval)
  POST [ tuint ]
     PROP()
     LOCAL(temp ret_temp (Vint (sum_int contents)))
     SEP (lseg LS sh (map Vint contents) p nullval).

Definition reverse_spec :=
 DECLARE _reverse
  WITH sh : share, contents : list val, p: val
  PRE  [ _p OF (tptr t_struct_list) ]
     PROP (writable_share sh)
     LOCAL (temp _p p)
     SEP (lseg LS sh contents p nullval)
  POST [ (tptr t_struct_list) ]
    EX p:val,
     PROP () LOCAL (temp ret_temp p)
     SEP (lseg LS sh (rev contents) p nullval).

(** The "main" function is special, since its precondition includes
 ** the spatial (SEP) resource describing all the extern initialized
 ** global variables.  That resource is calculated automatically
 ** from the program (prog) by the "main_pre" operator.  **)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]
     PROP() LOCAL (temp ret_temp (Vint (Int.repr (3+2+1)))) SEP(TT).

(** List all the function-specs, to form the global hypothesis *)
Definition Gprog : funspecs :=   ltac:(with_library prog [
    sumlist_spec; main_spec; reverse_spec]).

(** A little equation about the list_cell predicate *)
Lemma list_cell_eq: forall sh i p ,
   sepalg.nonidentity sh ->
   field_compatible t_struct_list [] p ->
   list_cell LS sh (Vint i) p =
   field_at sh t_struct_list (DOT _head) (Vint i) p.
Proof.
  intros.
  unfold list_cell, field_at; simpl.
  rewrite !prop_true_andp by auto with field_compatible.
  reflexivity.
Qed.

(** Here's a loop invariant for use in the body_sumlist proof *)
Definition sumlist_Inv (sh: share) (contents: list int) (p: val) : environ->mpred :=
          (EX cts1: list int, EX cts2: list int, EX t: val,
            PROP (contents = cts1++cts2)
            LOCAL (temp _t t; temp _s (Vint (sum_int cts1)))
            SEP ( lseg LS sh (map Vint cts1) p t ; lseg LS sh (map Vint cts2) t nullval)).

Lemma sum_int_app:
  forall a b, sum_int (a++b) = Int.add (sum_int a) (sum_int b).
Proof.
intros.
induction a; simpl. rewrite Int.add_zero_l; auto.
rewrite IHa. rewrite Int.add_assoc. auto.
Qed.

(** For every function definition in the C program, prove that the
 ** function-body (in this case, f_sumlist) satisfies its specification
 ** (in this case, sumlist_spec).
 **)
Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
(** Here is the standard way to start a function-body proof:  First,
 ** start-function; then forward.
 **)
start_function.
forward.  (* s = 0; *)
forward.  (* t = p; *)
forward_while (sumlist_Inv sh contents p).
* (* Prove that current precondition implies loop invariant *)
Exists (@nil int) contents p.
entailer!. cancel.
* (* Prove that loop invariant implies typechecking condition *)
entailer!.
* (* Prove that loop body preserves invariant *)
focus_SEP 1; apply semax_lseg_nonnull; [ | intros h' r y ? ?].
entailer!.
destruct cts2; inversion H0; clear H0; subst_any.
simpl. (* this line not necessary, but makes things look nicer *)
assert_PROP (field_compatible t_struct_list nil t) as FC by entailer!.
rewrite list_cell_eq by auto.
forward.  (* h = t->head; *)
forward.  (*  t = t->tail; *)
forward.  (* s = s + h; *)
Exists (cts1++[i],cts2,y).
entailer.
apply andp_right.
apply prop_right.
split.
rewrite app_ass; reflexivity.
 f_equal. rewrite sum_int_app. f_equal. simpl. apply Int.add_zero.
rewrite map_app. simpl map.
eapply derives_trans; [ | apply (lseg_cons_right_list LS) with (y:=t); auto].
rewrite list_cell_eq by auto.
cancel.
* (* After the loop *)
forward.  (* return s; *)
destruct cts2; [| inversion H]. rewrite <- app_nil_end.
entailer!.
Qed.

Definition reverse_Inv (sh: share) (contents: list val) : environ->mpred :=
          (EX cts1: list val, EX cts2 : list val, EX w: val, EX v: val,
            PROP (contents = rev cts1 ++ cts2)
            LOCAL (temp _w w; temp _v v)
            SEP (lseg LS sh cts1 w nullval;
                   lseg LS sh cts2 v nullval)).

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function.
forward.  (* w = NULL; *)
forward.  (* v = p; *)
forward_while (reverse_Inv sh contents).
* (* precondition implies loop invariant *)
Exists (@nil val) contents nullval p.
rewrite lseg_eq by (simpl; auto).
entailer!.
* (* loop invariant implies typechecking of loop condition *)
entailer!.
* (* loop body preserves invariant *)
focus_SEP 1; apply semax_lseg_nonnull;
        [entailer | intros h r y ? ?; simpl].
subst cts2.
forward. (* t = v->tail; *)
forward. (* v->tail = w; *)
(* The following line is optional, the proof works without it. *)
replace_SEP 2 (field_at sh t_struct_list (DOT _tail) w v) by entailer!.
forward.  (*  w = v; *)
forward.  (* v = t; *)
(* at end of loop body, re-establish invariant *)
Exists (h::cts1,r,v,y).
 simpl fst. simpl snd. simpl rev.
entailer!.  (* smt_test verif_reverse_example2 *)
 - rewrite app_ass. auto.
 - rewrite (lseg_unroll _ sh (h::cts1)).
    apply orp_right2.
   unfold lseg_cons.
   apply andp_right.
   + apply prop_right.
      destruct v; try contradiction; intro Hx; inv Hx.
   + Exists h cts1 w.
      entailer!.
* (* after the loop *)
forward.  (* return w; *)
Exists w; entailer!.
rewrite <- app_nil_end, rev_involutive.
auto.
Qed.

(** The next lemma concerns the extern global initializer,
 ** struct list three[] = {{1, three+1}, {2, three+2}, {3, NULL}};
 ** This is equivalent to a linked list of three elements [1,2,3].
 ** The proof is not very beautiful at present; it would be helpful
 ** to have a nicer proof theory for reasoning about this kind of thing.
 **)

Lemma setup_globals:
 forall Delta gv,
  PTree.get _three (glob_types Delta) = Some (tarray t_struct_list 3) ->
  ENTAIL Delta, PROP  ()
   LOCAL  (gvars gv)
   SEP
   (data_at Ews tuint (Vint (Int.repr 1)) (gv _three);
    mapsto Ews (tptr t_struct_list) (offset_val 4 (gv _three))
        (offset_val 8 (gv _three));
   mapsto Ews tuint (offset_val 8 (gv _three)) (Vint (Int.repr 2));
   mapsto Ews (tptr t_struct_list) (offset_val 12 (gv _three))
       (offset_val 16 (gv _three));
   mapsto Ews tuint (offset_val 16 (gv _three)) (Vint (Int.repr 3));
   mapsto Ews tuint (offset_val 20 (gv _three)) (Vint (Int.repr 0)))
  |-- PROP() LOCAL(gvars gv)
        SEP (lseg LS Ews (map Vint (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil))
                  (gv _three) nullval).
Proof.
  intros.
  go_lowerx.
  pose proof (gvars_denote_HP _ _ _ _ _ H2 H0 H).
  rewrite !prop_true_andp by auto.
  assert_PROP (size_compatible tuint (gv _three) /\ align_compatible tuint (gv _three)) by (entailer!; clear - H5; hnf in H5; intuition).
  rewrite <- mapsto_data_at with (v := Vint(Int.repr 1)); try intuition. 
  clear H0.
  rewrite <- (sepcon_emp (mapsto _ _ (offset_val 20 _) _)).
  assert (FC: field_compatible (tarray t_struct_list 3) [] (gv _three))
    by auto with field_compatible.
  match goal with |- ?A |-- _ => set (a:=A) end.
  replace (gv _three) with (offset_val 0 (gv _three)) by normalize.
  subst a.
  rewrite (sepcon_emp (lseg _ _ _ _ _)).
  rewrite sepcon_emp.
  repeat
  match goal with |- _ * (mapsto _ _ _ ?q * _) |-- lseg _ _ _ (offset_val ?n _) _ =>
    assert (FC': field_compatible t_struct_list [] (offset_val n (gv _three)));
      [apply (@field_compatible_nested_field CompSpecs (tarray t_struct_list 3)
         [ArraySubsc (n/8)] (gv _three));
       simpl;
       unfold field_compatible in FC |- *; simpl in FC |- *;
       assert (0 <= n/8 < 3) by (cbv [Z.div]; simpl; omega);
       tauto
      |];
    apply @lseg_unroll_nonempty1 with q;
      [destruct (gv _three); try contradiction; intro Hx; inv Hx | normalize; reflexivity | ];
    rewrite list_cell_eq by auto;
    do 2 (apply sepcon_derives;
      [ unfold field_at; rewrite prop_true_andp by auto with field_compatible;
        unfold data_at_rec, at_offset; simpl; normalize; try apply derives_refl | ]);
    clear FC'
    end.
  rewrite mapsto_tuint_tptr_nullval; auto. apply derives_refl.
  rewrite @lseg_nil_eq.
  entailer!.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
change (Tstruct _ _) with t_struct_list.
fold noattr. fold (tptr t_struct_list).
eapply semax_pre; [
  eapply ENTAIL_trans; [ | apply (setup_globals Delta gv); auto ] | ].
 entailer!.
*
forward_call (*  r = reverse(three); *)
  (Ews, map Vint [Int.repr 1; Int.repr 2; Int.repr 3], gv _three).
Intros r'.
rewrite <- map_rev. simpl rev.
forward_call  (* s = sumlist(r); *)
   (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil, r').
forward.  (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumlist.
semax_func_cons body_reverse.
semax_func_cons body_main.
Qed.


