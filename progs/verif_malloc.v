Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

(* First draft specs.  Not specifying that chunks are aligned. *)

Require Import VST.progs.malloc.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z.
Local Open Scope logic.  

(* TODO 
Initially I imagined the constants would be defined as 
parameters (with suitable assumptions, e.g., BIGBLOCK
needs to be big enough for at least one chunk of the largest size,
because fill_bin unconditionally initializes the last chunk. 
*)
Definition WORD: Z := 4. (* sizeof(size_t) 4 for 32bit Clight; 8 in clang *)
Definition ALIGN: Z := 2.
Definition BINS: Z := 8. 
Parameter BIGBLOCK: Z.
Parameter BIGBLOCK_def: 
  Int.repr BIGBLOCK = Int.mul (Int.shl (Int.repr 2) (Int.repr 16)) (Int.repr WORD).

Definition bin2sizeZ := fun b: Z => (Z.mul ((Z.mul (b+1) ALIGN)-1) WORD).

Definition size2binZ : Z -> Z := fun s => 
   if zlt (bin2sizeZ(BINS-1)) s then -1 
   else (s+(Z.mul WORD (ALIGN-1))-1) / (Z.mul WORD ALIGN).


Eval compute in bin2sizeZ (BINS-1).
Example bin2sizeBINS: bin2sizeZ (BINS-1) = 60. Proof. reflexivity. Qed.

(* Hint Unfold WORD ALIGN : myDB.
auto with myDB 
*)

(* Some sanity checks; may not be needed for code verification. *)

Lemma claim1: forall s,
0 <= s <= bin2sizeZ(BINS-1) -> s <= bin2sizeZ(size2binZ s).
Proof. intros. 
unfold bin2sizeZ in *.
unfold size2binZ in *.
simpl in *.
assert (H1: bin2sizeZ 7 = 60). { apply bin2sizeBINS. }
rewrite H1.
unfold ALIGN, WORD.
destruct (zlt 60 s).
- simpl. omega.
- simpl.  auto with arith.
(* assert (H2: (((s + 4 - 1) / 8 + 1) * 2 - 1) * 4 = (((s + 3) / 8) * 8 + 4)) by algebra *)
admit.
Admitted.


Lemma claim2: forall s, 
0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.

Lemma claim3: forall s, 0 <= s <= bin2sizeZ(BINS-1) 
    -> size2binZ(bin2sizeZ(size2binZ(s))) = size2binZ(s).

Lemma claim4: forall b,
0 <= b < BINS -> Z.rem (bin2sizeZ b + WORD) (Z.mul WORD ALIGN) = 0.

Lemma claim5: forall b, 
0 <= b < BINS -> size2binZ(bin2sizeZ(b)) = b.
Proof.
  intros. 
  unfold size2binZ.
  assert (H1: (bin2sizeZ (BINS - 1) >= (bin2sizeZ b))) 
    by ( unfold bin2sizeZ; unfold WORD, ALIGN, BINS in *; omega).
  destruct (zlt (bin2sizeZ (BINS - 1)) (bin2sizeZ b)) as [H2|H2]. contradiction.
  unfold bin2sizeZ. 
  clear H H1 H2.
  assert (H3: 
     (((b + 1) * ALIGN - 1) * WORD + WORD * (ALIGN - 1) - 1) / (WORD * ALIGN)
     = (b*ALIGN*WORD + 2*ALIGN*WORD - 2*WORD -1)/(WORD*ALIGN)).
     { admit. (* algebra *) }
  rewrite H3; clear H3. unfold WORD, ALIGN, BINS. simpl.
  admit. (* algebra, including integer quotient *)
Admitted.


Definition sbrk_spec := 
(* like malloc without token;
and I removed the possibility of failure to streamline the proof of fill_bin *)
   DECLARE _sbrk
   WITH n:Z
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( (* if eq_dec p nullval then emp else memory_block Tsh n p) *)
             memory_block Tsh n p).

Definition bin2size_spec :=
 DECLARE _bin2size
  WITH b: Z
  PRE [ _b OF tint ] 
     PROP( 0 <= b <= Int.max_signed ) 
     LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ tuint ] 
     PROP() LOCAL(temp ret_temp (Vint (Int.repr (bin2sizeZ b)))) SEP ().

Definition size2bin_spec :=
 DECLARE _size2bin
  WITH s: Z
  PRE [ _s OF tuint ]    (* Vlong? *)
     PROP( 0 <= s <= Int.max_unsigned ) 
     LOCAL (temp _s (Vint (Int.repr s))) SEP ()
  POST [ tint ]
     PROP() LOCAL(temp ret_temp (Vint (Int.repr (size2binZ s)))) SEP ().

(* malloc token, which accounts for the size field and padding.
 * n is the size requested
 * Unfolding the definition reveals the stored size value and the
 * actual size of the block. 
 * Note that offset_val is in bytes, not like C pointer arith. *)
Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   data_at Tsh tuint (offset_val (- WORD) p) (Vint (Int.repr n)) 
 * memory_block Tsh ((bin2sizeZ(size2binZ(n)) - n)) (offset_val n p).

Lemma malloc_token'_valid_pointer:
  forall sh n p, malloc_token' sh n p |-- valid_pointer p.

Lemma malloc_token'_precise:
  forall sh n p, predicates_sl.precise (malloc_token' sh n p).

(* linked list, for free blocks.
p points to a linked list of len blocks, each of sz bytes,
of the form (sz,nxt,_) with link nxt, terminated at r.
Using nat for ease of termination check, at cost of Z conversions. 
*)
Fixpoint mmlist (sz: Z) (len: nat) (p: val) (r: val): mpred :=
 match len with
 | O => !! (ptr_eq p r) && emp
 | (S n) => EX q:val, !! is_pointer_or_null q && 
            data_at Tsh tuint (offset_val (-WORD) p) (Vint(Int.repr sz))
          * data_at Tsh (tptr tvoid) p q
          * memory_block Tsh (sz - WORD) (offset_val WORD p)
          * mmlist sz n q r
 end.


(* module invariant:
Each element of array points to a null-terminated list of right size blocks.

This version folds over index list, which makes it easy to express the 
block size per bin; it may facilitate per-index update.
*)
Definition mm_inv (arr: val): mpred := 
  EX bins: list val, EX lens: list nat,
  !! (Zlength bins = BINS /\ Zlength lens = BINS)  &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins arr
  * fold_right (fun (i: nat) => fun (mp: mpred) => 
     (mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens O) (nth i bins nullval) nullval) * mp )
    emp 
    (seq 0 (Z.to_nat BINS)).


(* copy of malloc_spec' from floyd library, with mm_inv added *)
Definition malloc_spec'' := 
   DECLARE _malloc
   WITH n:Z, bin:val
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive (Vint (Int.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin;
             if eq_dec p nullval then emp
             else (malloc_token Tsh n p * memory_block Tsh n p)).

Definition free_spec'' := (* copy from floyd lib, with mm_inv added *)
   DECLARE _free
   WITH p:_, n:_, bin:_
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p; gvar _bin bin)
       SEP (malloc_token Tsh n p; memory_block Tsh n p; mm_inv bin)
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv bin).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, bin:_
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp 1%positive (Vint (Int.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin; 
            if eq_dec p nullval then emp
            else (malloc_token' Tsh n p * memory_block Tsh n p)).

Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, n:_, s:_
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint ]
       PROP ( n = s )
       LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr s)))
       SEP (malloc_token' Tsh n p; memory_block Tsh n p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP ().


Definition fill_bin_spec :=
 DECLARE _fill_bin
  WITH b: _
  PRE [ _b OF tint ]
     PROP(0 <= b < BINS) LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ (tptr tvoid) ] EX p:_, EX len:Z,
     PROP( len > 0 ) 
     LOCAL(temp ret_temp p)
     SEP ( mmlist (bin2sizeZ b) (Z.to_nat len) p nullval ).


Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]  main_post prog nil u.

Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   sbrk_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; free_small_spec; malloc_spec''; free_spec'';
   main_spec]).


Lemma body_bin2size: semax_body Vprog Gprog f_bin2size bin2size_spec.
Proof. start_function. forward. Qed.


Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
forward_call (BINS-1). 
assert (BINS - 1 <= Int.max_signed ). {  admit. (* TODO how prove this? *) } 
split. unfold BINS. omega.  assumption.
forward_if(PROP() LOCAL() SEP (FF)). (* FF because join point unreachable: both branches return *)
- (* then *) 
forward. entailer!.  f_equal. rewrite Int.neg_repr.
assert (H1: size2binZ s = -1). {  
  unfold size2binZ; simpl. destruct (zlt (bin2sizeZ 7)). reflexivity. contradiction. }
rewrite -> H1. reflexivity.
- (* else *)
forward.  entailer!. f_equal.
assert (H1: Int.divu (Int.repr (s + (4 - 1))) (Int.repr (4 * 2)) = Int.repr (size2binZ s) ).
   { admit. } (* TODO divu property and def of size2binZ *)
rewrite -> H1. reflexivity.
- (* fi *)
intros.  unfold overridePost. if_tac.
go_lowerx.
entailer.
apply ENTAIL_refl.
(* done here *)
Admitted.

(* note to Andrew: forward_for wouldn't work until we added True to the Prop in the following.*)
Definition fill_bin_dummy (b:Z) (p:val) (qNs:val*Z*Z) := 
  PROP(True)LOCAL(temp _q (let '(q, _, _) := qNs in q);
         temp _p p; 
         temp _s (Vint (Int.repr (let '(_,_,s) := qNs in s))); 
         temp _b (Vint (Int.repr b)))
  SEP().

Definition fill_bin_Inv (b:Z) (p:val) (qNs:val*Z*Z) := 
(*  EX N:Z, EX s:Z, *)
  PROPx (let '(q,N,s) := qNs in 
        [s = bin2sizeZ b; 0 <= N; s + N*(WORD+s) <= BIGBLOCK])
  (LOCALx ([temp _q (let '(q,N,s):=qNs in q);
         temp _p p; 
         temp _s (Vint (Int.repr (let '(q,N,s):=qNs in s))); 
         temp _b (Vint (Int.repr b))])
  (SEPx ( let '(q,N,s):=qNs in
         [mmlist s (Z.to_nat N) (offset_val s p) q;
          memory_block Tsh (BIGBLOCK-(s+N*(WORD+s))) q] ))).

Definition fill_bin_preIncr (b:Z) (p:val) (qNs:val*Z*Z) :=
(*  EX N:Z, EX s:Z, 
William suggests localizing the lets so tactic pattern-matches may work *)
  PROP ( let '(q,N,s) := qNs in 
         s = bin2sizeZ b /\ 0 <= N /\ s + N*(WORD+s) <= BIGBLOCK )
  LOCAL (temp _q (let '(q,_,_) := qNs in q);
         temp _p p; 
         temp _s (Vint (Int.repr (let '(_,_,s) := qNs in s))); 
         temp _b (Vint (Int.repr b)))
  SEP (  let '(q,N,s) := qNs in 
         mmlist s (Z.to_nat N) (offset_val s p) q 
         * memory_block Tsh (BIGBLOCK - (s+N*(WORD+s)) - (WORD+s)) (offset_val (WORD+s) q) 
         * data_at Tsh tuint (Vint (Int.repr s)) q (* size *)
         * data_at Tsh (tptr tvoid) (offset_val (WORD+s) q) (offset_val WORD q) (* next *)
         * memory_block Tsh (s-WORD-WORD) (offset_val (WORD+WORD) q) (* rest of block *) ).

Lemma body_fill_bin: semax_body Vprog Gprog f_fill_bin fill_bin_spec.
Proof. 
start_function. 
forward_call (b). 
- unfold BINS in H. (* trivial arith but layers of definition *) admit.
- forward_call (BIGBLOCK).
  * entailer!. repeat f_equal. rewrite -> BIGBLOCK_def. auto.
  * (* trivial arith but layers of defs *) admit.
  * Intros p.
  
  check_Delta;
  repeat simple apply seq_assoc1;
  lazymatch type of (fill_bin_Inv b p) with
  | _ -> environ -> mpred => idtac
  | _ => fail "Invariant (first argument to forward_for) must have type (_ -> environ -> mpred)"
  end;
  lazymatch type of (fill_bin_preIncr b p) with
  | _ -> environ -> mpred => idtac
  | _ => fail "PreInc (second argument to forward_for) must have type (_ -> environ -> mpred)"
  end.
apply -> seq_assoc;
      apply semax_seq' with (exp (fill_bin_Inv b p)); abbreviate_semax.
      Focus 2.
      eapply semax_seq.

repeat  match goal with P := @abbreviate ret_assert _ |- semax _ _ _ ?P' =>
                         constr_eq P P'; unfold abbreviate in P; subst P
           end.
 match goal with |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) ?body) _) _ =>
   (tryif unify (no_breaks body) true 
          then idtac
      else fail "Since there is a break in the loop body, you need to supply an explicit postcondition using the 3-argument form of forward_for.");
   eapply semax_for_3g2 with (PQR:=(fill_bin_preIncr b p)) (*
        [ reflexivity 
        |intro  
        | intro ;
          match goal with |- ENTAIL ?Delta, ?Pre |-- local (`(eq _) (eval_expr ?e)) =>
            do_compute_expr1 Delta Pre e;
            match goal with v := _ : val , H: ENTAIL _ , _ |-- _ |- _ => subst v; apply H end
          end
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE
        | intro; let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE
        ]    *)
  end.
  reflexivity.
  intro.
  admit.
  intro.
  match goal with |- ENTAIL ?Delta, ?Pre |-- local (`(eq _) (eval_expr ?e)) =>
            do_compute_expr1 Delta Pre e end.
            match goal with v := _ : val , H: ENTAIL _ , _ |-- _ |- _ => subst v; apply H end
          end.
        forward_for2 (fill_bin_Inv b p) (fill_bin_preIncr b p) .
      
      
      [  | eapply semax_seq; 
         [ forward_for2 (fill_bin_Inv b p) (fill_bin_preIncr b p) 
          | abbreviate_semax;
            apply extract_exists_pre; intro;
            let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE]
   ].
     lazymatch goal with
  | |- semax _ _ (Ssequence (Sfor _ _ _ _) _) _ =>
      apply -> seq_assoc;
      apply semax_seq' with (exp (fill_bin_Inv b p)); abbreviate_semax;
      [  | eapply semax_seq; 
         [ forward_for2 (fill_bin_Inv b p) (fill_bin_preIncr b p) 
          | abbreviate_semax;
            apply extract_exists_pre; intro;
            let HRE := fresh in 
            apply semax_extract_PROP; intro HRE; 
            repeat (apply semax_extract_PROP; fancy_intro true);
            do_repr_inj HRE]
   ]
  | |- semax _ _ (Sfor _ _ _ _) ?Post =>
      apply semax_seq' with (exp (fill_bin_Inv b p)); abbreviate_semax; idtac "Hi"
(*      [  | forward_for3 (fill_bin_Inv b p) (fill_bin_preIncr b p) Post]*)
  | |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _) ?Post =>
     apply semax_pre with (exp (fill_bin_Inv b p));
      [  | forward_for3 (fill_bin_Inv b p) (fill_bin_preIncr b p) Post]
  | |- semax _ _ (Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _) _ =>
     apply semax_pre with (exp (fill_bin_Inv b p));
      [ unfold_function_derives_right | forward_for2 (fill_bin_Inv b p) (fill_bin_preIncr b p) ]
  | |- _ => fail "forward_for2x cannot recognize the loop"
  end.
  
  
      
    (* forward_for (fill_bin_dummy b p) (fill_bin_dummy b p) *)
    forward_for (fill_bin_Inv b p) (fill_bin_preIncr b p).  
    + (* initializer establishes invar *)
      forward.
      Exists (p, 0, (bin2sizeZ b)).
      entailer!.  unfold fill_bin_Inv. unfold mmlist. simpl.  (* TODO arith wrong in invar? *) admit.
    + (* definedness of loop guard *) entailer!.  ++ admit. ++ admit.
    + (* body preserves *)
      Intros. (* to flatten SEP clause; only worked when I distributed the lets finely in fill_bin_Inv *)
      (* forward fails, needs props about casts *)
admit.
    + (* loop increment - same problem *) admit.
    + (* after the loop WORKING HERE *)
      Intros.
      forward.

Admitted.



(*
TODO use freezer to frame over the loop (waste before the list): memory_block Tsh s p
*)

(* TODO likely lemmas for malloc_small?
Adding or removing at the head preserves mmlist (just unfold def, 
increment or decrement the length witness).
If bin[i] is null then assigning an mmlist preserves mm_inv 
(induct on indices to get to i).
*)
Lemma body_malloc_small:  semax_body Vprog Gprog f_malloc_small malloc_small_spec.
Proof. 
start_function. 
freeze [0] MMinv.
forward_call (n).
(* WORKING HERE *)

Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.


(* TODO Complete implementation of malloc and free,
   and an interesting main, before verifying these. *)

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_size2bin.
semax_func_cons body_bin2size.
semax_func_cons body_fill_bin.
semax_func_cons body_malloc_small.
semax_func_cons body_free_small.
semax_func_cons body_malloc.
semax_func_cons body_free.
semax_func_cons body_main.
Qed.

