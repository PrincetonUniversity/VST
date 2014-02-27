Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Require Import sha.verif_sha_bdo2.
Require Import sha.verif_sha_bdo3.
Require Import sha.verif_sha_bdo4.
Local Open Scope logic.

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int),
     length b = LBLOCK ->
     semax  Delta_loop1
 (PROP ()
   LOCAL (`(eq ctx) (eval_id _ctx);
               `(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( K_vector;
           `(array_at tuint Tsh (tuints b) 0 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq ctx) (eval_id _ctx);
                `(eq (map Vint (rnd_64 regs K (rev (generate_word (rev b) 48)))))
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP (K_vector;
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16))))).
Admitted.

Lemma semax_seq_congr:  (* not provable *)
 forall (Espec: OracleKind) s1 s1' s2 s2',
  (forall Delta P R, semax Delta P s1 R <-> semax Delta P s1' R) ->
  (forall Delta P R, semax Delta P s2 R <-> semax Delta P s2' R) ->
 (forall Delta P R, 
    semax Delta P (Ssequence s1 s2) R <->
    semax Delta P (Ssequence s1' s2') R).
Abort.

Definition load8 id ofs :=
 (Sset id
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr ofs) tint) (tptr tuint)) tuint)).

Lemma sha256_block_load8:
  forall (Espec : OracleKind) 
     (data: val) (r_h: list int) (ctx: val)
   (H5 : length r_h = 8%nat),
     semax  
      (initialized _data
         (func_tycontext f_sha256_block_data_order Vprog Gtot))
  (PROP  ()
   LOCAL  (`eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (tuints r_h) 0 (Zlength r_h) ctx)))
   (Ssequence (load8 _a 0)
     (Ssequence (load8 _b 1)
     (Ssequence (load8 _c 2)
     (Ssequence (load8 _d 3)
     (Ssequence (load8 _e 4)
     (Ssequence (load8 _f 5)
     (Ssequence (load8 _g 6)
     (Ssequence (load8 _h 7)
         Sskip))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (`(eq (map Vint r_h))
                    (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
)));
   `eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (tuints r_h) 0 (Zlength r_h) ctx)))).
Proof.
intros.
simplify_Delta.
unfold load8.
abbreviate_semax.
normalize.
simpl.
normalize.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
abbreviate_semax.
assert (H5': Zlength r_h = 8%Z).
rewrite Zlength_correct; rewrite H5; reflexivity.
do 8 (forward;
         [ entailer!; apply ZnthV_map_Vint_is_int; omega | ]).
forward.  (* skip; *)
entailer.
rewrite H,H0,H1,H2,H3,H4,H6,H7; clear H H0 H1 H2 H3 H4 H6 H7.
do 9 (destruct r_h as [ | ?h r_h ] ; [inv H5 | ]).
reflexivity.
inv H5.
Qed.

Definition get_h (n: Z) :=
    Sset _t
        (Ederef
           (Ebinop Oadd
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr n) tint) (tptr tuint)) tuint).

Definition add_h (n: Z) (i: ident) :=
   Sassign
       (Ederef
          (Ebinop Oadd
             (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                   t_struct_SHA256state_st) _h (tarray tuint 8))
             (Econst_int (Int.repr n) tint) (tptr tuint)) tuint)
       (Ebinop Oadd (Etempvar _t tuint) (Etempvar i tuint) tuint).

Definition add_them_back :=
 [get_h 0, add_h 0 _a,
  get_h 1, add_h 1 _b,
  get_h 2, add_h 2 _c,
  get_h 3, add_h 3 _d,
  get_h 4, add_h 4 _e,
  get_h 5, add_h 5 _f,
  get_h 6, add_h 6 _g,
  get_h 7, add_h 7 _h].

Lemma add_them_back_proof:
  forall (Espec : OracleKind)
     (b: list int) (r_h: list int)(ctx: val)(hashed: list int),
     length b = LBLOCK ->
     semax  Delta_loop1
   (PROP  ()
   LOCAL 
   (`(eq ctx) (eval_id _ctx);
    `(eq (map Vint (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0
       (Zlength (process_msg init_registers hashed)) ctx)))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL(`(eq ctx) (eval_id _ctx)) 
    SEP (`(array_at tuint Tsh (tuints
                   (map2 Int.add (process_msg init_registers hashed)
                                         (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
            0 (Zlength (process_msg init_registers hashed)) ctx)))).
Admitted.

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at_ _ _ _ _ _) =>
  (apply array_at__array_at; clear; simpl; congruence) : cancel.
(* move the Hint to malloc_lemmas.v, 
  and change the name of array_at__array_at to array_at_array_at_
*)

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
unfold sha256state_.
simpl_stackframe_of. 
remember (process_msg init_registers hashed) as regs eqn:Hregs.
assert (Lregs: length regs = 8%nat) 
  by (subst regs; apply length_process_msg).
assert (Zregs: Zlength regs = 8%Z)
 by (rewrite Zlength_correct; rewrite Lregs; reflexivity).
forward. (* data = in; *)
abbreviate_semax.
match goal with |- semax _ (PROPx nil ?QR) _ _ =>
 apply semax_pre0 with (PROPx [isptr data] QR)
end.
apply andp_right; [ | apply andp_left2; auto].
entailer.
normalize.
match goal with |- semax _ _ ?c _ =>
 eapply seq_assocN with (cs := sequenceN 8 c)
end.
eapply semax_frame1.
eapply sha256_block_load8 with (ctx:=ctx); eassumption.
simplify_Delta; reflexivity.
rewrite Zregs.
entailer!.
instantiate (1:=[K_vector]); simpl; (* this line shouldn't be needed? *)
 cancel.
auto 50 with closed.
abbreviate_semax.
simpl.
forward.  (* i = 0; *)

eapply semax_frame_seq
 with (Frame:= [`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0 8) (eval_id _ctx) ]).
replace Delta with Delta_loop1
 by (simplify_Delta; reflexivity).
simple apply (sha256_block_data_order_loop1_proof
  _ sh b ctx data regs); auto.
rewrite Zregs.
simpl_data_at.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.

eapply semax_frame_seq
 with (Frame := [`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0 8) (eval_id _ctx),
                          `(data_block sh (intlist_to_Zlist b) data)]).
apply sha256_block_data_order_loop2_proof
              with (regs:=regs)(b:=b); eassumption.
entailer!.
auto 50 with closed.
unfold app; abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).

eapply semax_frame1
 with (Frame := [
   K_vector,
  `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16)),
  `(data_block sh (intlist_to_Zlist b) data)]).
apply (add_them_back_proof _ b regs ctx hashed); try eassumption.
simplify_Delta; reflexivity.
rewrite <- Hregs; rewrite Zregs.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _t Delta_loop1) 
 by (unfold Delta, Delta_loop1; simplify_Delta; reflexivity).
clear Delta H2.
rewrite <- Hregs. rewrite Zregs.
simple apply sha256_block_data_order_return; assumption.
Qed.










