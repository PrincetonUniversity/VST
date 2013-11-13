Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma example1:  (* from rearrange_regs_proof *)
name _a ->
name _b ->
name _c ->
name _d ->
name _e ->
name _f ->
name _g ->
name _h ->
name _l ->
name _Ki ->
name _i ->
name _T1 ->
name _T2 ->
name _data ->
name _ctx ->
forall (i : nat) (data : val) (bl : list int) (ctx : val),
isptr data ->
length bl = LBLOCK ->
i < 16 ->
forall w : int,
nth_error bl i = Some w ->
forall k : int,
nth_error K i = Some k ->
forall regs' : registers,
let Delta' :=
  initialized _Ki (initialized _l (initialized _l' Delta_loop1)) in
PROP  ()
LOCAL  (tc_environ Delta'; `(eq ctx) (eval_id _ctx);
`(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) (eval_id _data);
`(eq
    (Vint
       (big_endian_integer
          (fun z : Z =>
           force_option Int.zero
             (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap bl)))
                (z + Z.of_nat i * 4)))))) (eval_id _l);
`(eq (nth_error K i)) (`Some (`force_int (eval_id _Ki)));
`(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
`(eq (map Vint regs'))
  (`cons (eval_id _a)
     (`cons (eval_id _b)
        (`cons (eval_id _c)
           (`cons (eval_id _d)
              (`cons (eval_id _e)
                 (`cons (eval_id _f)
                    (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
SEP()
|-- PROP  (exists a b c d e f g h : int, regs' = [a, b, c, d, e, f, g, h])
    LOCAL  (`(eq ctx) (eval_id _ctx);
    `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data))
      (eval_id _data); `(eq (Vint w)) (eval_id _l);
    `(eq (Vint k)) (eval_id _Ki);
    `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
    `(eq (map Vint regs'))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
    SEP().
Proof.
intros; ungather_entail; revert Delta'; simplify_Delta.
entailer!.
* do 8 (destruct regs' as [ | ? regs']; [inv H9 | ]);
     destruct regs'; inv H9;  repeat eexists; reflexivity.
* apply nth_big_endian_integer''; auto .
* congruence.
Qed.

Lemma example2:  (* from body_SHA256_Init *)
name _c ->
EVAR
  (forall i : Z,
   EVAR
     (forall (j : reptype tuint) (c : val),
      PROP  ()
      LOCAL  (tc_environ (func_tycontext f_SHA256_Init Vprog Gtot);
      `(eq c) (eval_id _c))
      SEP 
      (`(array_at tuint Tsh
           (ZnthV tuint [Int.repr 1779033703, Int.repr (-1150833019)]) 0 8)
         (fun _ : lift_S (LiftEnviron mpred) => c);
      `(field_mapsto_ Tsh t_struct_SHA256state_st _Nl c);
      `(field_mapsto_ Tsh t_struct_SHA256state_st _Nh c);
      `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
      `(field_mapsto_ Tsh t_struct_SHA256state_st _num c))
      |-- local
            (`eq
               (`(eval_binop Oadd (tptr tuint) tint)
                  (fun _ : lift_S (LiftEnviron mpred) => c)
                  `(Vint (Int.repr i)))
               (eval_expr
                  (Ebinop Oadd
                     (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                           t_struct_SHA256state_st) _h (tarray tuint 8))
                     (Econst_int (Int.repr 2) tint) (tptr tuint)))) &&
          !!in_range 0 8 i &&
          local
            (tc_expr (func_tycontext f_SHA256_Init Vprog Gtot)
               (Ebinop Oadd
                  (Efield
                     (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                        t_struct_SHA256state_st) _h (tarray tuint 8))
                  (Econst_int (Int.repr 2) tint) (tptr tuint))) &&
          local
            (tc_expr (func_tycontext f_SHA256_Init Vprog Gtot)
               (Ecast (Econst_int (Int.repr 1013904242) tuint) tuint)) &&
          local
            (`(eq (Vint j))
               (eval_expr
                  (Ecast (Econst_int (Int.repr 1013904242) tuint) tuint))))).
Proof.
intros; ungather_entail;
 set (Delta := func_tycontext f_SHA256_Init Vprog Gtot); revert Delta; simplify_Delta.
unfold i,j; clear i j.
entailer!.
* reflexivity.
* compute; congruence.
* compute; congruence.
Qed.

