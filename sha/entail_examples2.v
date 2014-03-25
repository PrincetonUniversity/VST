Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope nat.
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
           force_int
             (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist bl)))
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
* apply nth_big_endian_integer; auto .
* congruence.
Qed.
