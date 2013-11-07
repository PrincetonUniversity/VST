Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma and_mone':
 forall x, Int.and x (Int.repr (-1)) = x.
Proof.
apply Int.and_mone.
Qed.

Lemma Sigma_1_eq: forall f_,
  Sigma_1 f_ =
            (Int.xor
              (Int.xor
                 (Int.or (Int.shl f_ (Int.repr 26))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 26))))
                 (Int.or (Int.shl f_ (Int.repr 21))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 21)))))
              (Int.or (Int.shl f_ (Int.repr 7))
                 (Int.shru (Int.and f_ (Int.repr (-1)))
                    (Int.sub (Int.repr 32) (Int.repr 7))))).
Proof.
intros.
unfold Sigma_1, Sh.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 26)) with (Int.repr 6).
change (Int.sub (Int.repr 32) (Int.repr 21)) with (Int.repr 11).
change (Int.sub (Int.repr 32) (Int.repr 7)) with (Int.repr 25).
reflexivity.
Qed.

Lemma  Sigma_0_eq: forall b_,
   Sigma_0 b_ = 
      (Int.xor
        (Int.xor
           (Int.or (Int.shl b_ (Int.repr 30))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 30))))
           (Int.or (Int.shl b_ (Int.repr 19))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 19)))))
        (Int.or (Int.shl b_ (Int.repr 10))
           (Int.shru (Int.and b_ (Int.repr (-1)))
              (Int.sub (Int.repr 32) (Int.repr 10))))).
Proof.
intros.
unfold Sigma_0, Sh.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 19)) with (Int.repr 13).
change (Int.sub (Int.repr 32) (Int.repr 10)) with (Int.repr 22).
change (Int.sub (Int.repr 32) (Int.repr 30)) with (Int.repr 2).
reflexivity.
Qed.

Lemma Ch_eq: forall f_ g_ h_,
  Ch f_ g_ h_ =
        (Int.xor (Int.and f_ g_) (Int.and (Int.not f_) h_)).
Proof. reflexivity.
Qed.

Lemma Maj_eq:
  forall b c d, 
  Maj b c d =
  (Int.xor (Int.xor (Int.and b c) (Int.and b d)) (Int.and c d)).
Proof.
intros.
unfold Maj.
rewrite (Int.xor_commut) at 1.
rewrite Int.xor_assoc. auto.
Qed.

Lemma rearrange_aux:
 forall h f c k l,
 Int.add (Int.add (Int.add (Int.add h f) c) k) l =
Int.add (Int.add (Int.add (Int.add l h) f) c) k.
Proof.
intros.
rewrite <- (Int.add_commut l).
repeat rewrite (Int.add_assoc h).
rewrite <- (Int.add_assoc l).
repeat rewrite (Int.add_assoc (Int.add l h)).
reflexivity.
Qed.

Lemma rearrange_aux2: 
forall (Espec : OracleKind) (i : nat)(w k : int)
  (regs' : registers) (a b c d e f g h : int) (eqofs : val -> Prop),
i < 16 ->
semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL  (`eqofs (eval_id _data); `(eq (Vint w)) (eval_id _l);
   `(eq (Vint k)) (eval_id _Ki);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint [a, b, c, d, e, f, g, h]))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP()) rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
      `eqofs (eval_id _data);
      `(eq (map Vint (rnd_function [a, b, c, d, e, f, g, h]  k w)))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
        SEP())).
Proof.
{
intros.
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
name i_ _i.
name T1 _T1.
name T2 _T2.
name data_ _data.
unfold Delta_loop1; simplify_Delta.
simpl.
unfold rearrange_regs.
repeat forward.
simpl eval_binop.
go_lower0;
repeat (apply derives_extract_prop; intro);
repeat apply andp_right; try apply prop_right; auto.
decompose [and] H2; clear H2; subst.
inv H17.
repeat match goal with 
 | H: eval_id _ rho = _ |- _ => rewrite H in *; clear H
 | H: _ = eval_id _ rho |- _ => rewrite <- H in *; clear H
end.
repeat split; auto.
clear H13 H0 rho H1 H19 Delta.
clear.
cbv beta iota delta [sem_and sem_notint sem_or sem_shl sem_shr sem_or sem_add sem_xor]; simpl.
repeat rewrite <- Sigma_1_eq.
repeat rewrite <- Sigma_0_eq.
repeat rewrite <- Ch_eq.
repeat rewrite <- Maj_eq.
repeat rewrite (rearrange_aux h).
reflexivity.
}
Admitted.  (* can't Qed, because it goes over 2 gigabytes *)

Lemma rearrange_regs_proof:
 forall (Espec: OracleKind) i (data: val) bl regs
 (Hdata: isptr data)
 (H: length bl = LBLOCK)
 (H0: i < 16), 
 semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL 
   (`(eq (offset_val (Int.repr (Zsucc (Z.of_nat i) * 4)) data)) (eval_id _data);
   `(eq (Vint (big_endian_integer
             (fun z : Z =>
              force_option Int.zero
                (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap bl)))
                   (z + Z.of_nat i * 4))))))
       (eval_id _l);
   `(eq (nth_error K i)) (`Some  (`force_int (eval_id _Ki)));
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint (rnd_64 regs K (firstn i bl))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP()) rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq (Vint (Int.repr (Z.succ (Z.of_nat i) - 1)))) (eval_id _i);
      `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) (eval_id _data);
      `(eq (map Vint (rnd_64 regs K (firstn (S i) bl))))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
        SEP())).
Proof.
intros.
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
name i_ _i.
name T1 _T1.
name T2 _T2.
name data_ _data.
assert (exists w, nth_error bl i = Some w).
 apply assert_lemmas.nth_error_in_bounds.
change LBLOCK with 16 in H; omega.
destruct H1 as [w H1].
assert (exists k, nth_error K i = Some k).
 apply assert_lemmas.nth_error_in_bounds.
compute; split; omega.
destruct H2 as [k H2].
set (Delta := initialized _Ki (initialized _l (initialized _l' Delta_loop1))).
set (Delta' := initialized _Ki (initialized _l (initialized _l' Delta_loop1))).
assert (Delta' = Delta) by reflexivity.
revert H3.
revert Delta.
cbv delta [Delta_loop1].
simplify_Delta.
intro HDelta'.
match goal with
         | |- semax ?D _ _ _  =>
               abbreviate D : tycontext as Delta
end.
assert (HDelta'': Delta' = Delta) by reflexivity.
clear HDelta'.
rewrite (rnd_64_S _ _ _ _ _ H2 H1).
forget (rnd_64 regs K (firstn i bl)) as regs'.
apply semax_pre with
  (PROP  (exists a, exists b, exists c, exists d, 
              exists e, exists f, exists g, exists h,
                regs' = [a,b,c,d,e,f,g,h])
   LOCAL 
   (`(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data))
      (eval_id _data);
   `(eq (Vint w)) (eval_id _l);
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
   SEP()).
abstract (entailer;
  [(exists a_, b_, c_, d_, e_, f_, g_, h_;
    clear - H4; rename H4 into H0;
    do 8 (destruct regs' as [ | ? regs']; [inv H0 | ]);
    destruct regs'; inv H0; reflexivity)
  | apply nth_big_endian_integer''; auto 
  | congruence]).
apply semax_extract_PROP; 
   intros [a [b [c [d [e [f [g [h Hregs]]]]]]]].
forget (eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) as eqofs.
clear Hdata data.
replace (Z.succ (Z.of_nat i) - 1)%Z with (Z.of_nat i) by (clear; omega).
rewrite <- HDelta''; unfold Delta'.
clear Delta' HDelta'' Delta.
subst regs'.
eapply rearrange_aux2; eassumption. 
Qed.
