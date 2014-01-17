(* compute.v - Mario Alvarez - January 2014
 * Implementation of "compute" solver plugin for MirrorShard *)

(* Need all of these? *)
Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import Expr.
(* Require Import wrapExpr. *)


(* From functions.v. Unsure if this is the best way to proceed. *)
Module compute (uk : unknown_types).
Module our_funcs := funcs uk.
Import our_funcs.
Import all_types.

Check Z.lt.

(* From entailer.v. Need to pare this down... *)
(*
Inductive computable: forall {A}(x: A), Prop :=
| computable_O: computable O
| computable_S: forall x, computable x -> computable (S x)
| computable_Zlt: forall x y, computable x -> computable y -> computable (Z.lt x y)
| computable_Zle: forall x y, computable x -> computable y -> computable (Z.le x y)
| computable_Zgt: forall x y, computable x -> computable y -> computable (Z.gt x y)
| computable_Zge: forall x y, computable x -> computable y -> computable (Z.ge x y)
| computable_eq: forall  A (x y: A), computable x -> computable y -> computable (eq x y)
| computable_ne: forall  A (x y: A), computable x -> computable y -> computable (x <> y)
| computable_Zpos: forall x, computable x -> computable (Zpos x)
| computable_Zneg: forall x, computable x -> computable (Zneg x)
| computable_Z0: computable Z0
| computable_xI: forall x, computable x -> computable (xI x)
| computable_xO: forall x, computable x -> computable (xO x)
| computable_xH: computable xH
| computable_Zadd: forall x y, computable x -> computable y -> computable (Z.add x y)
| computable_Zsub: forall x y, computable x -> computable y -> computable (Z.sub x y)
| computable_Zmul: forall x y, computable x -> computable y -> computable (Z.mul x y)
| computable_Zdiv: forall x y, computable x -> computable y -> computable (Z.div x y)
| computable_Zmod: forall x y, computable x -> computable y -> computable (Zmod x y)
| computable_Zmax: forall x y, computable x -> computable y -> computable (Z.max x y)
| computable_Zopp: forall x, computable x -> computable (Z.opp x)
| computable_Inteq: forall x y, computable x -> computable y -> computable (Int.eq x y)
| computable_Intlt: forall x y, computable x -> computable y -> computable (Int.lt x y)
| computable_Intltu: forall x y, computable x -> computable y -> computable (Int.ltu x y)
| computable_Intadd: forall x y, computable x -> computable y -> computable (Int.add x y)
| computable_Intsub: forall x y, computable x -> computable y -> computable (Int.sub x y)
| computable_Intmul: forall x y, computable x -> computable y -> computable (Int.mul x y)
| computable_Intneg: forall x, computable x  -> computable (Int.neg x)
| computable_Ceq: computable Ceq
| computable_Cne: computable Cne
| computable_Clt: computable Clt
| computable_Cle: computable Cle
| computable_Cgt: computable Cgt
| computable_Cge: computable Cge
| computable_Intcmp: forall op x y, 
  computable op -> computable x -> computable y -> computable (Int.cmp op x y)
| computable_Intcmpu: forall op x y, 
  computable op -> computable x -> computable y -> computable (Int.cmpu op x y)
| computable_Intrepr: forall x, computable x -> computable (Int.repr x)
| computable_Intsigned: forall x, computable x -> computable (Int.signed x)
| computable_Intunsigned: forall x, computable x -> computable (Int.unsigned x)
| computable_two_power_nat: forall x, computable x -> computable (two_power_nat x)
| computable_max_unsigned: computable (Int.max_unsigned)
| computable_align: forall x y, computable x -> computable y -> computable (align x y).
*)

(* Builtins *)

(* Have cases for all our built-in functions that the solver needs to handle *)
Check tc_environ.

Local Open Scope nat.
Import ListNotations.

(* Perform computation on reified objects *)
(* For now, assume a fancy is_const; and assume that we will get datatypes as consts
 * Don't treat data constructors as functions *)

Fixpoint compute (e : expr all_types) : expr all_types :=
  let our_const tv val := @Const all_types tv val in
  match e with
    (* Func 0 is tc_environ_f; not computable *)

    | Func 1 (* O_f *) [] => our_const (tvType 11 (* nat_tv *)) O

    | Func 2  (* force_ptr_f *) [tv] =>
      match compute tv with
        | Const (tvType 4 (* val_tv *)) tv' => our_const (tvType 4 (* val_tv *)) (force_ptr tv')
        | _ => e
      end
    
    | Func 3  (* app_val_f *) [l1; l2] =>
      match compute l1 with
        | Const (tvType 7 (* list_val_tv *)) l1' =>
          match compute l2 with
            | Const (tvType 7 (* list_val_tv *)) l2' => our_const (tvType 7 (* list_val_tv *)) (l1' ++ l2')
            | _ => e
          end
        | _ => e
      end

    (* Func 4 is eval_id_f; not computable *)

    | Func 5  (* and_f *) [p1; p2] =>
      match compute p1 with
        | Const tvProp p1' =>
          match compute p2 with
            | Const tvProp p2' => our_const tvProp (p1' /\ p2')
            | _ => e
          end
        | _ => e
      end

    | Func 6 (* align_f *) [v amnt] =>
      match compute v with
        | Cons (tvType 10 (* Z_tv *)) v' =>
          match compute amnt with
            | Cons (tvType 10 (* Z_tv *)) amnt' => our_const (tvType 10 (* Z_tv *)) (align v' amnt')
            | _ => e
          end
        | _ => e
      end

    (* Func 6 is eq_list_val_f; need to replace *)

    | Func 7  (* cons_val_f *) [h; t] =>
      match compute h with
        | Const (tvType 4 (* val_tv *)) h' =>
          match compute t with
            | Const (tvType 7 (* list_val_tv *)) t' => our_const (tvType 7 (* list_val_tv *)) (h' :: t')
            | _ => e
          end
        | _ => e
      end

    | Func 8  (* int_sub_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 9 (* int_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 9 (* int_tv *)) (Int.sub v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 9  (* vint_f *) [i] =>
      match compute i with
        | Const (tvType 9 (* int_tv *)) i' => our_const (tvType 4 (* val_tv *)) (Vint i')
        | _ => e
      end

    | Func 10 (* map_Vint_f *) [is] =>
      match compute is with
        | Const (tvType 8 (* list_int_tv *)) is' => our_const (tvType 7 (* list_val_tv *)) (map Vint is')
        | _ => e
      end

    | Func 11 (* typed_true_f *) [t; v] =>
      match compute t with
        | Const (tvType 2 (* c_type_tv *)) t' =>
          match compute v with
            | Const (tvType 4 (* val_tv *)) v' => our_const tvProp (typed_true t' v')
            | _ => e
          end
        | _ => e
      end

    | Func 12 (* int_add_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 9 (* int_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 9 (* int_tv *))  (Int.add v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 13 (* S_f *) [n] =>
      match compute n with
        | Const (tvType 11 (* nat_tv *)) n' => our_const (tvType 11 (* nat_tv *)) (S n')
        | _ => e
      end

    | Func 14 (* Z_lt_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const tvProp (Z.lt v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 15 (* Z_le_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const tvProp (Z.le v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 16 (* Z_gt_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const tvProp (Z.gt v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 17 (* Z_ge_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const tvProp (Z.ge v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 18 (* Zpos_f *) [p] =>
      match compute p with
        | Const (tvType 12 (* positive_tv *)) p' => our_const (tvType 10 (* Z_tv *)) (Zpos p')
        | _ => e
      end

    | Func 19 (* Zneg_f *) [p] =>
      match compute p with
        | Const (tvType 12 (* positive_tv *)) p' => our_const (tvType 10 (* Z_tv *)) (Zneg p')
        | _ => e
      end

    | Func 20 (* Z0_f *) [] => our_const (tvType 10 (* Z_tv *)) Z0

    | Func 21 (* xI_f *) [p] =>
      match compute p with
        | Const (tvType 12 (* positive_tv *)) p' => our_const (tvType 12 (* positive_tv *)) (xI p')
        | _ => e
      end

    | Func 22 (* xO_f *) [p] =>
      match compute p with
        | Const (tvType 12 (* positive_tv *)) p' => our_const (tvType 12 (* positive_tv *)) (xO p')
        | _ => e
      end

    | Func 23 (* xH_f *) [] => our_const (tvType 12 (* positive_tv *)) xH

    | Func 24 (* int_lt_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 9 (* int_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 13 (* bool_tv *)) (Int.lt v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 25 (* int_ltu_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 9 (* int_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 13 (* bool_tv *)) (Int.ltu v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 26 (* int_mul_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 9 (* int_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 9 (* int_tv *)) (Int.mul v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 27 (* int_neg_f *) [v] =>
      match compute v with
        | Const (tvType 9 (* int_tv *)) v' => our_const (tvType 9 (* int_tv *)) (Int.neg v')
        | _ => e
      end

    | Func 28 (* Z_add_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.add v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 29 (* Z_sub_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.sub v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 30 (* Z_mul_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.mul v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 31 (* Z_div_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.div v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 32 (* Z_mod_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.mod v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 33 (* Z_max_f *) [v1; v2] =>
      match compute v1 with
        | Const (tvType 10 (* Z_tv *)) v1' =>
          match compute v2 with
            | Const (tvType 10 (* Z_tv *)) v2' => our_const (tvType 10 (* Z_tv *)) (Z.max v1' v2')
            | _ => e
          end
        | _ => e
      end

    | Func 34 (* Z_opp_f *) [v] =>
      match compute v with
        | Const (tvType 10 (* Z_tv *)) v' => our_const (tvType 10 (* Z_tv *)) (Z.opp v')
        | _ => e
      end

    | Func 35 (* Ceq_f *) [] => our_const (tvType 14 (* comparison_tv *)) Ceq.

    | Func 36 (* Cne_f *) [] => our_const (tvType 14 (* comparison_tv *)) Cne.

    | Func 37 (* Clt_f *) [] => our_const (tvType 14 (* comparison_tv *)) Clt.

    | Func 38 (* Cle_f *) [] => our_const (tvType 14 (* comparison_tv *)) Cle.

    | Func 39 (* Cgt_f *) [] => our_const (tvType 14 (* comparison_tv *)) Cgt.

    | Func 40 (* Cge_f *) [] => our_const (tvType 14 (* comparison_tv *)) Cge.

    | Func 41 (* int_cmp_f *) [c; v1; v2] =>
      match compute c with
        | Const (tvType 14 (* comparison_tv *)) c' =>
          match compute v1 with
            | Const (tvType 9 (* int_tv *)) v1' =>
              match compute v2 with
                | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 13 (* bool_tv *)) (Int.cmp c' v1' v2')
                | _ => e
              end
            | _ => e
          end
        | _ => e
      end

    | Func 42 (* int_cmpu_f *) [c; v1; v2] =>
      match compute c with
        | Const (tvType 14 (* comparison_tv *)) c' =>
          match compute v1 with
            | Const (tvType 9 (* int_tv *)) v1' =>
              match compute v2 with
                | Const (tvType 9 (* int_tv *)) v2' => our_const (tvType 13 (* bool_tv *)) (Int.cmpu c' v1' v2')
                | _ => e
              end
            | _ => e
          end
        | _ => e
      end

    | Func 43 (* int_repr_f *) [v] =>
      match compute v with
        | Const (tvType 10 (* Z_tv *)) v' => our_const (tvType 9 (* int_tv *)) (Int.repr v')
        | _ => e
      end

    | Func 44 (* int_signed_f *) [v] =>
      match compute v with
        | Const (tvType 9 (* int_tv *)) v' => our_const (tvType 10 (* Z_tv *)) (Int.signed v')
        | _ => e
      end

    | Func 45 (* int_unsigned_f *) [v] =>
      match compute v with
        | Const (tvType 9 (* int_tv *)) v' => our_const (tvType 10 (* Z_tv *)) (Int.unsigned v')
        | _ => e
      end

    | Func 46 (* two_power_nat_f *) [n] =>
      match compute n with
        | Const (tvType 11 (* nat_tv *)) n' => our_const (tvType 10 (* Z_tv *)) (two_power_nat n')
        | _ => e
      end

    | Func 47 (* int_max_unsigned_f *) [] => our_const (tvType 10 (* Z_tv *)) Int.max_unsigned

    | _ => e

  end.