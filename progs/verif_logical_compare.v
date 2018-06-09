Require Import VST.floyd.proofauto.
Require Import VST.progs.logical_compare.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

(****  START *)

Definition logical_and_result v1 v2 : int :=
   if Int.eq v1 Int.zero then Int.zero else v2.

Definition logical_or_result v1 v2 : int :=
  if Int.eq v1 Int.zero then v2 else Int.one.

Fixpoint quick_shortcut_logical (s: statement) : option ident :=
match s with
| Sifthenelse _
     (Sset id (Econst_int _ (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})))
     s2 => match quick_shortcut_logical s2 with None => None | Some id2 =>
                 if ident_eq id id2 then Some id else None
                end
| Sifthenelse e1 s2
     (Sset id (Econst_int _ (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})))
      => match quick_shortcut_logical s2 with None => None | Some id2 =>
                 if ident_eq id id2 then Some id else None
            end
| Sset id (Ecast _ (Tint IBool Unsigned {| attr_volatile := false; attr_alignas := None |})) =>
        Some id
| _ => None
end.

Fixpoint shortcut_logical (eval: expr -> option val) (tid: ident) (s: statement)
            : option (int * list expr) :=
match s with
| Sifthenelse e1
     (Sset id (Econst_int one (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})))
     s2 => if andb (eqb_ident id tid) (Int.eq one Int.one)
                then match eval e1 with
                        | Some (Vint v1) =>
                           match shortcut_logical eval tid s2 with
                           | Some (v2, el) => Some (logical_or_result v1 v2, e1 :: el)
                           | _ => None
                           end
                        | _ => None
                        end
                else None
| Sifthenelse e1 s2
     (Sset id (Econst_int zero (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})))
      => if andb (eqb_ident id tid) (Int.eq zero Int.zero)
            then match eval e1 with
                     | Some (Vint v1) =>
                      match shortcut_logical eval tid s2 with
                      | Some (v2, el) => Some (logical_and_result v1 v2, e1 :: el)
                      | _ => None
                      end
                   | _ => None
                end
            else None
| Sset id (Ecast e (Tint IBool Unsigned {| attr_volatile := false; attr_alignas := None |})) =>
        if eqb_ident id tid
        then match eval (Ecast e tbool) with
                 | Some (Vint v) => Some (v, (Ecast e tbool :: nil))
                 | _ => None
                end
        else None
| _ => None
end.

Lemma semax_shortcut_logical:
  forall Espec {cs: compspecs} Delta P Q R tid s v Qtemp Qvar GV el,
   quick_shortcut_logical s = Some tid ->
   typeof_temp Delta tid = Some tint ->
   local2ptree Q = (Qtemp, Qvar, nil, GV) ->
   Qtemp ! tid = None ->
   shortcut_logical (msubst_eval_expr Delta Qtemp Qvar GV) tid s = Some (v, el) ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- fold_right (fun e q => tc_expr Delta e && q) TT el ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
          s (normal_ret_assert (PROPx P (LOCALx (temp tid (Vint v) :: Q) (SEPx R)))).
Admitted.

(***** END *)

Definition do_or_spec :=
 DECLARE _do_or
  WITH a: int, b : int
  PRE [ _a OF tbool, _b OF tbool ]
        PROP () LOCAL (temp _a (Vint a); temp _b (Vint b)) SEP ()
  POST [ tbool ]
        PROP() LOCAL (temp ret_temp (Vint (logical_or_result a b)))
        SEP().


Definition do_and_spec :=
 DECLARE _do_and
  WITH a: int, b : int
  PRE [ _a OF tbool, _b OF tbool ]
        PROP () LOCAL (temp _a (Vint a); temp _b (Vint b)) SEP ()
  POST [ tbool ]
        PROP() LOCAL (temp ret_temp (Vint (logical_and_result a b)))
        SEP().


Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=
      ltac:(with_library prog [do_or_spec; do_and_spec; main_spec]).

Ltac do_semax_shortcut_logical :=
 eapply semax_shortcut_logical;
   [ reflexivity | reflexivity | prove_local2ptree
   | reflexivity | reflexivity
   | unfold fold_right; entailer  ].

Lemma body_do_or: semax_body Vprog Gprog f_do_or do_or_spec.
Proof.
start_function.

eapply semax_seq'; [do_semax_shortcut_logical | abbreviate_semax].
forward.
destruct H,H0; subst; simpl; entailer!.
Qed.

Lemma body_do_and: semax_body Vprog Gprog f_do_and do_and_spec.
Proof.
start_function.
eapply semax_seq'; [do_semax_shortcut_logical | abbreviate_semax].
forward.
destruct H,H0; subst; simpl; entailer!.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_do_or.
semax_func_cons body_do_and.
semax_func_cons body_main.
Qed.

