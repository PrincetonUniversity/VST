Require Import veric.base.
Require Import veric.seplog.
Require Import veric.SequentialClight.
Require Import msl.msl_standard.
Require Import progs.list.
Require progs.test1.
Module P := progs.test1.

Import SeqC CSL.

SearchAbout semax_func.
Print funspec.

(* Admitted:  eliminate duplication definitions of arguments, funsig within veric *)

Definition sumlist_pre (contents: list int) (args: arguments) : predicate :=
  match args with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) contents) p (nullval, snd p)
  | _ => FF 
  end.

Definition sumlist_post (contents: list int) (res: arguments) : predicate :=
  match res with 
  | (Vint i, _) ::nil => prop (fold_right Int.add Int.zero contents = i)
  | _ => FF 
  end.

Definition sumlist_fsig : funsig := (Tcons P.t_listptr Tnil, P.t_int).

Definition reverse_pre (contents: list int) (args: arguments) : predicate :=
  match args with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) contents) p (nullval, snd p)
  | _ => FF 
  end.

Definition reverse_post (contents: list int) (res: arguments) : predicate :=
  match res with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) (rev contents)) p (nullval, snd p)
  | _ => FF 
  end.

Definition reverse_fsig : funsig := (Tcons P.t_listptr Tnil, P.t_listptr).

Definition main_fsig : funsig := (Tnil, P.t_int).

Definition Gprog : funspecs := 
  (P.i_sumlist, mk_funspec sumlist_fsig _ sumlist_pre sumlist_post)::
  (P.i_reverse, mk_funspec reverse_fsig _ reverse_pre reverse_post)::
  (P.i_main, mk_funspec main_fsig _ (main_pre P.prog) (main_post P.prog))::
nil.

Ltac prove_notin := clear; simpl; intuition; match goal with H: _ = _ |- _ => inv H end.

Lemma body_sumlist:
   semax_body Gprog P.f_sumlist _ sumlist_pre sumlist_post.
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro contents.
simpl.
Admitted.

Lemma body_reverse:
   semax_body Gprog P.f_reverse _ reverse_pre reverse_post.
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro contents.
simpl.
Admitted.

Lemma body_main:
   semax_body Gprog P.f_main _ (main_pre P.prog) (main_post P.prog).
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro x; destruct x.
simpl.
Admitted.

Lemma all_funcs_correct:
  semax_func Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [compute; auto | prove_notin | apply body_sumlist | ].
apply semax_func_cons; [compute; auto | prove_notin | apply body_reverse | ].
apply semax_func_cons; [compute; auto | prove_notin | apply body_main | ].
apply semax_func_nil.
Qed.




