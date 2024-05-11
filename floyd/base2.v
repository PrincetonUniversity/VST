Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Export VST.floyd.base.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Export VST.floyd.typecheck_lemmas.
Require Export VST.floyd.functional_base.
Require Export VST.floyd.seplog_tactics.
Require Export VST.floyd.const_only_eval.
Require Export VST.floyd.computable_functions.

Fixpoint delete_id {A: Type} i (al: list (ident*A)) : option (A * list (ident*A)) :=
 match al with
 | (j,x)::bl => if ident_eq i j then Some (x,bl)
                else match delete_id i bl with
                        | None => None
                        | Some (y,cl) => Some (y, (j,x)::cl)
                        end
  | nil => None
 end.

Inductive Impossible : Type := .

Definition cc_of_fundef (fd: Clight.fundef) : calling_convention :=
 match fd with
 | Internal f => fn_callconv f
 | External _ _ _ c => c
 end.

Definition funsig_of_fundef (fd: Clight.fundef) : funsig :=
 match fd with
 | Internal {| fn_return := fn_return; fn_params := fn_params |} =>
    (fn_params, fn_return)
 | External _ t t0 _ => (arglist 1 t, t0)
 end.

Section funspecs.

Context `{!heapGS Σ}.

Definition vacuous_funspec (fd: Clight.fundef): funspec :=
   NDmk_funspec (typesig_of_funsig (funsig_of_fundef fd)) (cc_of_fundef fd) 
   (Impossible) (fun _ => False) (fun _ => False).


Fixpoint augment_funspecs_new' (fds: list (ident * Clight.fundef)) (G: Maps.PTree.t funspec) : option funspecs :=
 match fds with
 | (i,fd)::fds' => match Maps.PTree.get i G with
                       | Some f =>
                              match augment_funspecs_new' fds' (Maps.PTree.remove i G) with
                               | Some G2 => Some ((i,f)::G2)
                               | None => None
                              end
                       | None =>
                              match augment_funspecs_new' fds' G with
                               | Some G2 => Some ((i, vacuous_funspec fd)::G2)
                               | None => None
                              end
                        end
 | nil => match Maps.PTree.elements G with nil => Some nil | _::_ => None end
 end.

Definition augment_funspecs_new prog (G:funspecs) : funspecs :=
 let Gt :=  fold_left (fun t ia => Maps.PTree.set (fst ia) (snd ia) t) G (Maps.PTree.empty _) in
 match augment_funspecs_new' (prog_funct prog) Gt with
 | Some G' => G'
 | None => nil
 end.

Fixpoint augment_funspecs' (fds: list (ident * Clight.fundef)) (G:funspecs) : option funspecs :=
 match fds with
 | (i,fd)::fds' => match delete_id i G with
                       | Some (f, G') =>
                              match augment_funspecs' fds' G' with
                               | Some G2 => Some ((i,f)::G2)
                               | None => None
                              end
                       | None =>
                              match augment_funspecs' fds' G with
                               | Some G2 => Some ((i, vacuous_funspec fd)::G2)
                               | None => None
                              end
                        end
 | nil => match G with nil => Some nil | _::_ => None end
 end.

Definition augment_funspecs prog G : funspecs :=
 match augment_funspecs' (prog_funct prog) G with
 | Some G' => G'
 | None => nil
 end.

Lemma decidable_eq_ident: ListDec.decidable_eq ident.
Proof.
intros ? ?.
red. destruct (ident_eq x y); auto.
Qed.

Lemma augment_funspecs_new_eq: forall prog G,
  augment_funspecs_new prog G = augment_funspecs prog G.
Abort.  (* Very likely true *)

End funspecs.
