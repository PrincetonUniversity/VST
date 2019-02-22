Require Export VST.floyd.base.
Require Export VST.floyd.typecheck_lemmas.
Require Export VST.floyd.functional_base.
Require Export VST.floyd.seplog_tactics.
Require Export VST.floyd.const_only_eval.
Require Export compcert.cfrontend.Ctypes.
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

Inductive NOTE__Perhaps_you_need_to_Import_floyd_library___See_reference_manual_chapter___with_library : Type := .

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

Definition vacuous_funspec (fd: Clight.fundef): funspec :=
   mk_funspec (funsig_of_fundef fd) (cc_of_fundef fd) (rmaps.ConstType NOTE__Perhaps_you_need_to_Import_floyd_library___See_reference_manual_chapter___with_library) (fun _ _ => FF) (fun _ _ => FF) (const_super_non_expansive _ _) (const_super_non_expansive _ _).

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