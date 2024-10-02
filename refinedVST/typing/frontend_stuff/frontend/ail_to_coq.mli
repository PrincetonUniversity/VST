(** Entry point of the Cerberus typed Ail AST. *)
type typed_ail =
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.ail_program

(** [translate fname ail] translates the Cerberus typed Ail AST [ast] into our
    Coq AST. The file name [fname] should correspond to the C source file that
    lead to generating [ail].  In case of error an error message is displayed,
    and the program fails with error code [-1]. Note that any invalid RefinedC
    annotation is ignored (although a warning is displayed on [stderr]) but an
    error will be triggered if one attempts to generate a spec file. *)
val translate : string -> typed_ail -> Coq_ast.t
