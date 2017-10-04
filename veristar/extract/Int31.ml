(* Module Int31, matches the (extracted) part
 of the UsualOrderedType signature *)

  type t = int

  (** val eq_dec : t -> t -> bool **)

  let eq_dec = (fun (x:int)(y : int) -> x=y)

  (** val compare : t -> t -> comparison **)

  let compare = fun (x:int)(y : int)->
    if x < y then Lt else if x > y then Gt else Eq
