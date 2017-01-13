(* driver.ml:
   -translates Smallfoot entailments to VeriStar entailments
   -pretty-prints entailments *)

open Veristar
open Ident
open VeriStar
open VeriStar
open Superposition
open Misc
open Config
open Symbtree
open Printf

let rec nat2int = function
  | O -> 0
  | S n' -> 1 + (nat2int n')

let rec pos2int = function
  | XH -> 1
  | XO(p) -> 2 * pos2int p
  | XI(p) -> 2 * pos2int p + 1

(* start pretty-printing entailments *)
let expr2string = function
  | Nil -> "nil"
  | Var(x) -> "x" ^ (string_of_int x)

let rec list2string f sep = function
  | [] -> ""
  | x :: [] -> f x
  | x :: y :: l' -> f x ^ sep ^ list2string f sep (y::l')

let atom2string b = function
  | Eqv(x, y) ->
    if b then expr2string x ^ "==" ^ expr2string y
    else expr2string x ^ "!=" ^ expr2string y

let pnatom2string = function
  | Equ(x, y)  -> expr2string x ^ "==" ^ expr2string y
  | Nequ(x, y) -> expr2string x ^ "!=" ^ expr2string y

let space_atom2string = function
  | Next(x, y) -> "next(" ^ expr2string x ^ "," ^ expr2string y ^ ")"
  | Lseg(x, y) -> "lseg(" ^ expr2string x ^ "," ^ expr2string y ^ ")"

let entailment2string n = function
  | Entailment(Assertion(p, s), Assertion(p', s')) ->
      let p0 = list2string pnatom2string "*" p in
      let s0 = list2string space_atom2string "*" s in
      let p0' = list2string pnatom2string "*" p' in
      let s0' = list2string space_atom2string "*" s' in
      "[" ^ list2string (fun s -> s) "*"
          (filter (fun s -> s<>"") (p0::s0::[])) ^ "]\n" ^
      "{}\n" ^
      "[" ^ list2string (fun s -> s) "*"
          (filter (fun s -> s<>"") (p0'::s0'::[])) ^ "]"
(*end pretty printing entailments*)

let num_purelits = function
  | Entailment(Assertion(p, s), Assertion(p', s')) ->
      List.length p + List.length p'

let num_spacelits = function
  | Entailment(Assertion(p, s), Assertion(p', s')) ->
      List.length s + List.length s'

let can_exp2expr : can_exp -> expr = function
  | Ce_num(i) ->
      if i=0 then Nil else Var(i)
  | Ce_ident(id) ->
      let s = id_name id in
      assert (String.length s > 0);
      Var (int_of_string (String.sub s 1 (String.length s - 1)))
  | Ce_xor(_,_) -> fprintf stdout "Warning: xor expr conversion failed\n"; Nil

let can_atom2pn_atom : can_atom -> pn_atom = function
  | EQ(e1, e2) -> Equ(can_exp2expr e1, can_exp2expr e2)
  | NEQ(e1, e2) -> Nequ(can_exp2expr e1, can_exp2expr e2)

let can_spred2space_atom : can_spred -> space_atom = function
  | Csp_listseg(lk, c, e1, e2, _, _, _) -> Lseg(can_exp2expr e1, can_exp2expr e2)
  | Csp_pointsto(e1, (_, e2)::l) ->  Next(can_exp2expr e1, can_exp2expr e2)
  | Csp_pointsto(e1, []) -> fprintf stdout "Warning: unhandled pointsto []\n"; Next(Nil, Nil)
  | Csp_tree(_, _, _) -> fprintf stdout "Warning: unhandled tree\n"; Next(Nil, Nil)
  | Csp_indpred(_, _, _) -> fprintf stdout "Warning: unhandled indpred\n"; Next(Nil, Nil)

let can_form2form = function
  | (al , spl) ->
      let pures = List.map can_atom2pn_atom al in
      let spaces = List.map can_spred2space_atom spl in
      (pures, spaces)

let (++) = List.append

let rec can_prop2prop = function
  | Cp_base(f) -> can_form2form f
  | Cp_star(p1, p2) ->
      let (pl, sl) = can_prop2prop p1 in
      let (pl', sl') = can_prop2prop p2 in
      (pl ++ pl', sl ++ sl')
  | _ -> fprintf stdout "Warning: prop conversion failed\n"; ([], [])

let can_entailment2entailment : can_entailment -> entailment = function
  | (p, cmd, q, _, _) ->
      match can_prop2prop p , can_prop2prop q with
      | (pl, sl) , (pl', sl') ->
          (Entailment(Assertion(pl, sl),
                      Assertion(pl', sl')))

let check (ent : entailment) : bool option =
  match check_entailment ent with
  | (VeriStar.Valid) -> Some true
  | (VeriStar.C_example(_)) -> Some false
  | (VeriStar.Aborted(_)) -> None

let driver (cent : can_entailment) : bool option =
  let ent = can_entailment2entailment cent in
  fprintf stdout "#pure literals = %d, #space literals = %d\n%s\n"
    (num_purelits ent) (num_spacelits ent) (entailment2string 0 ent);
  flush_all ();
      check ent





