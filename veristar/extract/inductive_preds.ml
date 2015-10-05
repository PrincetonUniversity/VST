open Misc
open Symbtree

type ip_description =
    {id: string; id_arg: ident list; cmp_arg: string list;
     guard: can_atom; newids: ident list; body: can_spred list}

(**** pretty printing ****)
open Format

let pp_string f s = fprintf f "%s" s

let rec pp_listsep pp s1 s2 f = function
  | [] -> fprintf f "%s" s2
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s %a" pp x s1 (pp_listsep pp s1 s2) l

let pp_idlist = pp_listsep pp_string "" ","

let pp_ip_description f = function
  | {id=p; id_arg=ia; cmp_arg=ca; guard=g; newids=ni; body=b} ->
      fprintf f "%s(%a;%a) = " p pp_idlist (List.map string_of_ident ia) pp_idlist ca;
      fprintf f "@[<2>if %a@ @[<2>then empty@]@ else E(%a). %a@]"
	pp_can_atom g pp_idlist (List.map string_of_ident ni) (pp_listsep pp_can_spred " * " ".") b

(**** environment of inductive definitions ****)
let ip_env = ref ([] : ip_description list)

let pp_ip_environment f =
  List.iter (fun ip -> pp_ip_description f ip; Format.pp_print_newline f ()) !ip_env

let add_ip_description ip = ip_env := ip :: !ip_env

let lookup_ip id = List.find (function ipd -> ipd.id=id) !ip_env

let instance_ip (id,el,cl) =
  let ip = lookup_ip id
  in let (f_i,f_i',il') =
      let iil = List.combine ip.id_arg el
      and iil' = List.map (fun i -> (i, Ce_ident (gensym i))) ip.newids
      in let f b i = List.assoc i (if b then iil else iil' @ iil)
      in (f true, f false, List.map snd iil')
     and f_c =
      let ccl = List.combine ip.cmp_arg cl
      in fun c -> List.assoc c ccl in
  let sub = mk_subst f_i f_c
  and sub' = mk_subst f_i' f_c
  in let (ca,vl,spl) = (sub_can_atom sub ip.guard, il', List.map (sub_can_spred sub') ip.body)
  in (* fprintf !Config.formatter "INDPRED INSTANCE (%a,%a,%a)@."
	pp_can_atom ca (pp_listsep pp_can_exp " * " ".") vl pp_spatial_list spl; *)
    (ca,vl,spl)
	
let _ =
  let list = "list"
  and x = create_ident "x"
  and y = create_ident "y"
  and tl = "tl" in
  let ex = Ce_ident x
  and ey = Ce_ident y in
  let list_ip =
    {id = list; id_arg = [x]; cmp_arg = [tl];
     guard = mk_EQ(ex, Ce_num 0);
     newids = [y];
     body = [Csp_pointsto (ex, [(tl,ey)]);
	     Csp_indpred (list,[ey],[tl])]}
  in add_ip_description list_ip

(* let _ = pp_ip_environment !Config.formatter *)
