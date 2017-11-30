(* THE PURPOSE of this utility is to calibrate the speed of
 compiled ocaml code on the current processor, for comparing
 build-timings of VST components *)

type ('a, 'b) prod =
| Pair of 'a * 'b



type key = int

type 'v tree =
| E
| T of 'v tree * key * 'v * 'v tree

(** val empty_tree : 'a1 tree **)

let empty_tree =
  E

(** val lookup : 'a1 -> key -> 'a1 tree -> 'a1 **)

let rec lookup default x = function
| E -> default
| T (tl, k, v, tr) ->
  if (<) x k
  then lookup default x tl
  else if (<) k x then lookup default x tr else v

(** val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let rec insert x v = function
| E -> T (E, x, v, E)
| T (a, y, v', b) ->
  if (<) x y
  then T ((insert x v a), y, v', b)
  else if (<) y x then T (a, y, v', (insert x v b)) else T (a, x, v, b)

(** val elements' :
    'a1 tree -> (key, 'a1) prod list -> (key, 'a1) prod list **)

let rec elements' s base =
  match s with
  | E -> base
  | T (a, k, v, b) -> elements' a ((Pair (k, v))::(elements' b base))

(** val elements : 'a1 tree -> (key, 'a1) prod list **)

let elements s =
  elements' s []

let test (f: int -> int) (n: int) =
 let rec build (j, t) = if j=0 then t
                    else build(j-1, insert (f j) 1 t)
  in let t1 = build(n,empty_tree)
  in let rec g (j,count) = if j=0 then count
                       else if lookup 0 (f j) t1 = 1
                            then g(j-1,count+1)
                            else g(j-1,count)
  in let start = Sys.time()
  in let answer = g(n,0)
      in (answer, Sys.time() -. start)

let run_tests() = test (fun _ -> Random.int  1000000) 5000000

let a = run_tests ()
		  
	    
