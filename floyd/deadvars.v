Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Import ListNotations.

(* In any of these functions, whenever there is a [list ident],
  we assume it is unsorted without duplicates. *)

(* Take the union of two lists *)
Fixpoint deadvars_union (al bl: list ident) : list ident :=
 match al with
 | a::al' => let cl := deadvars_union al' bl in
                   if id_in_list a bl then cl else a::cl
 | nil => bl
 end.
(* Take the intersection of two lists *)
Fixpoint deadvars_intersection (al bl: list ident) : list ident :=
 match al with
 | a::al' => if id_in_list a bl 
                then a :: deadvars_intersection al' bl 
                else deadvars_intersection al' bl 
 | nil => nil
 end.

(* Assume [vl,live] are disjoint.  If [i] is present in [vl], move it to [live] *)
Fixpoint deadvars_remove1 i vl live :=
 match vl with
 | j::vl' => if Pos.eqb i j 
             then (vl', i::live)
             else let (vl2, live2) := deadvars_remove1 i vl' live
                     in (j::vl2, live2)
 | nil => (nil, live)
 end.

(* Whenever  (vl',live')=deadvars_remove e vl live,   that means
    disjoint [vl,live],   disjoint [vl',live'],   [vl U live]=[vl' U live'],
    and vl' is the maximal subset of vl that contains no tempvar of e *)
Fixpoint deadvars_remove (e: expr) (vl live: list ident) : list ident * list ident :=
 match e with
 | Etempvar i _ => deadvars_remove1 i vl live
 | Ederef e1 _ => deadvars_remove e1 vl live
 | Eaddrof e1 _ => deadvars_remove e1 vl live
 | Eunop _ e1 _ => deadvars_remove e1 vl live 
 | Ebinop _ e1 e2 _ => let (vl', live') := deadvars_remove e1 vl live 
                                    in deadvars_remove e2 vl' live'
 | Ecast e1 _ => deadvars_remove e1 vl live
 | Efield e1 _ _ => deadvars_remove e1 vl live
 | _ => (vl, live)
 end.

(* Whenever  (vl',live')=deadvars_removel e vl live,   that means
    disjoint [vl,live],   disjoint [vl',live'],   [vl U live]=[vl' U live'],
    and vl' is the maximal subset of vl that contains no tempvar of el *)
Fixpoint deadvars_removel (el: list expr) (vl live: list ident) : list ident * list ident :=
  match el with
  | nil => (vl , live)
  | e::el' => let (vl', live') := deadvars_remove e vl live
                   in deadvars_removel el' vl' live'
  end.

Fixpoint deadvars_dead (i: ident) (vl: list ident) : list ident * list ident :=
 match vl with
 | j::vl' => if Pos.eqb i j 
             then ([i],vl')
             else let (k,vl'') := deadvars_dead i vl' in (k,j::vl')
 | nil => (nil, nil)
 end.

(* (vl',live')=deadvars_delete al vl live,   that means
    disjoint [vl,live],   disjoint [vl',live'],   [vl U live]=[vl' U live'],
    and vl' is the maximal subset of vl that contains no element of al *)
Fixpoint deadvars_delete (al vl live: list ident) : list ident * list ident :=
 match al with
 | a::al' => let (vl',live') := deadvars_delete al' vl live
                   in deadvars_remove1 a vl' live'
 | nil => (vl,live)
 end.

Fixpoint nobreaks (s: statement) : bool :=
match s with
| Sbreak => false
| Scontinue => false
| Ssequence c1 c2 => nobreaks c1 && nobreaks c2
| Sloop c1 c2 => nobreaks c1 && nobreaks c2
| Sifthenelse _ c1 c2 => nobreaks c1 && nobreaks c2
| _ => true
end.

(* (live'',dead'') = deadvars_stmt vl live dead c (fun vl' live' dead' => B) (bcont)    means,
   Let ubd = the variables of vl, used-before-defined in c
   Let def = variables of vl, defined-before-used in c
   Let vl = ubd U def U vl'
   That is, ubd we know for sure are live before c, 
     def we know for sure are dead,
     and vl' we need to keep investigating the commands after c.
   Finally, live' = ubd U live,      dead' = def U dead
     and we continue the flow analysis with B, or for break statements we continue with bcont.
   What's returned is a pair (live'',dead'') such that live'' U dead'' = vl.  *)
Fixpoint deadvars_stmt (vl: list ident) (live dead: list ident) (c: statement) 
                   (cont bcont: list ident -> list ident -> list ident -> list ident * list ident) : list ident * list ident :=
  match vl with nil => (live,dead) | _ =>
   match c with
   | Sskip => cont vl live dead
   | Sassign e1 e2 => let (vl',live') := deadvars_removel [e1;e2] vl live in
                         cont vl' live' dead
   | Sset i e => let (vl',live') := deadvars_remove e vl live in
                     let (d,vl'') := deadvars_dead i vl' in
                      cont vl'' live' (d++dead)
   | Scall i e el => let (vl',live') := deadvars_removel (e::el) vl live in
                      let (d,vl'') := match i with
                                      | Some i' => deadvars_dead i' vl'
                                      | None => (nil,vl')
                                      end
                      in cont vl'' live' (d++dead)
   | Sbuiltin i ef tl el =>
                     let (vl',live') := deadvars_removel el vl live in
                      let (d,vl'') := match i with
                                      | Some i' => deadvars_dead i' vl'
                                      | None => (nil,vl')
                                      end
                      in cont vl'' live' (d++dead)
   | Ssequence c1 c2 =>
          deadvars_stmt vl live dead c1 (fun vl' live' dead' => 
             deadvars_stmt vl' live' dead' c2 cont bcont) bcont
   | Sreturn None => (nil, vl++dead)
   | Sreturn (Some e) => let (vl',live') := deadvars_removel [e] vl live
                          in (live', vl' ++ dead)
   | Sifthenelse e c1 c2 =>
      if nobreaks c1 && nobreaks c2
      then
           let (vl', live')  := deadvars_removel [e] vl live in
            let (live1,dead1) := deadvars_stmt vl' nil dead c1 (fun _ l d => (l,d)) bcont in
            let (live2,dead2) := deadvars_stmt vl' nil dead c2 (fun _ l d => (l,d)) bcont in
            let live'' := deadvars_union live1 live2 in
            let dead'' := deadvars_intersection dead1 dead2 in
            let (vl'',live3) := deadvars_delete live'' vl' live' in
            let (vl3, _) := deadvars_delete dead'' vl'' nil in
            cont vl3 live3 dead''
     else
           let (vl', live')  := deadvars_removel [e] vl live in
            let (live1,dead1) := deadvars_stmt vl' live' dead c1 cont bcont in
            let (live2,dead2) := deadvars_stmt vl' live' dead c2 cont bcont in
            let live'' := deadvars_union live1 live2 in
            let dead'' := deadvars_intersection dead1 dead2 in
            (live'',dead'')           
   | Sbreak => bcont vl live dead
   | Sloop c1 c2 =>
                             (* on the next line, using  vlx++deadx  instead of just deadx  is rather aggressive; is it sound?  *)
            let cont0 := fun vlx livex deadx => (livex,vlx++deadx) in
            let cont1 := fun vl' live' dead' => deadvars_stmt vl' live' dead' c2 cont0 cont
            in deadvars_stmt vl live dead c1 cont1 cont
   | _ => (live,dead)
   end
  end.

Fixpoint temps_of_localdefs (dl: list localdef) : list ident :=
 match dl with
 | nil => nil
 | temp i _ :: dl' => i :: temps_of_localdefs dl'
 | _ :: dl' => temps_of_localdefs dl'
 end.

(*  (live',dead') = deadvars_post post vl live dead.
  The forward flow analysis has reached a postcondition whose LOCALS clause contains
   exactly the tempvars in [post], and by this time in the forward flow analysis we have
   classified our starting variables into three disjoint lists:
     live: definitely live
     dead: definitely dead
     vl:  not yet sure.
   So now we know that the intersection of (vl, post) are all definitely live,
    and the rest of vl are definitely dead, so we can construct 
      live' = (vl intersect post) ++ live
      dead' = (vl - post) ++ dead' *)
Fixpoint deadvars_post (post: list ident) (vl: list ident) (live dead: list ident) : list ident * list ident :=
 match post with
 | nil => (nil, vl++dead)
 | i :: post' => let (vl',live') := deadvars_remove1 i vl live in
                             deadvars_post post' vl' live' dead
 end.

Ltac inhabited_value T :=
 match T with
 | nat => constr:(O)
 | Z => constr:(0%Z)
 | list ?A => constr:(@nil A)
 | positive => xH
 | bool => false
 | prod ?A ?B => let x := inhabited_value A in
                           let y := inhabited_value B in
                               constr:(pair x y)
 | _ => match goal with x:T |- _ => x | x := _ : T |- _ => x end
 end.

Fixpoint expr_temps (e: expr) (vl: list ident) : list ident :=
 match e with
 | Etempvar i _ => if id_in_list i vl then vl else i::vl
 | Ederef e1 _ => expr_temps e1 vl
 | Eaddrof e1 _ => expr_temps e1 vl
 | Eunop _ e1 _ => expr_temps e1 vl
 | Ebinop _ e1 e2 _ => expr_temps e2 (expr_temps e1 vl)
 | Ecast e1 _ => expr_temps e1 vl
 | Efield e1 _ _ => expr_temps e1 vl
 | _ => vl
 end.

Ltac locals_of_assert P :=
 match P with
 | (PROPx _ (LOCALx ?Q _)) => constr:(temps_of_localdefs Q)
 | emp => constr:(@nil ident)
 | andp ?A ?B => let a := locals_of_assert A in
                  let b := locals_of_assert B in
                  constr:(a++b)
 | stackframe_of _ => constr:(@nil ident)
 | local (liftx (eq _) (eval_expr ?E)) =>
            let vl := constr:(expr_temps E nil) in vl
 | @exp _ _ ?T ?F =>
    let x := inhabited_value T in
     let d := constr:(F x) in
      let d := eval cbv beta in d in 
       let d := locals_of_assert d in
           d
 end.

Ltac locals_of_ret_assert Post :=
 match Post with
 | @abbreviate ret_assert ?P => locals_of_ret_assert P
 | normal_ret_assert ?P => let a := locals_of_assert P in
                                          constr:(pair a (@nil ident))
 | loop1_ret_assert ?P ?R => let a := locals_of_assert P in 
                                            let b := locals_of_ret_assert R in
                                               constr:(pair a (fst b))
 | loop2_ret_assert ?P _ => let a := locals_of_assert P in
                                          constr:(pair a (@nil ident))
 | function_body_ret_assert _ _ => constr:(pair (@nil ident) (@nil ident))
 | overridePost ?P ?R => let b := locals_of_ret_assert R in
                                      let a := locals_of_assert P in
                                         constr:(pair a (snd b))
 | frame_ret_assert ?A ?B =>
     let vlA :=  locals_of_ret_assert A
      in let vlB := locals_of_assert B
       in let vl := constr:(pair (fst vlA ++ vlB) (snd vlA ++ vlB))
        in vl
 end.

Ltac find_dead_vars P c Q :=
     let vl := locals_of_assert P in 
     let post := locals_of_ret_assert Q in
     let post := eval compute in post in
     let d := constr:(snd (deadvars_stmt vl nil nil c 
                                     (deadvars_post (fst post)) 
                                     (deadvars_post (snd post)))) in
      let d := eval compute in d in
      d.

Ltac deadvars := 
 match goal with
 | X := @abbreviate ret_assert ?Q |-
    semax _ ?P ?c ?Y =>
    constr_eq X Y;
    match find_dead_vars P c Q with
    | nil => idtac
    | ?d =>  idtac "Dropping dead vars!"; drop_LOCALs d
     end + fail 99 "deadvars failed for an unknown reason"
 | |- semax _ _ _ _ => 
       fail "deadvars: Postcondition must be an abbreviated local definition (POSTCONDITION); try abbreviate_semax first"
 | |- _ |-- _ => idtac
 | |- _ => fail "deadvars: the proof goal should be a semax"
 end.

Tactic Notation "deadvars" "!" :=
 match goal with
 | X := @abbreviate ret_assert ?Q |-
    semax _ ?P ?c ?Y =>
    constr_eq X Y;
    match find_dead_vars P c Q with
    | nil => fail 2 "deadvars!: Did not find any dead variables"
    | ?d =>  drop_LOCALs d
     end
 | |- semax _ _ _ _ => 
       fail 1 "deadvars!: Postcondition must be an abbreviated local definition (POSTCONDITION); try abbreviate_semax first"
 | |- _ => fail 1 "deadvars!: the proof goal should be a semax"
 end.

