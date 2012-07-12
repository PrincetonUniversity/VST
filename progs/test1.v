(* 
#include <stddef.h>

struct list {int h; struct list *t;};

struct list three[] = {
    {1, three+1}, {2, three+2}, {3, NULL}
};

int sumlist (struct list *p) {
  int s = 0;
  struct list *t = p;
  int h;
  while (t) {
     h = t->h;
     t = t->t;
     s = s + h;
  }
  return s;
}

struct list *reverse (struct list *p) {
  struct list *w, *t, *v;
  w = NULL; 
  v = p;
  while (v) {
    t = v->t;
    v->t = w;
    w = v;
    v = t;
  }
  return w;
}  

int main (void) {
  struct list *r; int s;
  r = reverse(three);
  s = sumlist(r);
  return s;
}
*)
Require Import veric.base.
Require Import compcert.Maps.

Section idents.
Local Open Scope positive_scope.
Definition i_s : ident := 1.
Definition i_h : ident := 2.
Definition i_t : ident := 3.
Definition i_list : ident := 4.
Definition i_sumlist : ident := 5.
Definition i_p : ident := 6.
Definition i_three : ident := 7.
Definition i_reverse : ident := 8.
Definition i_w : ident := 9.
Definition i_v : ident := 10.
Definition i_main : ident := 11.
Definition i_r : ident := 12.
End idents.

Definition t_int := Tint I32 Signed noattr.

Definition t_list :=   Tstruct i_list (Fcons i_h t_int
               (Fcons i_t (Tcomp_ptr i_list noattr)
               Fnil)) noattr.

Definition t_listptr := Tpointer t_list noattr.

Definition set: forall {A}, ident -> A -> PTree.t A -> PTree.t A := 
 @PTree.set.
Implicit Arguments set [A].

Definition zet {A} (i: Z) (x: A) (m: ZMap.t (option A)) : ZMap.t (option A) := 
 ZMap.set i (Some x) m.
Implicit Arguments zet [A].

Definition f_sumlist : fundef :=
 Internal (mkfunction
 (* return *) t_int
 (* params *) ((i_p, t_listptr)::nil)
 (* vars *)  nil
 (* temps *) ((i_s,t_int)::(i_t,t_listptr)::(i_h,t_int)::nil)
 (* body *) 
  (Ssequence (Sset i_s (Econst_int (Int.repr 0) t_int))
   (Ssequence (Sset i_t (Etempvar i_p t_listptr))
    (Ssequence (Sset i_h (Econst_int (Int.repr 0) t_int))
     (Ssequence 
         (Swhile (Etempvar i_t t_listptr)
          (Ssequence (Sset i_h (Efield (Ederef (Etempvar i_t t_listptr) t_list) i_h t_int))
           (Ssequence (Sset i_t (Efield (Ederef (Etempvar i_t t_listptr) t_list) i_t t_listptr))
            (Sset i_s (Ebinop Oadd (Etempvar i_s t_int) (Etempvar i_h t_int) t_int)))))
   (Sreturn (Some (Etempvar i_s t_int)))))))).

Definition f_reverse: fundef :=
 Internal (mkfunction
 (* return *) t_listptr
 (* params *) ((i_p, t_listptr)::nil)
 (* vars *)  nil
 (* temps *) ((i_w,t_listptr)::(i_t,t_listptr)::(i_v,t_listptr)::nil)
 (* body *) 
  (Ssequence (Sset i_w (Econst_int (Int.repr 0) t_int))
   (Ssequence (Sset i_v (Etempvar i_p t_listptr))
    (Ssequence (Sset i_t (Econst_int (Int.repr 0) t_int))
     (Ssequence 
         (Swhile (Etempvar i_v t_listptr)
          (Ssequence (Sset i_t (Efield (Ederef (Etempvar i_v t_listptr) t_list) i_t t_listptr))
           (Ssequence (Sassign (Efield (Ederef (Etempvar i_v t_listptr) t_list) i_t t_listptr) (Etempvar i_w t_listptr))
           (Ssequence (Sset i_w (Etempvar i_v t_listptr))
            (Sset i_v (Etempvar i_t t_listptr))))))
   (Sreturn (Some (Etempvar i_w t_listptr)))))))).

Definition f_main: fundef :=
 Internal (mkfunction
 (* return *) t_int
 (* params *) nil
 (* vars *)  nil
 (* temps *)  ((i_r, t_listptr)::(i_s, t_int)::nil) 
 (* body *) 
  (Ssequence (Scall (Some i_r) (Evar i_reverse (Tfunction (Tcons t_listptr Tnil) t_listptr)) (Evar i_three t_listptr :: nil))
    (Ssequence (Scall (Some i_s) (Evar i_sumlist (Tfunction (Tcons t_listptr Tnil) t_int)) (Etempvar i_r t_listptr::nil)) 
     (Sreturn (Some (Etempvar i_s t_int)))))).

Definition b_three : block := 1.
Definition b_sumlist : block := -1.
Definition b_reverse : block := -2.
Definition b_main    : block := -3.

Definition g_symb : PTree.t block :=
 set i_three b_three
  (set i_sumlist b_sumlist
   (set i_reverse b_reverse
    (set i_main b_main
      (PTree.empty block)))).

Definition g_funs: ZMap.t (option fundef) :=
 zet b_sumlist f_sumlist
 (zet b_reverse f_reverse 
  (zet b_main f_main
   (ZMap.init None))).

Parameter gv_three : globvar type.

Definition g_vars: ZMap.t (option (globvar type)) :=
 zet b_three gv_three 
   (ZMap.init None).

Definition g_nextfun : block := -4.
Definition g_nextvar : block := 2.

Definition prog : Genv.t fundef type.
 refine (@Genv.mkgenv _ _ g_symb g_funs g_vars g_nextfun g_nextvar
               _ _ _ _ _ _).
unfold g_nextfun; omega.
unfold g_nextvar; omega.
unfold g_nextfun, g_nextvar, g_symb, set; intros.
repeat rewrite PTree.gsspec in H.
repeat if_tac in H; 
try rewrite PTree.gempty in H;
inv H; try match goal with |- ?A <> _ /\ _  =>
          unfold A
         end; split; try omega; congruence.
unfold g_funs, zet,  g_nextfun; intros.
repeat rewrite ZMap.gsspec in H.
repeat if_tac in H; 
try rewrite ZMap.gi in H;
inv H; try match goal with |- _ < ?A < _ =>
          unfold A
         end; omega.
unfold g_vars, zet,  g_nextvar; intros.
repeat rewrite ZMap.gsspec in H.
repeat if_tac in H; 
try rewrite ZMap.gi in H;
inv H; try match goal with |- _ < ?A < _ =>
          unfold A
         end; omega.
unfold g_symb, set; intros.
repeat rewrite PTree.gsspec in H,H0.
unfold i_three, i_sumlist, i_reverse, i_main in *.
repeat if_tac in H; 
try (rewrite PTree.gempty in H; inv H);
repeat if_tac in H0; 
try (rewrite PTree.gempty in H0; inv H0);
inv H; inv H0; try congruence.
Defined.



