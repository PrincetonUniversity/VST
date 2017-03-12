
Definition size_is (n: Z) : Prop := False.

Lemma assert_size_is_Type (n: Z) :
  forall (A: Type), size_is n -> A.
Proof.
intros. elimtype False; apply H.
Qed.

Lemma assert_size_is_Prop (n: Z) :
  forall (A: Prop), size_is n -> A.
Proof.
intros. elimtype False; apply H.
Qed.

Opaque size_is.


Ltac composite i :=
  match i with
  | _ _ => idtac
  | (fun _ => _) => idtac
  end.

Ltac primary i := try (composite i; fail 1).

Ltac count_one :=
match goal with
|  H := ?t |- _ =>
     primary t;
     clear H
| H := fun x : ?t => _ |- size_is ?n  =>
        let y := fresh "y" in
         assert (y:t) by admit;
         let H1 := fresh in pose (H1 := H y);
          unfold H in H1; clear H;
       change (size_is (Z.succ n)); compute
|  H := ?t1 ?t2 |- size_is ?n =>
      first [ primary t2;
              let H1 := fresh in pose (H1:=t1);
               first [clear H | clearbody H];
               change (size_is (Z.succ n)); compute
             | primary t1;
              let H2 := fresh in pose (H2:=t2);
               first [clear H | clearbody H];
               change (size_is (Z.succ n)); compute
             | composite t1;
              let H1 := fresh in pose (H1:=t1);
              change (t1 t2) with (H1 t2) in H
             | composite t2;
               let H2 := fresh in pose (H2 := t2);
               first [clear H | clearbody H];
               change (size_is (Z.succ n)); compute
             | first [clear H | clearbody H];
               change (size_is (Z.succ n)); compute
              ]
end.

Ltac goal_size :=
match goal with |- ?A =>
  let H := fresh in set (H:=A);
  first [apply (assert_size_is_Type 0) | apply (assert_size_is_Prop 0)];
  repeat count_one
end.