Require Import veric.base.

Structure external_specification {M E Z:Type} :=
  { ext_spec_type : E -> Type
  ; ext_spec_pre : forall (e:E),
      ext_spec_type e -> list typ -> list val -> Z -> M -> Prop
  ; ext_spec_post : forall (e:E), 
      ext_spec_type e -> list typ -> list val -> Z -> M ->  Prop
  ; ext_spec_evolve : Z -> Z -> Prop
  }.
Implicit Arguments external_specification [ ].

Definition ext_spec := external_specification mem external_function.
