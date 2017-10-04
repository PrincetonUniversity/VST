Require Import ZArith.

Arguments Z.double _ : simpl never.
Arguments Z.succ_double _ : simpl never.
Arguments Z.pred_double _ : simpl never.
Arguments Z.pos_sub _ _ : simpl never.
Arguments Z.add _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.succ _ : simpl never.
Arguments Z.pred _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.square _ : simpl never.
Arguments Z.compare _ _ : simpl never.
Arguments Z.sgn _ : simpl never.
Arguments Z.leb _ _ : simpl never.
Arguments Z.ltb _ _ : simpl never.
Arguments Z.geb _ _ : simpl never.
Arguments Z.gtb _ _ : simpl never.
Arguments Z.eqb _ _ : simpl never.
Arguments Z.max _ _ : simpl never.
Arguments Z.min _ _ : simpl never.
Arguments Z.abs _ : simpl never.
Arguments Z.abs_nat _ : simpl never.
Arguments Z.abs_N _ : simpl never.
Arguments Z.to_nat _ : simpl never.
Arguments Z.to_N _ : simpl never.
(* Beware: If we do this one, "omega" on nat fails
Arguments Z.of_nat _ : simpl never. *)
Arguments Z.of_N _ : simpl never.
Arguments Z.to_pos _ : simpl never.
Arguments Z.iter _ _ _ _ : simpl never.
Arguments Z.pos_div_eucl _ _ : simpl never.
Arguments Z.div_eucl _ _ : simpl never.
Arguments Z.div _ _ : simpl never.
Arguments Z.modulo _ _ : simpl never.
Arguments Z.quotrem _ _ : simpl never.
Arguments Z.quot _ _ : simpl never.
Arguments Z.rem _ _ : simpl never.
Arguments Z.even _ : simpl never.
Arguments Z.odd _ : simpl never.
Arguments Z.div2 _ : simpl never.
Arguments Z.quot2 _ : simpl never.
Arguments Z.log2 _ : simpl never.
Arguments Z.sqrtrem _ : simpl never.
Arguments Z.sqrt _ : simpl never.
Arguments Z.gcd _ _ : simpl never.
Arguments Z.ggcd _ _ : simpl never.
Arguments Z.testbit _ _ : simpl never.
Arguments Z.shiftl _ _ : simpl never.
Arguments Z.shiftr _ _ : simpl never.
Arguments Z.lor _ _ : simpl never.
Arguments Z.land _ _ : simpl never.
Arguments Z.ldiff _ _ : simpl never.
Arguments Z.lxor _ _ : simpl never.
Arguments Z.eq _ _ : simpl never.
Arguments Z.lt _ _ : simpl never.
Arguments Z.gt _ _ : simpl never.
Arguments Z.le _ _ : simpl never.
Arguments Z.ge _ _ : simpl never.
Arguments Z.divide _ _ : simpl never.
Arguments Z.Even _ : simpl never.
Arguments Z.Odd _ : simpl never.
Arguments Z.eq_dec _ _ : simpl never.
