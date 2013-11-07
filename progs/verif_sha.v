Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.


Lemma liftSEPlift1:
 forall (R:  mpred) f, 
     `(SEP (`R)) f = `R.
Proof. intros. 
unfold SEPx. 
 super_unfold_lift.
extensionality rho.
simpl. rewrite sepcon_emp.
auto.
Qed.

Lemma body_SHA256_Update: semax_body Vprog Gtot f_SHA256_Update SHA256_Update_spec.
Proof.
start_function.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment _fragment.
forward.  (* data=data_; *)
forward.
instantiate (1:= (len,a,c)) in (Value of witness).
entailer!.
cbv beta iota.
rewrite liftSEPlift1.
unfold sha256state_.
normalize. intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
simpl_typed_mapsto.
unfold fst,snd.
normalize.
unfold s256_relate in H0.
unfold addlength_rel in H0.
destruct a.
change 16 with LBLOCK in H0.
simpl in H0.
unfold s256_Nh,s256_Nl, s256_num, s256_data in H0.
unfold fst,snd in H0.
destruct H0 as [? [? [? [? [? ?]]]]].
destruct H4 as [n' H4].
forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer.
(*

	if (n != 0)	{
                fragment = SHA_CBLOCK-n;
		if (len >= fragment)  {
			memcpy (p+n,data,fragment);
			sha256_block_data_order (c,p);
			data  += fragment;
			len   -= fragment;
			memset (p,0,SHA_CBLOCK);	/* keep it zeroed */
		}
		else  {
			memcpy (p+n,data,len);
			c->num = n+(unsigned int)len;
			return;
		}
	}
*)