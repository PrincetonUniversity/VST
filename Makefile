target: progs/verif_reverse.vo

msl/msl_standard.vo:
	(cd msl; make $*)

compcert/Clight_sem.vo:
	(cd compcert; ./make $*)

sepcomp/step_lemmas.vo: compcert/Clight_sem.vo 
	(cd sepcomp; make  $*)

veric/SequentialClight.vo: compcert/Clight_sem.vo msl/msl_standard.vo \
            sepcomp/step_lemmas.vo
	(cd veric; make $*)

floyd/proofauto.vo: veric/SequentialClight.vo
	(cd floyd; make $*)

progs/verif_reverse.vo: floyd/proofauto.vo
	(cd progs; make $*)

clean: 
	(cd msl; make clean); (cd compcert; ./make clean); \
        (cd sepcomp; make clean); (cd veric; make clean); \
        (cd floyd; make clean); (cd progs; make clean)
