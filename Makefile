target: veric/SeparationLogicSoundness.vo

msl/msl_standard.vo:
	(cd msl; make)

compcert/Clight_sem.vo:
	(cd compcert; ./make)

compositional_compcert/step_lemmas.vo: compcert/Clight_sem.vo 
	(cd compositional_compcert; make )

veric/SequentialClight.vo: compcert/Clight_sem.vo msl/msl_standard.vo \
            compositional_compcert/step_lemmas.vo
	(cd veric; make)

floyd/proofauto.vo: veric/SequentialClight.vo
	(cd floyd; make)

progs/reverse.vo: floyd/proofauto.vo
	(cd progs; make)
