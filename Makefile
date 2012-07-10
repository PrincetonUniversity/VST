target: veric/SeparationLogicSoundness.vo

msl/msl_standard.vo:
	(cd msl; make depend; make)

compcert/Clight_sem.vo:
	(cd compcert; make depend; make)

veric/SeparationLogicSoundness.vo: compcert/Clight_sem.vo msl/msl_standard.vo
	(cd veric; make depend; make)
