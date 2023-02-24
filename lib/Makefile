# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

ifneq ($(MAKECMDGOALS),run-clightgen)
ifneq ($(MAKECMDGOALS),clean)
CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -docroot VSTlib -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)
endif
endif
####################################################################
##                      Your targets here                         ##
####################################################################

run-clightgen: proof/math_extern.v proof/malloc_extern.v proof/SC_atomics_extern.v

include CoqMakefile.local

clean:
	rm -f CoqMakefile CoqMakefile.conf
	rm -f proof/{*.vo,*.vos,*.vok,*.glob} 
	rm -f proof/{math_extern.v,malloc_extern.v,SC_atomics_extern.v}
	rm -f test/{*.vo,*.vos,*.vok,*.glob} 
	rm -f test/{incr.v,incr_main.v,testmath.v}

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
