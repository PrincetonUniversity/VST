HFILES = pile.h pile_private.h onepile.h apile.h triang.h stdlib.h \
         fast/fastpile_private.h
CFILES = pile.c onepile.c apile.c triang.c main.c stdlib.c \
         fast/fastpile.c fast/fastapile.c
VFILES = linking.v spec_stdlib.v verif_stdlib.v spec_pile.v verif_pile.v \
         spec_onepile.v verif_onepile.v spec_apile.v verif_apile.v \
         spec_triang.v verif_triang.v spec_main.v verif_main.v \
         link_pile.v \
         fast/spec_fastpile.v fast/verif_fastpile.v \
         fast/spec_fastpile_concrete.v fast/verif_fastpile_concrete.v \
         fast/subsume_fastpile.v \
         fast/spec_fastapile.v fast/verif_fastapile.v \
         fast/spec_fastmain.v fast/verif_fastmain.v \
         fast/link_fastpile.v

CC=ccomp
CFLAGS=-O

-include CONFIGURE
VST_LOC ?= ../..

ifdef COMPCERT_LOC
CLIGHTGEN ?= $(COMPCERT_LOC)/clightgen
endif 

ifdef CLIGHTGEN
VERSION1= $(lastword $(shell $(CLIGHTGEN) --version))
VERSION2= $(subst version=,,$(shell grep version ../../compcert/VERSION))
ifneq ($(VERSION1),$(VERSION2))
$(warning clightgen version $(VERSION1) does not match VST/compcert/VERSION $(VERSION2))
endif
endif


CVFILES = $(patsubst %.c,%.v,$(CFILES))
OFILES = $(patsubst %.c,%.o,$(CFILES))
VOFILES = $(patsubst %.v,%.vo,$(CVFILES) $(VFILES))


VST_DIRS= msl sepcomp veric floyd
VSTFLAGS= -R $(VST_LOC)/compcert compcert $(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d)) -R . pile


target: _CoqProject $(VOFILES) incr/verif_incr.vo

cvfiles: $(CVFILES)

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

ifdef CLIGHTGEN
$(CVFILES): $(CFILES) $(HFILES)
	$(CLIGHTGEN) -normalize $(CFILES)

incr/incr.v: incr/incr.c
	$(CLIGHTGEN) -normalize $<
endif

incr/verif_incr.vo: incr/verif_incr.v incr/incr.vo

_CoqProject: Makefile
	@echo $(VSTFLAGS) > _CoqProject

clean:
	rm -f {./,*/}{*.vo,*.o,.*.aux,*.glob}

# .depend depend:
# 	coqdep $(VSTFLAGS) *.v >.depend

spec_apile.vo: apile.vo spec_stdlib.vo spec_pile.vo
spec_main.vo: main.vo spec_stdlib.vo spec_onepile.vo spec_apile.vo spec_triang.vo
spec_onepile.vo: onepile.vo spec_stdlib.vo spec_pile.vo
spec_pile.vo: pile.vo spec_stdlib.vo
spec_stdlib.vo: stdlib.vo
spec_triang.vo: triang.vo spec_stdlib.vo spec_pile.vo
verif_apile.vo: linking.vo apile.vo spec_stdlib.vo spec_pile.vo spec_apile.vo
verif_main.vo: linking.vo main.vo spec_stdlib.vo spec_onepile.vo spec_apile.vo spec_triang.vo spec_main.vo verif_triang.vo
verif_onepile.vo: linking.vo onepile.vo spec_stdlib.vo spec_pile.vo spec_onepile.vo
verif_pile.vo: linking.vo pile.vo spec_stdlib.vo spec_pile.vo
verif_triang.vo: linking.vo triang.vo spec_stdlib.vo spec_pile.vo spec_triang.vo
verif_stdlib.vo: linking.vo spec_stdlib.vo
link_pile.vo: linking.vo verif_stdlib.vo verif_pile.vo verif_apile.vo verif_onepile.vo verif_main.vo

incr/verif_incr.vo: incr/incr.vo
fast/spec_fastpile.vo: fast/fastpile.vo spec_stdlib.vo
fast/spec_fastpile_concrete.vo: fast/fastpile.vo spec_stdlib.vo
fast/subsume_fastpile.vo: fast/fastpile.vo fast/spec_fastpile.vo fast/spec_fastpile_concrete.vo
fast/verif_fastpile.vo: linking.vo fast/fastpile.vo spec_stdlib.vo fast/spec_fastpile.vo
fast/verif_fastpile_concrete.vo: linking.vo fast/fastpile.vo spec_stdlib.vo fast/spec_fastpile_concrete.vo
fast/spec_fastapile.vo: fast/fastapile.vo spec_stdlib.vo fast/spec_fastpile.vo
fast/verif_fastapile.vo: linking.vo fast/fastapile.vo spec_stdlib.vo spec_pile.vo fast/spec_fastapile.vo
fast/spec_fastonepile.vo: onepile.vo spec_stdlib.vo fast/spec_fastpile.vo
fast/verif_fastonepile.vo: linking.vo onepile.vo spec_stdlib.vo fast/spec_fastpile.vo spec_onepile.vo
fast/spec_fastmain.vo: main.vo spec_stdlib.vo fast/spec_fastonepile.vo fast/spec_fastapile.vo fast/spec_fasttriang.vo
fast/verif_fastmain.vo: linking.vo main.vo spec_stdlib.vo fast/spec_fastonepile.vo fast/spec_fastapile.vo fast/spec_fasttriang.vo fast/spec_fastmain.vo fast/verif_fasttriang.vo
fast/link_fastpile.vo: verif_stdlib.vo fast/verif_fastpile.vo fast/verif_fastapile.vo fast/verif_fastonepile.vo fast/verif_fastmain.vo linking.vo
fast/spec_fasttriang.vo: triang.vo spec_stdlib.vo fast/spec_fastpile.vo
fast/verif_fasttriang.vo: linking.vo triang.vo spec_stdlib.vo fast/spec_fastpile.vo fast/spec_fasttriang.vo
