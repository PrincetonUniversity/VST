HFILES = pile.h pile_private.h onepile.h apile.h triang.h stdlib.h \
         fast/fastpile_private.h
CFILES = pile.c onepile.c apile.c triang.c main.c stdlib.c \
         fast/fastpile.c fast/fastapile.c
VFILES = PileModel.v spec_stdlib.v verif_stdlib.v spec_pile.v spec_pile_private.v verif_pile.v \
         spec_onepile.v verif_onepile.v spec_apile.v verif_apile.v \
         spec_triang.v verif_triang.v spec_main.v verif_core.v \
         fast/spec_fastpile.v fast/spec_fastpile_private.v fast/verif_fastpile.v \
         fast/spec_fastpile_concrete.v fast/verif_fastpile_concrete.v \
         fast/subsume_fastpile.v \
         fast/verif_fastapile.v fast/verif_fastcore.v \
         fast/verif_fastmain.v \
         simple_spec_stdlib.v simple_verif_stdlib.v simple_spec_pile.v simple_verif_pile.v \
         simple_spec_onepile.v simple_verif_onepile.v simple_spec_apile.v simple_verif_apile.v \
         simple_spec_triang.v simple_verif_triang.v simple_spec_main.v 

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


target: _CoqProject verif_main.vo simple_verif_main.vo fast/verif_fastmain.vo incr/verif_incr.vo

cvfiles: $(CVFILES)

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

CGFLAGS =  -DCOMPCERT -short-idents

ifdef CLIGHTGEN
$(CVFILES): $(CFILES) $(HFILES)
	$(CLIGHTGEN) -normalize $(CGFLAGS) $(CFILES)

incr/incr.v: incr/incr.c
	$(CLIGHTGEN) -normalize $(CGFLAGS) $<
endif

incr/verif_incr.vo: incr/verif_incr.v incr/incr.vo

_CoqProject: Makefile
	@echo $(VSTFLAGS) > _CoqProject

clean:
	rm -f *.vo *.o *.aux *.vok *.vos
	rm -f fast/*.vo fast/*.o fast/*.aux fast/*.vok fast/*.vos

# .depend depend:
# 	coqdep $(VSTFLAGS) *.v >.depend

FLOYD= $(VST_LOC)/floyd/proofauto.vo $(VST_LOC)/floyd/VSU.vo

PileModel.vo: PileModel.v $(FLOYD)
spec_apile.vo: apile.vo spec_stdlib.vo spec_pile.vo $(FLOYD)
spec_main.vo: main.vo spec_stdlib.vo spec_onepile.vo spec_apile.vo spec_triang.vo $(FLOYD)
spec_onepile.vo: onepile.vo spec_stdlib.vo spec_pile.vo $(FLOYD)
spec_pile.vo: pile.vo PileModel.vo spec_stdlib.vo $(FLOYD)
spec_pile_private.vo: spec_pile.vo spec_stdlib.vo $(FLOYD)
spec_stdlib.vo: spec_stdlib.v stdlib.vo $(FLOYD)
spec_main.vo: spec_main.v main.vo $(FLOYD)
spec_triang.vo: triang.vo spec_stdlib.vo spec_pile.vo $(FLOYD)
verif_apile.vo: apile.vo spec_stdlib.vo spec_pile.vo spec_apile.vo spec_pile_private.vo
verif_core.vo: main.vo verif_stdlib.vo spec_pile_private.vo verif_pile.vo verif_onepile.vo verif_apile.vo verif_triang.vo
verif_main.vo: spec_main.vo verif_core.vo
verif_onepile.vo: onepile.vo spec_stdlib.vo spec_pile.vo spec_onepile.vo
verif_pile.vo: pile.vo spec_stdlib.vo spec_pile_private.vo
verif_triang.vo: triang.vo spec_stdlib.vo spec_pile.vo spec_triang.vo
verif_stdlib.vo: spec_stdlib.vo
link_pile.vo: verif_main.vo
incr/verif_incr.vo: incr/incr.vo
fast/spec_fastpile.vo: fast/fastpile.vo spec_stdlib.vo PileModel.vo $(FLOYD)
fast/spec_fastpile_private.vo: fast/spec_fastpile.vo spec_stdlib.vo  $(FLOYD)
fast/spec_fastpile_concrete.vo: fast/fastpile.vo spec_stdlib.vo $(FLOYD)
fast/subsume_fastpile.vo: fast/fastpile.vo spec_stdlib.vo fast/spec_fastpile.vo fast/verif_fastpile.vo fast/verif_fastpile_concrete.vo $(FLOYD)
fast/verif_fastpile.vo: fast/fastpile.vo spec_stdlib.vo fast/spec_fastpile.vo fast/spec_fastpile_private.vo
fast/verif_fastpile_concrete.vo: fast/fastpile.vo spec_stdlib.vo fast/spec_fastpile_concrete.vo
fast/verif_fastapile.vo: fast/fastapile.vo spec_stdlib.vo spec_pile.vo fast/spec_fastpile_private.vo
fast/verif_fastonepile.vo: onepile.vo spec_stdlib.vo fast/spec_fastpile.vo spec_onepile.vo
fast/verif_fastcore.vo: main.vo verif_stdlib.vo fast/spec_fastpile_private.vo fast/verif_fastpile.vo fast/verif_fastonepile.vo fast/verif_fastapile.vo fast/verif_fasttriang.vo 
fast/verif_fastmain.vo: main.vo fast/verif_fastcore.vo
fast/link_fastpile.vo: fast/verif_fastmain.vo
fast/verif_fasttriang.vo: triang.vo spec_stdlib.vo spec_triang.vo fast/spec_fastpile.vo
simple_spec_apile.vo: apile.vo simple_spec_stdlib.vo simple_spec_pile.vo $(FLOYD)
simple_spec_main.vo: main.vo simple_spec_stdlib.vo simple_spec_onepile.vo simple_spec_apile.vo simple_spec_triang.vo $(FLOYD)
simple_spec_onepile.vo: onepile.vo simple_spec_stdlib.vo simple_spec_pile.vo $(FLOYD)
simple_spec_pile.vo: pile.vo PileModel.vo simple_spec_stdlib.vo $(FLOYD)
simple_spec_stdlib.vo: simple_spec_stdlib.v stdlib.vo $(FLOYD)
simple_spec_main.vo: simple_spec_main.v main.vo $(FLOYD)
simple_spec_triang.vo: triang.vo simple_spec_stdlib.vo simple_spec_pile.vo $(FLOYD)
simple_verif_apile.vo: apile.vo simple_spec_stdlib.vo simple_spec_pile.vo simple_spec_apile.vo $(FLOYD)
simple_verif_main.vo: simple_spec_main.vo main.vo simple_verif_stdlib.vo simple_verif_pile.vo simple_verif_onepile.vo simple_verif_apile.vo simple_verif_triang.vo $(FLOYD)
simple_verif_onepile.vo: onepile.vo simple_spec_stdlib.vo simple_spec_pile.vo simple_spec_onepile.vo $(FLOYD)
simple_verif_pile.vo: pile.vo simple_spec_pile.vo simple_spec_stdlib.vo $(FLOYD)
simple_verif_triang.vo: triang.vo simple_spec_stdlib.vo simple_spec_pile.vo simple_spec_triang.vo $(FLOYD)
simple_verif_stdlib.vo: simple_spec_stdlib.vo $(FLOYD)
simple_link_pile.vo: simple_verif_main.vo $(FLOYD)
