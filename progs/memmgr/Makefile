ifdef VST_LOC
include $(VST_LOC)/Makefile.bundled
endif

HFILES= mmap0.h malloc.h
CFILES= mmap0.c malloc.c
VFILES = malloc_lemmas.v ASI_mmap0.v ASI_malloc.v malloc_shares.v malloc_sep.v \
         VSU_malloc_definitions.v verif_malloc_free.v \
         verif_bin2size2bin.v verif_list_from_block.v verif_fill_bin.v \
         verif_malloc_small.v verif_malloc_large.v \
         verif_free_small.v verif_free_large.v \
         verif_pre_fill.v verif_try_pre_fill.v \
         VSU_malloc.v VSU_mmap0.v VSU_MM.v

CC=ccomp
CFLAGS=-O

CLIGHTGEN= $(COMPCERT_LOC)/clightgen

CVFILES = $(patsubst %.c,%.v,$(CFILES))
OFILES = $(patsubst %.c,%.o,$(CFILES))
VOFILES = $(patsubst %.v,%.vo,$(CVFILES) $(VFILES))


all: _CoqProject $(VOFILES) VSU_MM.vo 

cvfiles: $(CVFILES)

%.vo: %.v
	@echo COQC $*.v
	@coqc $(VSTFLAGS) $*.v

$(CVFILES): $(CFILES) $(HFILES)
	$(CLIGHTGEN) -short-idents -normalize $(CFILES)

clean:
	rm -f *.vo *.o .*.aux *.vok *.vos *.glob

ASI_malloc.vo: malloc_lemmas.vo
malloc_lemmas.vo: malloc.vo
malloc_sep.vo: malloc_lemmas.vo malloc_shares.vo
VSU_malloc_definitions.vo: malloc.vo malloc_lemmas.vo malloc_sep.vo ASI_mmap0.vo ASI_malloc.vo
verif_malloc_free.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_bin2size2bin.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_list_from_block.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_fill_bin.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_malloc_small.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_malloc_large.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_free_small.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_free_large.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_pre_fill.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
verif_try_pre_fill.vo: malloc.vo ASI_malloc.vo malloc_lemmas.vo malloc_sep.vo VSU_malloc_definitions.vo
VSU_malloc.vo: verif_malloc_free.vo verif_bin2size2bin.vo verif_list_from_block.vo verif_fill_bin.vo verif_malloc_small.vo verif_malloc_large.vo verif_free_small.vo verif_free_large.vo verif_pre_fill.vo verif_try_pre_fill.vo verif_malloc_free.vo
VSU_mmap0.vo: mmap0.vo ASI_mmap0.vo
VSU_MM.vo: VSU_malloc.vo VSU_mmap0.vo
