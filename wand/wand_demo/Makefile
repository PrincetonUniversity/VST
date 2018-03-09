CURRENT_LOC=.
VST_LOC=../..
CC_LOC=../../compcert
VFA_LOC=../vfa
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

CC_DIRS= lib common cfrontend exportclight
VST_DIRS= msl sepcomp veric floyd

CC_FLAGS= -R $(CC_LOC) compcert
VST_FLAGS=$(foreach d, $(VST_DIRS), -Q $(VST_LOC)/$(d) VST.$(d))
VFA_FLAGS= -R $(VFA_LOC) VFA

INCLUDE_DEMO = -R $(CURRENT_LOC) WandDemo $(VST_FLAGS) $(CC_FLAGS) $(VFA_FLAGS)
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_LOC) WandDemo $(VST_FLAGS) $(CC_FLAGS) $(VFA_FLAGS)
DEP_FLAG = $(DEP_DEMO)

FILES = \
  wand_frame.v wandQ_frame.v wand_frame_tactic.v VST_lemmas.v \
  list.v list_lemmas.v verif_list.v \
  SearchTree_ext.v bst.v bst_lemmas.v spec_bst.v verif_bst.v verif_bst_other.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_LOC)/$*.v

all: \
	_CoqProject .loadpath .depend $(FILES:%.v=%.vo)

../vfa/Maps.vo: ../vfa/Maps.v
	$(COQC) $(COQ_FLAG) $<

../vfa/Perm.vo: ../vfa/Perm.v
	$(COQC) $(COQ_FLAG) $<

../vfa/SearchTree.vo: ../vfa/SearchTree.v ../vfa/Maps.vo ../vfa/Perm.vo
	$(COQC) $(COQ_FLAG) $<

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob

_CoqProject: Makefile
	@echo $(COQ_FLAG) > _CoqProject

.loadpath: Makefile
	@echo $(COQ_FLAG) > .loadpath

.DEFAULT_GOAL := all

include .depend
