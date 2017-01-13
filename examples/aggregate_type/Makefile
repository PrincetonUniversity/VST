CURRENT_DIR = $(shell pwd)
VST_DIR = $(shell cd ../..; pwd)
-include CONFIGURE

COMPCERT_DIR = $(VST_DIR)compcert/
COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = demo1 demo2
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) compcert
INCLUDE_VST = -R $(VST_DIR)/msl msl
INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) AggregateType.$(d))
COQ_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_VST) $(INCLUDE_DEMO)
DEP_COMPCERT = -R $(COMPCERT_DIR) -as compcert
DEP_VST = -R $(VST_DIR)/msl -as msl
DEP_DEMO = -R $(CURRENT_DIR) -as AggregateType
DEP_FLAG = $(DEP_COMPCERT) $(DEP_VST) $(DEP_DEMO)

DEMO1_FILES = \
  expr.v type_rec_functions.v path_rec_functions.v soundness_proofs.v

DEMO2_FILES = \
  expr.v computable_theorems.v other_def.v type_induction.v prod_lemmas.v type_rec_functions.v path_rec_functions.v field_at_data_at.v

FILES = \
  $(DEMO1_FILES:%.v=demo1/%.v) \
  $(DEMO2_FILES:%.v=demo2/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo) \

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo */*.vo *.glob */*.glob

.DEFAULT_GOAL := all

include .depend
