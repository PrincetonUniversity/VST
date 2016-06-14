CURRENT_DIR = $(shell pwd)
RAMIFY_COQLIB = "/Users/Qinxiang/Documents/NUS-project"

COQC=coqc
COQDEP=coqdep -slash

COQ_FLAG = -R $(CURRENT_DIR) -as RndHoare -R $(RAMIFY_COQLIB) -as RamifyCoq
DEP_FLAG = -R $(CURRENT_DIR) -as RndHoare -R $(RAMIFY_COQLIB) -as RamifyCoq

FILES = \
  axiom.v\
  sigma_algebra.v measurable_function.v probability_measure.v regular_conditional_prob.v\
  random_oracle.v random_variable.v meta_state.v imperative.v probabilistic_pred.v max_anti_chain.v\
  normal_imperative.v

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
