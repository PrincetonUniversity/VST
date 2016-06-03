CURRENT_DIR = $(shell pwd)

COQC=coqc
COQDEP=coqdep -slash

COQ_FLAG = -R $(CURRENT_DIR) -as RndHoare
DEP_FLAG = -R $(CURRENT_DIR) -as RndHoare

FILES = \
  sigma_algebra.v measurable_function.v probability_measure.v regular_conditional_prob.v\
  random_oracle.v random_variable.v imperative.v probabilistic_pred.v full_domain.v

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
