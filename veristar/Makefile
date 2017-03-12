# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is
COQFLAGS= -I . -as veristar
DEPFLAGS= -I ../msl -as msl -I ../compositional_compcert -as compositional_compcert -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
COQTOPFLAGS= -batch -load-vernac-source

FILES = LibTactics.v LibTactics2.v tactics.v basic.v \
	redblack.v wellfounded.v compare.v variables.v datatypes.v fresh.v \
	superpose.v superpose_modelsat.v heapresolve.v veristar.v model_type.v model.v \
	clause_lemmas.v cclosure.v superpose_sound.v superpose_modelsat_sound.v \
	spred_lemmas.v clausify_sound.v clause_universe.v \
	wellformed_sound.v unfold_sound.v norm_sound.v veristar_sound.v \
	clauses.v list_denote.v simple_model.v

proof: $(FILES:.v=.vo)

redblack.ml redblack.mli: redblack.vo rbtest.v
	${COQC} $(COQFLAGS) $(DEPFLAGS) rbtest.v

redblack.cmi: redblack.mli
	ocamlc -c redblack.mli

redblack.cmo: redblack.ml redblack.cmi
	ocamlc -c redblack.ml

rbtest2.cmo: redblack.cmi rbtest2.ml
	ocamlc -c rbtest2.ml

rbtest: redblack.cmo rbtest2.cmo
	ocamlc redblack.cmo rbtest2.cmo -o rbtest

rbtest-out: rbtest
	./rbtest >rbtest-out

#rm veristar.mli: hack to get around nonextraction of module sharing constraints
extract: veristar.vo superpose_modelsat.vo
	cd extract && $(COQTOP) $(COQTOPFLAGS) extract.v && \
	awk -f splice.awk veristar.ml >tmpfile && \
	mv tmpfile veristar.ml && \
	rm veristar.mli && \
	make

puretest: extract
	time extract/smallfoot test/test.pure.entailments.sf > /tmp/pure.1
	results/truthify.awk </tmp/pure.1 >/tmp/pure.2
	diff -s /tmp/pure.2 results/pure.ground

test: extract
	time extract/smallfoot test/test.entailments.sf > /tmp/test.1
	results/truthify.awk </tmp/test.1 >/tmp/test.2
	diff -s /tmp/test.2 results/test.ground

doc:
	$(COQDOC) -R . veristar -g --html -d doc $(FILES)

graph:
	runhaskell util/mkSrcGraph.hs > util/srcGraph.dot
	tred util/srcGraph.dot | dot -Tpng >util/srcGraph.png

all: extract

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $(COQFLAGS) $(DEPFLAGS) -dump-glob $*.glob $*.v

depend:
	$(COQDEP) $(COQFLAGS) $(DEPFLAGS) $(FILES) > .depend

clean:
	rm -f *.vo *.glob *.cmx *.cmi *~

count:
	wc -l $(FILES)

.PHONY: doc graph test

include .depend
