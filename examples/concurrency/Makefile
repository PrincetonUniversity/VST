COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

FILES = small_concurrent_stack.v oracular_safety.v resourcemaps.v csl_to_machine_safety.v

.PHONY : clean all lib docs

all: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

# dependencies:
csl_to_machine_safety.vo:resourcemaps.vo
oracular_safety.vo:small_concurrent_stack.vo
