COQC=coqc 
COQDEP=coqdep
COQDOC=coqdoc

FILES = small_concurrent_stack.v oracular_safety.v

.PHONY : clean all lib docs

all: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)
