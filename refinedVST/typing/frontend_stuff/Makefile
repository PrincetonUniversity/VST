all:
	@dune build _build/default/refinedc.install --display short
.PHONY: all

all_with_examples: generate_all
	@dune build --display short
.PHONY: all_with_examples

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

C_SRC = $(wildcard examples/*.c)

%.c.gen: %.c phony
	@dune exec -- refinedc check $<
.PHONY: phony

generate_all: $(addsuffix .gen, $(C_SRC))
.PHONY: generate_all

check_generate_all: generate_all
	git diff --exit-code
.PHONY: check_generate_all

clean_generated:
	@for FILE in ${C_SRC} ; do dune exec -- refinedc clean --soft $$FILE ; done
	@rm -f $(addsuffix .gen, $(C_SRC))
.PHONY: clean_generated

clean: clean_generated
	@dune clean
.PHONY: clean

# We cannot use builddep-pins as a dependency of builddep-opamfiles because the CI removes all pins.
builddep-pins:
	@opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
	@opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
.PHONY: builddep-pins

builddep-opamfiles: builddep/refinedc-builddep.opam
	@true
.PHONY: builddep-opamfiles