# This makefile is based on Karl Palmskog's "Coq Program Verification Template"
# available at https://github.com/palmskog/coq-program-verification-template and
# licensed under the MIT license.

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force
