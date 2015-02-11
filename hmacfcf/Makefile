
MODULES := splitVector cAU hF HMAC_spec NMAC_to_HMAC GNMAC_PRF GHMAC_PRF HMAC_PRF

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -I "../FCF" $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
