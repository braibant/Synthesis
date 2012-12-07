ROOT    := ..
MODULES := Stack Isa Mult MOD Add Driver Extraction

VS      := $(MODULES:%=%.v)

.PHONY: coq clean backend

backend: coq
	ocamlbuild -lib unix -Is extracted,backend main.byte

all: coq backend


coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Synthesis \
                     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
	ocamlbuild -clean
	rm -f extracted/*
