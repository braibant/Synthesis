ROOT    := ..
MODULES := Stack Sorter Add Driver Extraction

VS      := $(MODULES:%=%.v)

.PHONY: coq clean backend

backend: coq
	ocamlbuild -lib unix -Is extracted,backend generators.native

all: coq backend

demo: backend
	# generate demo cores in the directory verilog/
	mkdir -p verilog/
	./generators.native -adder 4
	./generators.native -sorter 4
	./generators.native -stack

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
