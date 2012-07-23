#SymEvalTests

MODULES := Word Array Common Vector Core Front RTL Flat CSE FirstOrder Compiler
TESTS := 
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)
ARGS :=-R . Synthesis

#SepExprTests UnfolderTests 

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

admit:
	@ echo Admitted lemmas --------------------------
	@ grep admit *.v
	@ grep Admitted *.v

toplevel: coq
	coqtop.opt $(ARGS)