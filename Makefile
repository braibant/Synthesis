# Makefile for FeSI

all : Makefile.coq
	$(MAKE) -f Makefile.coq

clean : Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq : Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
