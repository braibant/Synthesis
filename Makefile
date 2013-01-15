.PHONY: all clean dist

all:
	# BEWARE: This will probably take a long time!
	$(MAKE) -C src
	$(MAKE) -C examples

FILES := src/Structures.v src/Consider.v src/Seq.v src/Compare.v	\
src/Word.v src/Vector.v src/DList.v src/Common.v src/Core.v		\
src/Front.v src/IR.v src/RTL.v src/CSE.v src/BDD.v src/CP.v		\
src/FirstOrder.v src/Compiler.v examples/Add.v examples/Driver.v	\
examples/Extraction.v examples/Sorter.v examples/Stack.v

doc:
	coqdoc -toc -interpolate -utf8 -html -g -R src Synthesis -R examples Examples --lib-subtitles --no-lib-name -d html $(FILES) 	


clean:
	$(MAKE) -C src clean
	$(MAKE) -C examples clean


VERSION := 0.1
dist:
	git archive --format=tar --prefix=synthesis/ master src examples LICENSE README.txt | gzip > fe-si-$(VERSION).tar.gz

admit:
	$(MAKE) -C src admit
