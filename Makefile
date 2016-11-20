DIRS=src extraction from_compcert

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQLIBS:=-I ~/gitrepos/cases/src -R ~/gitrepos/cases/theories Case_Tactics\
	-R ~/gitrepos/PilkiLib "" -R src/ "" -R from_compcert ""


COQC=coqc -q $(INCLUDES) $(COQLIBS)
COQDEP=coqdep $(COQLIBS)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) $(COQLIBS) -batch -load-vernac-source


OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  -I extraction -I driver

VPATH=$(DIRS)
GPATH=$(DIRS)

FCPCERT= AST.v  Axioms.v Errors.v  Floats.v  Integers.v  Maps.v \
  Memdata.v  CompMemory.v  Memtype.v Values.v Cminor.v \
  Events.v Globalenvs.v Smallstep.v Intv.v Ordered.v Switch.v
#  RTL.v RTLgen.v CminorSel.v Op.v Registers.v RTLgenspec.v Sets.v \
#  RTLgenproof.v

SRC= Libs.v Memory.v OtherMemory.v ArithClasses.v \
  PolyBase.v Polyhedra.v Loops.v CeildFloord.v PLang.v\
  PDep.v Bounds.v Instructions.v BoxedPolyhedra.v\
  PermutInstrs.v TimeStamp.v Tilling.v ExtractPoly.v Final.v\
  SimpleLanguage.v OCamlInterface.v

EXTRACTION=extraction.v

FILES=$(SRC) $(EXTRACTION) $(FCPCERT)

validator: driver/*.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) PrintingPprog.native

proof: $(FILES:.v=.vo)


extraction: extraction.v
	rm -f extraction/*.ml extraction/*.mli extraction/*.vo
	$(COQEXEC) extraction/extraction.v

.PHONY: extraction

.SUFFIXES: .v .vo

.v.vo:
#	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob /dev/null $*.v

depend: $(FILES)
	$(COQDEP) $^ \
        > .depend


clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -rf _build
	rm -f doc/coq2html.ml doc/coq2html
	rm -f extraction/*.ml extraction/*.mli



include .depend

FORCE:
