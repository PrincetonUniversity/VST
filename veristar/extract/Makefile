export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc -dtypes
export OCAMLOPT = ocamlopt -dtypes

INCLUDES =

PARSING = misc.mli misc.ml location.mli location.ml parsetree.mli parsetree.ml config.mli config.ml symbtree.mli symbtree.ml error.mli error.ml parser.mly lexer.mll
PARSING_TRASH = parser.output

VERISTAR = veristar.mli veristar.ml driver.ml

TOPLEVEL_SOURCES = $(PARSING) $(VERISTAR) vcgen.mli vcgen.ml inductive_preds.mli inductive_preds.ml symbsimp.mli symbsimp.ml toplevel.ml
TOPLEVEL_TRASH = $(PARSING_TRASH)
TOPLEVEL = SOURCES="$(TOPLEVEL_SOURCES)" \
           RESULT=toplevel \
           TRASH="$(TOPLEVEL_TRASH)"

MAIN = SOURCES="$(TOPLEVEL_SOURCES) main.ml" \
       LIBS="str" \
       RESULT=smallfoot.byte \
       TRASH="$(TOPLEVEL_TRASH)"

MAINGUI = \
       SOURCES="$(TOPLEVEL_SOURCES) main-gui.ml" \
       EXTRA_CMO="gtkInit.cmo" \
       OCAMLFLAGS="-I +lablgtk" \
       OCAMLLDFLAGS="-I +lablgtk" \
       LIBS="str unix lablgtk" \
       RESULT=smallfoot-gui.byte \
       TRASH="$(TOPLEVEL_TRASH)"

MAINOPT = SOURCES="$(TOPLEVEL_SOURCES) main.ml" \
       LIBS="str" \
       RESULT=smallfoot \
       TRASH="$(TOPLEVEL_TRASH)"

MAINOPTGUI = \
       SOURCES="$(TOPLEVEL_SOURCES) main-gui.ml" \
       EXTRA_CMX="gtkInit.cmx" \
       OCAMLFLAGS="-I +lablgtk" \
       OCAMLLDFLAGS="-I +lablgtk" \
       LIBS="str unix lablgtk" \
       RESULT=smallfoot-gui \
       TRASH="$(TOPLEVEL_TRASH)"

default: smallfoot

all: toplevel smallfoot.byte smallfoot-gui.byte smallfoot smallfoot-gui veristar

.PHONY: smallfoot.byte
smallfoot.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) debug-code

.PHONY: smallfoot-gui.byte
smallfoot-gui.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINGUI) debug-code

.PHONY: smallfoot
smallfoot:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

.PHONY: smallfoot-gui
smallfoot-gui:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPTGUI) native-code

.PHONY: toplevel
toplevel:
	$(MAKE) -f $(OCAMLMAKEFILE) $(TOPLEVEL) byte-code-library

.PHONY: veristar
veristar:
	$(OCAMLC) $(VERISTAR) -o util.out

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINGUI) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPTGUI) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TOPLEVEL) clean
	rm *.annot

depend:
	ocamldep $(INCLUDES) *.mli *.ml > .depend
include .depend
