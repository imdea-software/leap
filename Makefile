BOLT_DIR=$(shell ocamlfind query bolt)
CAMLP4LIB=${BOLT_DIR}
PROJNAME=leap

# Makefile configuration
OCAMLBUILD=ocamlbuild.native

# Folders
SCRIPTS=scripts
TOOLS=tools
TOOLS_SRC=../../../../others/tools


# Tools
Z3=z3-4.3.1
YICES=yices-1.0.34
MINISAT=minisat
LINGELING=lingeling-587f


# Programs
LEAP=leap
PROG2FTS=prog2fts
PINV=pinv
SINV=sinv
PVD=pvd
NUMINV=numinv
SPEC_CHECK=spec_check
TLL=tll


# Configuration
SYS=`uname -s`

check_tool = @if ( test -e $(TOOLS)/$(1) ) || (test -h $(TOOLS)/$(1) ) ; then \
							echo "$(1): already installed"; \
						else \
							echo "$(1): not installed. Linking to $(TOOLS_SRC)/$(1)/bin/$(2)-$(SYS)"; \
							ln -s $(TOOLS_SRC)/$(1)/bin/$(2)-$(SYS) $(TOOLS)/$(1); \
						fi


.PHONY: clean softclean all expand unexpand leap prog2fts pinv sinv pvd tll numinv spec_check doc tools tests


# Flags

OCAML_FLAGS= \
	-pp "`pwd`/prep.sh" \
        -lflags -I,"${BOLT_DIR}" \
	-cflags -I,"${BOLT_DIR}" \
#	-cflags -warn-error,A \
#	-cflags -w,Z \


LIBS = unix,str,dynlink,bolt


# Compilation rules

all: $(PROG2FTS) $(PINV) $(SINV) $(PVD) \
		 $(NUMINV) $(SPEC_CHECK) $(TLL) $(LEAP) $(LEAP).native $(TOOLS)

$(TOOLS) :
	@echo "Verifying presence of tools in "$(TOOLS)" folder...";
	$(call check_tool,z3,$(Z3));
	$(call check_tool,yices,$(YICES));
	$(call check_tool,minisat,$(MINISAT));
	$(call check_tool,lingeling,$(LINGELING));


$(LEAP):
	$(OCAMLBUILD) -use-ocamlfind -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).byte
	@ln -f -s ./_build/src/progs/leap/$(LEAP).byte $(LEAP)

$(LEAP).native:
	$(OCAMLBUILD) -use-ocamlfind -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).native
	@ln -f -s ./_build/src/progs/leap/$(LEAP).native $(LEAP)

$(PROG2FTS):
	$(OCAMLBUILD) -use-ocamlfind -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PROG2FTS).native
	@ln -f -s ./_build/src/progs/prog2fts/$(PROG2FTS).native $(PROG2FTS)

$(PINV):
	$(OCAMLBUILD) -use-ocamlfind -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PINV).native
	@ln -f -s ./_build/src/progs/pinv/$(PINV).native $(PINV)

$(SINV):
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(SINV).native
	@ln -f -s ./_build/src/progs/sinv/$(SINV).native $(SINV)

$(PVD):
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PVD).native
	@ln -f -s ./_build/src/progs/pvd/$(PVD).native $(PVD)

$(NUMINV):
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(NUMINV).native
	@ln -f -s ./_build/src/progs/numinv/$(NUMINV).native $(NUMINV)

$(SPEC_CHECK):
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(SPEC_CHECK).native
	@ln -f -s ./_build/src/progs/spec_check/$(SPEC_CHECK).native $(SPEC_CHECK)

$(TLL):
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(TLL).native
	@ln -f -s ./_build/src/progs/tll/$(TLL).native $(TLL)

solvertest:
	$(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) test.native

tests:
	@for i in src/tests/*.ml; do $(OCAMLBUILD) -j 0 $(OCAML_FLAGS) -libs $(LIBS) "$$(expr "$$i" : '\(.*\)\.ml').byte" ; done


doc:
	@find src/* \( -name *.ml -o -name *.mli -o -name *.mll -o -name *.mly \) | cut -d"." -f1 | sort -u > leap.odocl
	$(OCAMLBUILD) -ocamldoc "ocamldoc.opt -hide-warnings" leap.docdir/index.html

clean:
	$(OCAMLBUILD) -clean
	rm -f $(LEAP) $(TLL) $(PROG2FTS) $(PINV) $(SINV) $(PVD) $(NUMINV) $(SPEC_CHECK) test.native

softclean:
	rm -rf _build _log

dist:   clean
	tar  zcvf ../${PROJNAME}-`date +"%Y-%m-%d-%H-%M-%S"`.tar.gz \
				--exclude=tmp --exclude=test --exclude=.svn --exclude=*.o \
				--exclude=yices --exclude=z3 --exclude=trsParse . 

expand:
	for i in `find examples/* src/* -type f | grep -v \\.swp | grep -v \\.svn` ; do expand -t 2 $$i > temp.file ; mv temp.file $$i; done

unexpand:
	for i in `find examples/* src/* -type f | grep -v \\.swp | grep -v \\.svn` ; do unexpand -t 2 $$i > temp.file ; mv temp.file $$i; done

