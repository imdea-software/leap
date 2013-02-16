PROJNAME=leap

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


.PHONY: clean softclean all expand unexpand leap prog2fts pinv sinv pvd tll numinv spec_check doc tools


# Flags

OCAML_FLAGS= \
	-pp "`pwd`/prep.sh"


LIBS = unix,str,dynlink,bolt


# Compilation rules

all: $(PROG2FTS) $(PINV) $(SINV) $(PVD) \
		 $(NUMINV) $(SPEC_CHECK) $(TLL) $(LEAP) $(TOOLS)

$(TOOLS) :
	@echo "Verifying presence of tools in "$(TOOLS)" folder...";
	$(call check_tool,z3,$(Z3));
	$(call check_tool,yices,$(YICES));
	$(call check_tool,minisat,$(MINISAT));
	$(call check_tool,lingeling,$(LINGELING));


$(LEAP):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).native
	@ln -f -s ./_build/src/progs/leap/$(LEAP).native $(LEAP)

$(PROG2FTS):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PROG2FTS).native
	@ln -f -s ./_build/src/progs/prog2fts/$(PROG2FTS).native $(PROG2FTS)

$(PINV):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PINV).native
	@ln -f -s ./_build/src/progs/pinv/$(PINV).native $(PINV)

$(SINV):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(SINV).native
	@ln -f -s ./_build/src/progs/sinv/$(SINV).native $(SINV)

$(PVD):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(PVD).native
	@ln -f -s ./_build/src/progs/pvd/$(PVD).native $(PVD)

$(NUMINV):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(NUMINV).native
	@ln -f -s ./_build/src/progs/numinv/$(NUMINV).native $(NUMINV)

$(SPEC_CHECK):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(SPEC_CHECK).native
	@ln -f -s ./_build/src/progs/spec_check/$(SPEC_CHECK).native $(SPEC_CHECK)

$(TLL):
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) $(TLL).native
	@ln -f -s ./_build/src/progs/tll/$(TLL).native $(TLL)

solvertest:
	ocamlbuild -j 0 $(OCAML_FLAGS) -libs $(LIBS) test.native



doc:
	@find src/* \( -name *.ml -o -name *.mli -o -name *.mll -o -name *.mly \) | cut -d"." -f1 | sort -u > leap.odocl
	ocamlbuild -ocamldoc "ocamldoc.opt -hide-warnings" leap.docdir/index.html

clean:
	ocamlbuild -clean
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
