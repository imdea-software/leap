PROJNAME=leap

# Makefile configuration
OCAMLBUILD=ocamlbuild.native

# Folders
SRC=src
BIN=bin
PROGS=$(SRC)/progs


# Tools

# Programs
LEAP=leap
PRGINFO=prginfo
#PINV=pinv
#SINV=sinv
#PVD=pvd
#NUMINV=numinv
#SPEC_CHECK=spec_check
TLL=tll
SOLVE=solve
TSL=tsl
#TMPTSL=tmptsl
APPLYTAC=applytac
TOOLS=tools


# Configuration
SYS=`uname -s`

REVISION=`svn info | grep Revision | cut -d ' ' -f 2`
DATE=`svn info | grep Date | cut -d ' ' -f 7-10 | cut -c 2-17`
TIME=`svn info | grep Date | cut -d ' ' -f 5-6`
#REVISION=0



check_tool = @if [[ `command -v $(1)` ]] ; then \
							 echo "[ OK ]  --  $(1)"; \
						 else \
							 echo "[    ]  --  $(1)"; \
						 fi

copy = @mkdir -p $(2); cp $(1) $(2)/$(3)


.PHONY: profile debug clean all expand unexpand leap prog2fts prginfo pinv sinv pvd tll solve applytac tmptsl tsl numinv spec_check doc tools tests

# Flags

OCAMLBUILD_FLAGS= -j 0 -build-dir _build

OCAML_FLAGS=
#-cflags -w,+A-4
#-cflags -w,K
#	-cflags -warn-error,A \
#	-cflags -w,Z \

PROFILE_FLAGS=-ocamlc ocamlcp -ocamlopt ocamloptp
DEBUG_FLAGS=

LIBS = unix,str


# Compilation rules

all: $(PRGINFO) \
		 $(PINV) \
		 $(SINV) \
		 $(PVD) \
		 $(NUMINV) \
		 $(SPEC_CHECK) \
		 $(TLL) \
		 $(TSL) \
		 $(SOLVE) \
		 $(LEAP) \
		 $(TOOLS)

$(TOOLS) :
	@echo "Verifying presence of tools in the system...";
	$(call check_tool,z3);
	$(call check_tool,yices);
	$(call check_tool,minisat);
	$(call check_tool,lingeling);
	$(call check_tool,cvc4)

write-revision:
	@echo "let value = "${REVISION} > $(PROGS)/Revision.ml
	@echo "let date = \"${DATE}\"" >> $(PROGS)/Revision.ml
	@echo "let time = \"${TIME}\"" >> $(PROGS)/Revision.ml


profile: write-revision
	$(OCAMLBUILD) $(PROFILE_FLAGS) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).p.native
	$(call copy,./_build/$(PROGS)/leap/$(LEAP).p.native,$(BIN),$(LEAP).p.native)

debug: write-revision
	$(OCAMLBUILD) $(DEBUG_FLAGS) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).d.byte
	$(call copy,./_build/$(PROGS)/leap/$(LEAP).d.byte,$(BIN),$(LEAP).d.byte)

$(LEAP).byte: write-revision
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@
	$(call copy,./_build/$(PROGS)/leap/$@,$(BIN),$@)

$(LEAP): write-revision
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/leap/$@.native,$(BIN),$@)

$(PRGINFO):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/prginfo/$@.native,$(BIN),$@)

$(PINV):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/pinv/$@.native,$(BIN),$@)

$(SINV):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/sinv/$@.native,$(BIN),$@)

$(PVD):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/pvd/$@.native,$(BIN),$@)

$(NUMINV):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/numinv/$@.native,$(BIN),$@)

$(SPEC_CHECK):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/spec_check/$@.native,$(BIN),$@)

$(TLL):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tll/$@.native,$(BIN),$@)

$(TSL):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tsl/$@.native,$(BIN),$@)

$(SOLVE):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/solve/$@.native,$(BIN),$@)

$(TMPTSL):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tmptsl/$@.native,$(BIN),$@)

$(APPLYTAC):
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/applytac/$@.native,$(BIN),$@)

solvertest:
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) test.native

tests:
	@for i in $(SRC)/tests/*.ml; do $(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) "$$(expr "$$i" : '\(.*\)\.ml').byte" ; done


doc:
	@find $(SRC)/* \( -name *.ml -o -name *.mli -o -name *.mll -o -name *.mly \) | cut -d"." -f1 | sort -u > leap.odocl
	$(OCAMLBUILD) -ocamldoc "ocamldoc.opt -hide-warnings" leap.docdir/index.html

clean:
	$(OCAMLBUILD) -clean
	@rm -rf $(BIN)/*
	@rm *.odocl


dist:   clean
	tar  zcvf ../${PROJNAME}-`date +"%Y-%m-%d-%H-%M-%S"`.tar.gz \
				--exclude=tmp --exclude=test --exclude=.svn --exclude=*.o \
				--exclude=yices --exclude=z3 --exclude=trsParse . 

expand:
	@echo "Expanding tabs..."
	@for i in `find examples/* $(SRC)/* -type f | grep -v \\.swp | grep -v \\.svn | grep -v \\.py` ; do expand -t 2 $$i > temp.file ; mv temp.file $$i; done
	@for i in `find examples/* $(SRC)/* -type f | grep \\.sh` ; do chmod +x $$i; done


unexpand:
	@echo "Unexpanding tabs..."
	@for i in `find examples/* $(SRC)/* -type f | grep -v \\.swp | grep -v \\.svn | grep -v \\.py` ; do unexpand -t 2 $$i > temp.file ; mv temp.file $$i; done
	@for i in `find examples/* $(SRC)/* -type f | grep \\.sh` ; do chmod +x $$i; done

cleartmp:
	@echo "Erasing temporary editor's files..."
	@for i in `find . -type f | grep \\.sw` ; do rm $$i ; done
	@echo "OK"

