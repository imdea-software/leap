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
PINV=pinv
SINV=sinv
PVD=pvd
SPEC_CHECK=spec_check
TLL=tll
THM=thm
SOLVE=solve
TSLK=tslk
TSL=tsl
APPLYTAC=applytac
TOOLS=tools

# Configuration
SYS=`uname -s`

REVISION=`git rev-list --count master`
MYPATH=`echo $(PATH)`
DATE=`date +"%A %B %d %Y"`
TIME=`date +"%X %z"`


check_tool = @if [[ `command -v $(1)` ]] ; then \
							 echo "[ OK ]  --  $(1)"; \
						 else \
							 echo "[    ]  --  $(1)"; \
						 fi

copy = @mkdir -p $(2); cp $(1) $(2)/$(3)


.PHONY: profile debug clean all expand unexpand leap prog2fts prginfo tll solve applytac tsl spec_check doc tools tests revision

# Flags

OCAMLBUILD_FLAGS= -j 0 -build-dir _build

OCAML_FLAGS=-cflags -w,-4-32

PROFILE_FLAGS=-ocamlc ocamlcp -ocamlopt ocamloptp
DEBUG_FLAGS=

LIBS = unix,str


# Compilation rules

all: $(PRGINFO) \
		 $(NUMINV) \
		 $(SPEC_CHECK) \
		 $(TLL) \
		 $(THM) \
		 $(TSLK) \
		 $(TSL) \
		 $(SOLVE) \
		 $(APPLYTAC) \
		 $(LEAP) \
		 $(TOOLS)

$(TOOLS) :
	@echo "Verifying presence of tools in the system...";
	$(call check_tool,z3);
	$(call check_tool,yices);
	$(call check_tool,minisat);
	$(call check_tool,lingeling);
	$(call check_tool,cvc4)

revision:
	@echo "let value = "${REVISION} > $(PROGS)/Revision.ml
	@echo "let date = \"${DATE}\"" >> $(PROGS)/Revision.ml
	@echo "let time = \"${TIME}\"" >> $(PROGS)/Revision.ml

set-my-path:
	@echo "let mypath = \"${MYPATH}\"" > $(PROGS)/MyPath.ml

profile: set-my-path
	$(OCAMLBUILD) $(PROFILE_FLAGS) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).p.native
	$(call copy,./_build/$(PROGS)/leap/$(LEAP).p.native,$(BIN),$(LEAP).p.native)

debug: set-my-path
	$(OCAMLBUILD) $(DEBUG_FLAGS) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $(LEAP).d.byte
	$(call copy,./_build/$(PROGS)/leap/$(LEAP).d.byte,$(BIN),$(LEAP).d.byte)

$(LEAP).byte: set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@
	$(call copy,./_build/$(PROGS)/leap/$@,$(BIN),$@)

$(LEAP): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/leap/$@.native,$(BIN),$@)

$(PRGINFO): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/prginfo/$@.native,$(BIN),$@)

$(SPEC_CHECK): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/spec_check/$@.native,$(BIN),$@)

$(TLL): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tll/$@.native,$(BIN),$@)

$(THM): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/thm/$@.native,$(BIN),$@)

$(TSL): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tsl/$@.native,$(BIN),$@)

$(TSLK): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/tslk/$@.native,$(BIN),$@)

$(SOLVE): set-my-path
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $(OCAML_FLAGS) -libs $(LIBS) $@.native
	$(call copy,./_build/$(PROGS)/solve/$@.native,$(BIN),$@)

$(APPLYTAC): set-my-path
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
	@rm -f leap.odocl


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

