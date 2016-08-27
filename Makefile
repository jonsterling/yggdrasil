BUILD_DIR=${PWD}/_build
MENHIR_FLAGS=-use-menhir -menhir 'menhir --external-tokens Token --table'
MKDIR=mkdir -p
OCAMLBUILD=rebuild
OCAMLBUILD_JOBS=-j 0
OCAMLBUILD_FLAGS=${OCAMLBUILD_JOBS} -use-ocamlfind -no-links ${MENHIR_FLAGS}
OPAM=opam
REMOVE=rm -rf
SYMLINK=ln -sf
YGGDRASIL=bin/yggdrasil

.PHONY: all clean examples install lib links tests tools top

all: lib links tools

bin:
	@${MKDIR} bin

bin/yggdrasil: bin
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} -I src/lib/Yggdrasil src/tools/yggdrasil/Main.native
	@${SYMLINK} ${BUILD_DIR}/src/tools/yggdrasil/Main.native bin/yggdrasil

clean:
	@${OCAMLBUILD} -clean
	@${REMOVE} bin

distclean: clean
	@${OPAM} pin remove cats yggdrasil

examples: tools
	@for e in $$(ls examples); do\
		printf "\n*** %s ***\n" $$e;\
		${YGGDRASIL} parse examples/$$e;\
	done

tools: bin/yggdrasil

install:
	@${OPAM} list -i cats > /dev/null || ${OPAM} pin add cats git://github.com/freebroccolo/ocaml-cats --yes
	@${OPAM} list -i optics > /dev/null || ${OPAM} pin add optics git://github.com/freebroccolo/ocaml-optics --yes
	@${OPAM} list -i yggdrasil > /dev/null || ${OPAM} pin add . --yes
	@make all
	@echo
	@echo "* installing binaries at ./bin"
	@echo
	@echo "* run './bin/yggdrasil help' for details"

lib:
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} src/lib/yggdrasil.cmxa

links: bin/yggdrasil

test: lib
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} -I src/lib/Yggdrasil tests/test00.native
	@${BUILD_DIR}/tests/test00.native

top:
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} src/lib/yggdrasil.cma
	@utop
