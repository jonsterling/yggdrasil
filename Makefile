BUILD_DIR=${PWD}/_build
EVAL=eval
GIT=git
GREP=grep
MENHIR_FLAGS=-use-menhir -menhir 'menhir --external-tokens Token --table'
MKDIR=mkdir -p
OCAMLBUILD=rebuild
OCAMLBUILD_JOBS=-j 0
OCAMLBUILD_FLAGS=${OCAMLBUILD_JOBS} -use-ocamlfind -no-links ${MENHIR_FLAGS}
OPAM=opam
POPD=cd ..
PUSHD=cd
REMOVE=rm -rf
SYMLINK=ln -sf
YGGDRASIL=bin/yggdrasil

.PHONY: all clean examples install lib links preinstall tests tools top

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

install: preinstall
	@$(MAKE) all
	@echo
	@echo "* installing binaries at ./bin"
	@echo
	@echo "* run './bin/yggdrasil help' for details"

lib:
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} src/lib/yggdrasil.cmxa

links: bin/yggdrasil

preinstall:
	@${OPAM} show merlin | ${GREP} 'upstream-url.*#reason.*$$' > /dev/null || ${OPAM} pin -y add merlin 'https://github.com/the-lambda-church/merlin.git#reason-0.0.1'
	@${OPAM} show merlin_extend | ${GREP} 'upstream-url.*#reason.*$$' > /dev/null || ${OPAM} pin -y add merlin_extend 'https://github.com/let-def/merlin-extend.git#reason-0.0.1'
	@${OPAM} list -i reason > /dev/null || (${MKDIR} dep && ${PUSHD} dep >&- && (${GIT} clone https://github.com/facebook/reason.git 2>&- || true) && ${PUSHD} reason >&- && ${OPAM} pin -y add reason . && ${POPD} >&- && ${POPD} >&-)
	@${OPAM} list -i cats > /dev/null || ${OPAM} pin -y add cats git://github.com/freebroccolo/ocaml-cats
	@${OPAM} list -i optics > /dev/null || ${OPAM} pin -y add optics git://github.com/freebroccolo/ocaml-optics
	@${OPAM} list -i yggdrasil > /dev/null || ${OPAM} pin -y add .

test: lib
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} -I src/lib/Yggdrasil tests/test00.native
	@${BUILD_DIR}/tests/test00.native

tools: bin/yggdrasil

top:
	@${OCAMLBUILD} ${OCAMLBUILD_FLAGS} src/lib/yggdrasil.cma
	@utop
