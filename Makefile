OCAMLBUILD=ocamlbuild
OPAM=opam

.PHONY: all clean examples install lib links tests tools top

all: lib links tools top

bin:
	@mkdir -p bin

bin/yggdrasil: bin
	@${OCAMLBUILD} -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' -I src/lib src/tools/yggdrasil.native
	@ln -sf ${PWD}/_build/src/tools/yggdrasil.native bin/yggdrasil

clean:
	@${OCAMLBUILD} -clean
	@rm -rf bin

distclean: clean
	@${OPAM} pin remove cats yggdrasil

examples: tools
	@for e in $$(ls examples); do\
		printf "\n*** %s ***\n\n" $$e;\
		bin/yggdrasil parse examples/$$e;\
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
	@${OCAMLBUILD} -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/lib/yggdrasil.cmxa

links: bin/yggdrasil

test: lib
	@${OCAMLBUILD} -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' -I src/lib tests/test00.native
	@_build/tests/test00.native

top:
	@${OCAMLBUILD} -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/lib/yggdrasil.cma
	@utop
