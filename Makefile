.PHONY: all clean examples install lib links tests tools

all: lib links tools

bin:
	@mkdir -p bin

bin/yggdrasil: bin tools
	@ln -sf ${PWD}/_build/src/tools/yggdrasil.native bin/yggdrasil

clean:
	@ocamlbuild -clean
	@rm -rf bin

distclean: clean
	@opam pin remove cats yggdrasil

examples: tools
	@for e in $$(ls examples); do\
		printf "\n*** %s ***\n\n" $$e;\
		bin/yggdrasil parse examples/$$e;\
	done

tools: lib
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' -I src/lib src/tools/yggdrasil.native

install:
	@opam list -i cats > /dev/null || opam pin add cats git://github.com/freebroccolo/ocaml-cats --yes
	@opam list -i yggdrasil > /dev/null || opam pin add . --yes
	@make all
	@echo
	@echo "* installing binaries at ./bin"
	@echo
	@echo "* run './bin/yggdrasil help' for details"

lib:
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/lib/yggdrasil.cmxa

links: bin/yggdrasil

test: lib
	@ocamlbuild -j 0 -use-ocamlfind -no-links -I src tests/test00.native
	@_build/tests/test00.native
