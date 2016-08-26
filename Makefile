.PHONY: all clean examples install lib links tests tools top

all: lib links tools top

bin:
	@mkdir -p bin

bin/yggdrasil: bin
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' -I src/lib src/tools/yggdrasil.native
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

tools: bin/yggdrasil

install:
	@opam list -i cats > /dev/null || opam pin add cats git://github.com/freebroccolo/ocaml-cats --yes
	@opam list -i optics > /dev/null || opam pin add optics git://github.com/freebroccolo/ocaml-optics --yes
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
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' -I src/lib tests/test00.native
	@_build/tests/test00.native

top:
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/lib/yggdrasil.cma
	@utop
