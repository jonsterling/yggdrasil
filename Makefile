.PHONY: all clean examples index install lib links tests

all: index lib links

bin:
	@mkdir -p bin

bin/yggdrasil: bin index
	@ln -sf ${PWD}/_build/src/index.native bin/yggdrasil

examples: index
	@for e in $$(ls examples); do\
		printf "\n*** %s ***\n\n" $$e;\
		_build/src/index.native parse examples/$$e;\
	done

index: lib
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/index.native

install:
	@opam list -i cats > /dev/null || opam pin add cats git://github.com/freebroccolo/ocaml-cats --yes
	@opam list -i yggdrasil > /dev/null || opam pin add . --yes
	@make all

lib:
	@ocamlbuild -j 0 -use-ocamlfind -no-links -use-menhir -menhir 'menhir --external-tokens Token --table' src/Yggdrasil.cmxa

links: bin/yggdrasil

test: lib
	@ocamlbuild -j 0 -use-ocamlfind -no-links -I src tests/test00.native
	@_build/tests/test00.native

clean:
	@ocamlbuild -clean
	@rm -rf bin

distclean: clean
	@opam pin remove cats yggdrasil
