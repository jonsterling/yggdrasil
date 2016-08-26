# Yggdrasil

A higher-dimensional type theory based on computads

#### Building

Prerequisites:

* OCaml `4.03.0`
* OPAM `1.2.2`

```sh
$ git clone https://github.com/freebroccolo/yggdrasil
$ cd yggdrasil
$ make install
```

This will compile the project and place binaries in the local `bin` directory.

#### Running

Run the tests:

```sh
$ make test
```

This does type checking and other analysis on several examples and pretty prints the results:

```
computad:

  cells:
    [0] (∂ bool type)
    [0] (∂ list type)
    [0] (∂ nat type)
    [1] (∂ ff bool)
    [1] (∂ tt bool)
    [1] (∂ not (-> bool bool))
    [1] (∂ and (-> [bool bool] bool))
    [1] (∂ nil list)
    [1] (∂ cons (-> [nat list] list))
    [1] (∂ map (-> [(-> nat nat) list] list))
    [1] (∂ zero nat)
    [1] (∂ succ (-> nat nat))
    [1] (∂ add (-> [nat nat] nat))
    [2] (∂ and/ff/ff (-> (and ff ff) ff))
    [2] (∂ and/ff/tt (-> (and ff tt) ff))
    [2] (∂ and/tt/ff (-> (and tt ff) ff))
    [2] (∂ and/tt/tt (-> (and tt tt) tt))
    [2] (∂ not/ff (-> (not ff) tt))
    [2] (∂ not/tt (-> (not tt) ff))

term: (not ff)
type: bool

term: and
type: (-> [bool bool] bool)

term: (and ff)
type: (-> bool bool)

term: (and ff ff)
type: bool

term: map
type: (-> [(-> nat nat) list] list)

term: (map succ)
type: (-> list list)

term: (map succ nil)
type: list

term: (map (λ (∂ x nat) (succ x)) nil)
type: list

term: (λ [(∂ f (-> nat nat)) (∂ x nat)] (succ (f x)))
type: (-> [(-> nat nat) nat] nat)
```
