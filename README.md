# Yggdrasil

[![Travis Build Status](https://travis-ci.org/freebroccolo/yggdrasil.svg?branch=master)](https://travis-ci.org/freebroccolo/yggdrasil)

A higher-dimensional type theory based on computads

#### Building

Prerequisites:

* OPAM `1.2.2`
* OCaml `4.02.3`

```sh
$ git clone https://github.com/freebroccolo/yggdrasil
$ cd yggdrasil
$ make install
```

This will compile the project and place binaries in the `./bin` directory.

#### Running

Run the examples:

```sh
$ ./bin/yggdrasil parse examples/ex00.ygg
```

This will parse the example `ex00.ygg`, do some analysis, and print the result
(see below). You can also run all of the examples with `make examples`.

<details>
  <summary>`$ make example`</summary>
<pre>
term: bool
type: type

term: (not ff)
type: bool

term: (not tt)
type: bool

term: (and ff ff)
type: bool

term: (and (and tt tt) ff)
type: bool

term: (and (and tt tt) tt)
type: bool

term: (and (and tt tt) (not ff))
type: bool

term: and/eta
type: (λ [(∂ x bool) (∂ y bool)] (and x y))

term: (λ (∂ x bool) (not x))
type: (-> bool bool)

term: (λ [(∂ x bool) (∂ y bool)] (and x y))
type: (-> [bool bool] bool)

term: (λ (∂ x bool) (λ (∂ y bool) (and x y)))
type: (-> [bool bool] bool)

computad:

  cells:
    [0] (∂ bool type)
    [1] (∂ ff bool)
    [1] (∂ tt bool)
    [1] (∂ not (-> bool bool))
    [1] (∂ and (-> [bool bool] bool))
    [2] (∂ and/eta (λ [(∂ x bool) (∂ y bool)] (and x y)))
    [2] (∂ and/ff/ff (-> (and ff ff) ff))
    [2] (∂ and/ff/tt (-> (and ff tt) ff))
    [2] (∂ and/tt/ff (-> (and tt ff) ff))
    [2] (∂ and/tt/tt (-> (and tt tt) tt))
    [2] (∂ not/ff (-> (not ff) tt))
    [2] (∂ not/tt (-> (not tt) ff))

  rules:
    and ≜
      [ff, ff] => ff
      [ff, tt] => ff
      [tt, ff] => ff
      [tt, tt] => tt
    not ≜
      ff => tt
      tt => ff
</pre>
</details>

#### Contributing

If you'd like to help, the best place to start are issues with the following labels:

* [`E-easy`](https://github.com/freebroccolo/yggdrasil/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy)
* [`E-help-wanted`](https://github.com/freebroccolo/yggdrasil/issues?q=is%3Aissue+is%3Aopen+label%3AE-help-wanted)

We follow the issue labels used by Rust which are described in detail
[here](https://github.com/rust-lang/rust/blob/master/CONTRIBUTING.md#issue-triage).

If you find something you want to work on, please leave a comment so that others
can coordinate their efforts with you. Also, please don't hesitate to open a new
issue if you have feedback of any kind.
