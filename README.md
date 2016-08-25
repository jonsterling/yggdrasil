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

This does type checking and other analysis on several examples and pretty prints the results.
