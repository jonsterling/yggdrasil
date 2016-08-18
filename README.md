# Yggdrasil

A higher-dimensional type theory based on computads

#### Building

Prerequisites:

* OCaml `4.03.0`
* OPAM `1.2.2`

```sh
git clone https://github.com/freebroccolo/yggdrasil
cd yggdrasil
make install
```

This will compile the project and place binaries in the local `bin` directory.

#### Running

Run the command line interface:

```sh
$ bin/yggdrasil help
```

Run an examples:

```sh
$ bin/yggdrasil parse examples/ex00.ygg
```
