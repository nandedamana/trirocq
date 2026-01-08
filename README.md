# trirocq: tnum Arithmetic Verified in Rocq

This project uses Dune as the build system. As of writing this, the
latest version of Dune (v3.20.2) available from opam does not support
the `rocq` language (it supports `coq`, but then you'll have to
uninstall `rocq-*` packages and install `coq-*` packages). If your
version of Dune has the same issue, you can clone [their GitHub
repository](https://github.com/ocaml/dune) and do a `make release`
(please make sure to use `CLONED_PATH/dune.exe` instead of `dune`
then). It builds without much hassle.
