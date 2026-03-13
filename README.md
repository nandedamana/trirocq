# trirocq: tnum Arithmetic Verified in Rocq

This project gives the soundness proof of the tnum multiplication
algorithm used in the Linux kernel eBPF verifier (specifically, the
particular version upstreamed by [this
patch](https://patchwork.kernel.org/project/netdevbpf/patch/20250826034524.2159515-1-nandakumar@nandakumar.co.in/)).
Proofs for the soundness and optimality of tnum addition are also
given, since multiplication depends on addition.

## Verification Process

The algorithms used in the kernel are manually encoded in Rocq, and
then they are verified against the specification of soundness (and
optimality in the case of addition). Encoding being manual is
considered non-problematic since the code being verified is small.

This project does not produce any executable component; it consists
only of proofs, and one could get Rocq to verify the proofs by
building the project (which invokes Rocq's proof checking mechanism).

## Standalone Nature

The project depends only on the Rocq standard library. No axioms are
used (you may find one if you perform a search, but that's for an
experimental proof of tnum subtraction, which does not affect tnum
multiplication, our primary goal). Even the custom binary (i.e., not
tristate) arithmetic routines defined as part of the process are
proven to be sound.

## Building

Following is the build environment we use:

- `rocq-core` (9.1.1), `rocq-stdlib` (9.0.0) from opam

- Latest version of Dune built from the
  [source](https://github.com/ocaml/dune) using `make release` at
  commit `bb781c774a17438e52720dff0d5f5245c6a6b86a`

With the appropriate opam environment loaded (using `eval $(opam
env)`) and Dune built at say, `PATH_TO_DUNE`, one could build this
project using:

```
PATH_TO_DUNE/dune.exe build
```

The reason we recommend building Dune from source is because the
latest version of Dune available in opam as of writing this does not
support the `rocq` language (it supports `coq`, but then you'll have
to uninstall `rocq-*` packages and install `coq-*` packages). If your
version of Dune from opam doesn't have this issue, there is no need to
build it from source.
