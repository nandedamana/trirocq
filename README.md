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

We use an opam-based build environment with:

- `rocq-core` (9.1.1)
- `rocq-runtime` (9.1.1)
- `rocq-stdlib` (9.0.0)
- `dune` (3.22.2)

Earlier versions of dune do not support the `rocq` language (they
supports `coq`, but then you'll have to uninstall `rocq-*` packages
and install `coq-*` packages). If you are unable to install a recent
version of dune via opam, you can build it from the
[source](https://github.com/ocaml/dune).
