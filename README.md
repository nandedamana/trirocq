# trirocq: Tristate Arithmetic Verified in Rocq

![Rocq stable, free](https://github.com/nandedamana/trirocq/actions/workflows/build-free.yml/badge.svg?branch=main)
![Rocq stable, nonfree CompCert](https://github.com/nandedamana/trirocq/actions/workflows/build-compcert-nonfree.yml/badge.svg?branch=main)



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

NOTE: There is work in progress to verify the C code using CompCert/VST.
This requires nonfree CompCert, which is disabled in the build
scripts/metadata by default. Algorithm verification can still be done
without CompCert.

## Directory Structure

- `theories/` -- modeling of bit vector (`bvec`, bounded list of `bit`s) and
  tnum (value word and mask word); Rocq encodings of tnum arithmetic operations
  and their soundness/optimality proofs.

- `writeup/` -- pen-and-paper-style proof description; no familiarity with Rocq
  assumed.

- `Ztheories/` -- experimental development of `bvec` based on `Z` (modulo `2 ^
  BITWIDTH`).

## Building

We use an opam-based build environment. See trirocq.opam for dependencies and
their versions.

TODO: move to `dune pkg`, when [the Rocq repositories become supported](https://discuss.ocaml.org/t/rocq-released-repository-with-dune-package-management/18054/2).

Earlier versions of dune do not support the `rocq` language (they
supports `coq`, but then you'll have to uninstall `rocq-*` packages
and install `coq-*` packages). If you are unable to install a recent
version of dune via opam, you can build it from the
[source](https://github.com/ocaml/dune).
