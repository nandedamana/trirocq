# trirocq: Tristate Arithmetic Verified in Rocq

![Rocq stable, free](https://github.com/nandedamana/trirocq/actions/workflows/build-free.yml/badge.svg?branch=main)
![Rocq stable, nonfree CompCert](https://github.com/nandedamana/trirocq/actions/workflows/build-compcert-nonfree.yml/badge.svg?branch=main)



This project gives the soundness proof of the tnum multiplication
algorithm used in the Linux kernel eBPF verifier (specifically, the
particular version upstreamed by [this
patch](https://patchwork.kernel.org/project/netdevbpf/patch/20250826034524.2159515-1-nandakumar@nandakumar.co.in/)).
Proofs for the soundness and optimality of tnum addition are also
given, since multiplication depends on addition.  The same algorithms
are re-implemented in C with minor differences, which are then
end-to-end verified using the [Verified Software
Toolchain](https://vst.cs.princeton.edu/).

## Verification Process

1. The algorithms behind the tnum arithmetic operations from Linux are
   manually encoded in Rocq, after which their relevant properties are
   proven (like soundness and optimality).

2. Since the Linux tnum arithmetic implementation employs struct
   copying, a feature [not supported by
   VST](https://stackoverflow.com/questions/60710135/coq-vst-internal-structure-copying),
   this project provides alternative hand-written implementation that
   is verified using VST. (End-to-end verification of `tnum_sub` is
   pending, which is irrelevant as far as `tnum_mul` is concerned.)

No axioms are added by this project. One could get Rocq to (re-)verify
the proofs by building the project (which invokes Rocq's proof
checking mechanism).

## Nonfree Dependency and the Standalone Part

The VST-based verification part of this project depends on CompCert,
which is
[nonfree](https://en.wikipedia.org/wiki/Proprietary_software). However,
the algorithm verification part has no dependencies except on Rocq and
the Rocq standard library, which are fully
[free](https://www.gnu.org/philosophy/free-sw.html). Building this
project with the default parameters will ignore the VST part. To
enable it, remove the `dune` file from the project root and uncomment
the relevant lines in `trirocq.opam` (please see the GitHub CI file
that depends on nonfree components).

Please note that built either way, both the C files and the Rocq files
from this project fall under the licensing terms of this project, not
that of CompCert or VST.

## Directory Structure

- `theories/` -- modeling of bit vector (`bvec`, bounded list of `bit`s) and
  tnum (value word and mask word); Rocq encodings of tnum arithmetic operations
  and their soundness/optimality proofs.

- `writeup/` -- pen-and-paper-style proof description; no familiarity with Rocq
  assumed.

- `Ztheories/` -- uses a new version of `bvec` based on `Z` (modulo `2 ^ BITWIDTH`).
  Everything from `theories/` already ported, except `tnum_sub`.

- `verification/` -- End-to-end verification using VST.

## Building

(First, please read the section on the optional nonfree dependencies above.)

We use an opam-based build environment. See trirocq.opam for dependencies and
their versions.

TODO: move to `dune pkg`, when [the Rocq repositories become supported](https://discuss.ocaml.org/t/rocq-released-repository-with-dune-package-management/18054/2).

Earlier versions of dune do not support the `rocq` language (they
supports `coq`, but then you'll have to uninstall `rocq-*` packages
and install `coq-*` packages). If you are unable to install a recent
version of dune via opam, you can build it from the
[source](https://github.com/ocaml/dune).

## Research

The Arxiv version of our paper *Improved Tristate Multiplication With
Formalization in Rocq* can be found at
[arxiv.org/abs/2609.39009](https://arxiv.org/abs/2609.39009).

## Licensing

The file `verification/tnum.c` contains code from the Linux kernel,
licensed under GNU General Public License v2.0.

Files from this project: TODO.
