(lang dune 3.22)
(using rocq 0.11)

(name trirocq)

(source
 (gitlab nandakumariitpkd/trirocq))

(authors "Nandakumar Edamana <nandakumar@nandakumar.co.in>")

(maintainers "Nandakumar Edamana <nandakumar@nandakumar.co.in>")

(license GPL-3.0-only)

(package
 (name trirocq)
 (synopsis "trirocq: tnum Arithmetic Verified in Rocq")
 (description "Verified implementation of tnum arithmetic operations. Tnum, or tristate number, is an abstract domain used in the linux kernel eBPF verifier.")
 (depends ocaml)
 (tags
  ("tnum" "linux" "ebpf" "abstract interpretation")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
