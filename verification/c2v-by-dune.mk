all: tnumSplitDotC.v

tnumSplitDotC.v: tnum-split.c
	clightgen -o tnumSplitDotC.v -normalize -fstruct-passing tnum-split.c
	echo '(* Generated using clightgen; see Makefile *)' > tnumSplitDotC.tmp
	echo '' >> tnumSplitDotC.tmp
	cat tnumSplitDotC.v >> tnumSplitDotC.tmp
	mv tnumSplitDotC.tmp tnumSplitDotC.v
	sed -i 's/From Coq /From Stdlib /' tnumSplitDotC.v
