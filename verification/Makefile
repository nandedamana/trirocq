tnum.v: tnum.c
	clightgen -o tnumDotC.v -normalize -fstruct-passing tnum.c
	echo '(* Generated using clightgen; see Makefile *)' > tnumDotC.tmp
	echo '' >> tnumDotC.tmp
	cat tnumDotC.v >> tnumDotC.tmp
	mv tnumDotC.tmp tnumDotC.v
	sed -i 's/From Coq /From Stdlib /' tnumDotC.v
