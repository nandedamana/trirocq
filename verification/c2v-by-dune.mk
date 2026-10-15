tnumPtrDotC.v: tnum-ptr.c
	clightgen -o "$@" -normalize -fstruct-passing "$<"
	echo '(* Generated using clightgen; see Makefile *)' > "$@".tmp
	echo '' >> "$@".tmp
	cat "$@" >> "$@".tmp
	mv "$@".tmp "$@"
	sed -i 's/From Coq /From Stdlib /' "$@"
