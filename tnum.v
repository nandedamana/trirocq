(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Vector.

Variant bit := zero | one.

(* TODO switch to 64 after testing *)
Definition SIZE := 4.

Section tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)

  Definition tnum_v := Vector.t bit SIZE.
  Definition tnum_m := Vector.t bit SIZE.
  Variant tnum := tcons : tnum_v -> tnum_m -> tnum.
End tnum.

Section vtnum.
  (* The Kernel representation technically allows four values per trit,
   * but forbids the combination {.v = 1, .m = 1} by convention (i.e.,
   * the value bit should be reset if the mask is set). The representation
   * we use here is a true tristate one.
   *)
  
  Definition vtnum := Vector.t (option bit) SIZE.
  Definition vtnil := Vector.nil (option bit).
  Definition vtcons := Vector.cons (option bit).
  Arguments vtcons _ {_} _.

  Example vt10 : vtnum := (vtcons (Some one) (vtcons (Some zero) (vtcons (Some one) (vtcons (Some zero) vtnil)))).
  Example vt3 : vtnum := (vtcons (Some zero) (vtcons (Some zero) (vtcons (Some one) (vtcons (Some one) vtnil)))).
End vtnum.
