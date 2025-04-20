(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Vector.

Variant bit := zero | one.

(* TODO switch to 64 after testing *)
Definition SIZE := 4.
Definition v64 := Vector.t bit SIZE.

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t := cons (v : v64) (m : v64) : t.
End tnum.

Module otnum.
  (* The Kernel representation technically allows four values per trit,
   * but forbids the combination {.v = 1, .m = 1} by convention (i.e.,
   * the value bit should be reset if the mask is set). The representation
   * we use here is a true tristate one, ruling out illegal constructions
   * in any intermediate steps.
   *)
  
  Definition t := Vector.t (option bit) SIZE.
  Definition nil := Vector.nil (option bit).
  Definition cons := Vector.cons (option bit).
  Arguments cons _ {_} _.

  Example vt10 := (cons (Some one) (cons (Some zero) (cons (Some one) (cons (Some zero) nil)))).
  Example vt3  := (cons (Some zero) (cons (Some zero) (cons (Some one) (cons (Some one) nil)))).
End otnum.

(* TODO REM; wrote down just as a reference for the usage of nth; main point: I do not have to generate proof for `i < SIZE`. *)
(* TODO take v.length instead of SIZE *)
Goal forall (v : otnum.t) i (hidx : i < SIZE), let ith := Vector.nth v (Fin.of_nat_lt hidx) in ith = Some one \/ ith = Some zero \/ ith = None.
  intros v i hidx.
  destruct (Vector.nth v (Fin.of_nat_lt hidx)).
  destruct b; auto.
  auto.
Qed.

(* TODO from Harisankar et al. *)
