(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Vector.

Variant bit := zero | one.

Definition bit_xor (x y : bit) :=
  match x, y with
  | zero, zero => zero
  | zero, one => one
  | one, zero => one
  | one, one => zero
  end.

(* TODO module for v64 *)
(* TODO switch to 64 after testing *)
Definition SIZE := 4.
Definition v64 := Vector.t bit SIZE.
Definition v64_ith (v : v64) {i} (hidx : i < SIZE) :=
  Vector.nth v (Fin.of_nat_lt hidx).

Axiom v64_add : v64 -> v64 -> v64.

(* Carry due to the addition of bits at position (i - 1); 0 for i = 0 *)
(* TODO define? *)
Axiom v64_prvcarry : forall (x y : v64) {i} (hidx : i < SIZE), bit.

Axiom v64_fulladd_result : forall (x y z : v64), z = v64_add x y -> forall i (hidx : i < SIZE), v64_ith z hidx = bit_xor (v64_prvcarry x y hidx) (bit_xor (v64_ith x hidx) (v64_ith y hidx)).

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t := cons (v : v64) (m : v64) : t.

  (* TODO rem if unused *)
  Definition ith_v (tn : t) {i} (hidx : i < SIZE) :=
    match tn with
      cons v _ => Vector.nth v (Fin.of_nat_lt hidx)
    end.

  Definition ith_m (tn : t) {i} (hidx : i < SIZE) :=
    match tn with
      cons _ m => Vector.nth m (Fin.of_nat_lt hidx)
    end.
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

  Definition ith (v : t) {i} (hidx : i < SIZE) :=
    Vector.nth v (Fin.of_nat_lt hidx).

  (* TODO reverse the representation so that i=0 would mean LSB? *)
  Example vt10 := (cons (Some one) (cons (Some zero) (cons (Some one) (cons (Some zero) nil)))).
  Example vt3  := (cons (Some zero) (cons (Some zero) (cons (Some one) (cons (Some one) nil)))).
End otnum.

(* TODO REM; wrote down just as a reference for the usage of nth; main point: I do not have to generate proof for `i < SIZE`. *)
Goal forall (v : otnum.t) i (hidx : i < SIZE), let ith := Vector.nth v (Fin.of_nat_lt hidx) in ith = Some one \/ ith = Some zero \/ ith = None.
  intros v i hidx.
  destruct (Vector.nth v (Fin.of_nat_lt hidx)).
  destruct b; auto.
  auto.
Qed.

(* TODO REM?
(* I learned this way of representing sets from:
 * https://github.com/rocq-community/coq-100-theorems/blob/master/inclusionexclusion.v
 * (Must be a standard technique, though.)
 *)

Definition v64set := v64 -> bool.
Axiom alpha : v64set -> otnum.t.
Axiom gamma : otnum.t -> v64set.

Definition ingamma (x : v64) (T : otnum.t) := gamma T x = true.

(* The following two axioms sort of mirror Harishankar et al. *)

(* ith trit is Some b in T => ith bit is b in the .v of every c in gamma(T) *)
Axiom TODO1 : forall (T : otnum.t) (i : nat) (hidx : i < SIZE) (b : bit),
    otnum.ith T hidx = Some b -> forall x, ingamma x T -> v64_ith x hidx = b.

(* ith trit is None in T => ith bit is 0 or 1 in the .v of every c in gamma(T) *)
Axiom TODO2 : forall (T : otnum.t) (i : nat) (hidx : i < SIZE),
    otnum.ith T hidx = None ->
    forall x, ingamma x T -> v64_ith x hidx = zero \/ v64_ith x hidx = one.
*)

(* TODO replace the above two with the following? *)
Definition ingamma (x : v64) (T : otnum.t) : Prop :=
    forall i (hidx : i < SIZE),
      (forall b, otnum.ith T hidx = Some b -> v64_ith x hidx = b).
(* TODO confirm: unnecessary since this is essentially a don't care case.
      /\
        (otnum.ith T hidx = None -> v64_ith x hidx = zero \/ v64_ith x hidx = one).
*)

(* On my own *)
(* We need to define otnum addition with the following properties:
 * 1. Soundness: the result of adding abstract numbers P and Q include the results
 *    of adding any concrete p and q (written less formally for simplicity).
 * 2. TODO optimality:
 *)

(* Define an otnum_add that is trivially sound *)
(* TODO REM; proving this is not easy (if possible at all), despite it being
 * trivially sound; I should go for the relationship method.

Definition otnum_add (X Y : otnum.t) :=
  otnum.cons None (otnum.cons None (otnum.cons None (otnum.cons None (otnum.nil)))).
*)

Axiom otnum_add : otnum.t -> otnum.t -> otnum.t.

(*
0 0 0
0 1 1
0 x x
1 0 1
1 1 0
1 x x
x 0 x
x 1 x
x x x
*)
Definition obit_xor (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_xor p q)
  | _, _ => None
  end.

(* TODO REM? *)
Lemma obit_xor_mu (x y : option bit) : (x = None \/ y = None) -> obit_xor x y = None.
  intros H. destruct H as [ hx | hy ].
  unfold obit_xor. rewrite hx. reflexivity.
  unfold obit_xor. rewrite hy.
  destruct x. destruct b; reflexivity. reflexivity.
Qed.

Lemma obit_xor_mu_right (x : option bit) : obit_xor x None = None.
  unfold obit_xor. destruct x. destruct b.
  reflexivity. reflexivity. reflexivity.
Qed.
  
Lemma obit_xor_mu_left (y : option bit) : obit_xor None y = None.
  unfold obit_xor. destruct y; reflexivity.
Qed.

Axiom otnum_prvcarry : forall (P Q : otnum.t) {i} (hidx : i < SIZE), option bit.

(* Analogue of v64_fulladd_result *)
Axiom otnum_fulladd_result : forall (P Q R : otnum.t), R = otnum_add P Q -> forall i (hidx : i < SIZE), otnum.ith R hidx = obit_xor (otnum_prvcarry P Q hidx) (obit_xor (otnum.ith P hidx) (otnum.ith Q hidx)).

(* TODO prove *)
Lemma matching_carry (P Q : otnum.t) (x y : v64) :
  ingamma x P /\ ingamma y Q ->
  forall i (hidx : i < SIZE),
      (forall b, otnum_prvcarry P Q hidx = Some b -> v64_prvcarry x y hidx = b)(* /\
        otnum_prvcarry P Q hidx = None -> (let carry := v64_prvcarry x y hidx in carry = zero \/ carry = one)*).
Admitted.

(* Mirrors Harishankar et al. except for dropping `wellformed` *)
Lemma otnum_add_sound (P Q R : otnum.t) (x y : v64) :
  R = otnum_add P Q /\ ingamma x P /\ ingamma y Q -> ingamma (v64_add x y) R.
Proof.
  intro H.
  destruct H as (HR & ingamX & ingamY).

  assert (hxy : ingamma x P /\ ingamma y Q). split; trivial.

  unfold ingamma. intros i hidx b Hri.
  unfold ingamma in ingamX.
  unfold ingamma in ingamY.
  apply otnum_fulladd_result with (i := i) (hidx := hidx) in HR.
  rewrite HR in Hri.

  (* Get rid of the `= None` cases *)
  assert (hpi : exists bp, otnum.ith P hidx = Some bp).
  destruct (otnum.ith P hidx). destruct (otnum.ith Q hidx).
  exists b0. reflexivity.
  rewrite obit_xor_mu_right in Hri. easy.
  rewrite obit_xor_mu_left in Hri. rewrite obit_xor_mu_right in Hri. easy.

  (* TODO dedeup and move out *)
  assert (hqi : exists bq, otnum.ith Q hidx = Some bq).
  destruct (otnum.ith P hidx). destruct (otnum.ith Q hidx).
  exists b1. reflexivity.
  rewrite obit_xor_mu_right in Hri. easy.
  rewrite obit_xor_mu_left in Hri. rewrite obit_xor_mu_right in Hri. easy.

  assert (hci : exists bc, otnum_prvcarry P Q hidx = Some bc).
  destruct (otnum_prvcarry P Q hidx).
  exists b0. reflexivity.
  rewrite obit_xor_mu_left in Hri. easy.
  
  destruct hpi as (bp & hbp).
  destruct hqi as (bq & hbq).
  destruct hci as (bc & hbc).
  
  assert (hcarry : forall b, otnum_prvcarry P Q hidx = Some b -> v64_prvcarry x y hidx = b).
  apply matching_carry. assumption.

  rewrite v64_fulladd_result with (x := x) (y := y).

  rewrite ingamX with (b := bp).
  rewrite ingamY with (b := bq).
  rewrite hcarry with (b := bc).

  rewrite hbp in Hri. rewrite hbq in Hri. rewrite hbc in Hri.
  unfold obit_xor in Hri. injection Hri. trivial.

  exact hbc. exact hbq. exact hbp. trivial.
Qed.

