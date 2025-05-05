(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Vector.

Variant bit := zero | one.

Definition bit_and (x y : bit) :=
  match x, y with
  | one, one => one
  | _, _ => zero
  end.

(* TODO REM *)
Definition bit_or (x y : bit) :=
  match x, y with
  | zero, zero => zero
  | _, _ => one
  end.

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

Require Import Lia.
Lemma ltprv {i} {n} : S i < n -> i < n.
  lia.
Qed.

(* TODO replace v64_prvcarry with this *)
(* Calculating cin in difficult; TODO create a wrapper that models the propagation *)
(* Issue: The term "ltprv hidx" has type "i < SIZE" while it is expected to have type "p + 1 < SIZE" *)
(*
Fixpoint v64_prvcarry2 (x y : v64) {i} (hidx : (i + 1) < SIZE) :=
  let a := v64_ith x (ltprv hidx) in
  let b := v64_ith y (ltprv hidx) in
  let c := match i with
           | 0 => zero
           | S p => @v64_prvcarry2 x y p (ltprv hidx)
           end in
  bit_or (bit_or (bit_and a b) (bit_and a c)) (bit_and b c).
*)

Definition p_from_pltq {p q} (pltq : p < q) := p.

(* Uses the "convoy pattern" to solve the issue noted above
 * - http://adam.chlipala.net/cpdt/html/MoreDep.html
 * - https://stackoverflow.com/questions/32060556/convoy-pattern-and-match-involving-inequality?rq=3
 *)
(* Carry due to the addition of bits at position (i - 1); 0 for i = 0 *)
Fixpoint v64_prvcarry (x y : v64) {i} (hidx : i < SIZE) : bit :=
  match i return i < SIZE -> bit with
  | 0 => fun _ => zero
  | S i' => fun hidx => let a := v64_ith x (ltprv hidx) in
                        let b := v64_ith y (ltprv hidx) in
                        let cin := v64_prvcarry x y (ltprv hidx) in
                        bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin)
  end hidx.

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
 *)

Definition ingamma (x : v64) (T : otnum.t) : Prop :=
    forall i (hidx : i < SIZE),
      (forall b, otnum.ith T hidx = Some b -> v64_ith x hidx = b).

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

(*
0 0 0
0 1 0
0 x 0
1 0 0
1 1 1
1 x x
x 0 0
x 1 x
x x x
*)
Definition obit_and (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_and p q)
  | _, _ => None
  end.

(*
0 0 0
0 1 1
0 x x
1 0 1
1 1 1
1 x 1
x 0 x
x 1 1
x x x
*)
Definition obit_or (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_or p q)
  | Some one, _ => Some one
  | _, Some one => Some one
  | _, _ => None
  end.

Fixpoint otnum_prvcarry (P Q : otnum.t) {i} (hidx : i < SIZE) : option bit :=
  match i return i < SIZE -> option bit with
  | 0 => fun _ => Some zero
  | S i' => fun hidx => let a := otnum.ith P (ltprv hidx) in
                        let b := otnum.ith Q (ltprv hidx) in
                        let cin := otnum_prvcarry P Q (ltprv hidx) in
                        obit_or (obit_or (obit_and a b) (obit_and a cin)) (obit_and b cin)
  end hidx.

(* Analogue of v64_fulladd_result *)
Axiom otnum_fulladd_result : forall (P Q R : otnum.t), R = otnum_add P Q -> forall i (hidx : i < SIZE), otnum.ith R hidx = obit_xor (otnum_prvcarry P Q hidx) (obit_xor (otnum.ith P hidx) (otnum.ith Q hidx)).

Lemma and_obit_bit a b c : obit_and (Some a) (Some b) = Some c -> bit_and a b = c.
  unfold obit_and. intro H. injection H. auto.
Qed.

Lemma or_obit_bit a b c : obit_or (Some a) (Some b) = Some c -> bit_or a b = c.
  unfold obit_or. unfold bit_or. destruct a.
  all: intro H. injection H. auto.
  injection H. auto.
Qed.

Ltac destruct_bit :=
  match goal with
  | [ b : option bit |- _ ] => destruct b
  | [ b : bit |- _ ] => destruct b
  end.

(* TODO rename *)
Ltac crush1 := compute; easy.
Ltac crush2 := 
  match goal with
  | [ |- _ -> exists p q, Some ?x = Some p /\ Some ?y = Some q /\ bit_and p q = ?c ] => exists x
  | [ |- exists q, _ /\ Some ?x = Some q /\ _ ] => exists x
  end.

Lemma obit_and_imp x y c : obit_and x y = Some c -> exists p q, x = Some p /\ y = Some q /\ bit_and p q = c.
  unfold obit_and. repeat destruct_bit. all: repeat crush1 || crush2.
Qed.

Lemma obit_and_imp2 a b c : obit_and (Some a) (Some b) = Some c -> bit_and a b = c.
  unfold obit_and. repeat destruct_bit. all: repeat crush1 || crush2.
Qed.

Lemma obit_or_imp x y c : obit_or x y = Some c -> x = Some c \/ y = Some c.
  unfold obit_or. repeat destruct_bit. all: compute; auto.
Qed.

Ltac assert_and_rel H :=
  match goal with
    | [ H : obit_and ?x ?y = Some _ |- bit_and ?p ?q = _ ] =>
        assert (forall x', x = Some x' -> p = x');
        assert (forall y', y = Some y' -> q = y')
  end.

Ltac assert_or_rel H :=
  match goal with
    | [ H : obit_or ?x ?y = Some _ |- bit_or ?p ?q = _ ] =>
        assert (forall x', x = Some x' -> p = x');
        assert (forall y', y = Some y' -> q = y')
  end.

(* TODO REM *)
Lemma assert_or_rel x y c p q : obit_or x y = Some c -> bit_or p q = c.
  intro H.
  assert_or_rel H.
Admitted.

Ltac destruct_oband H :=
  let H' := fresh "H'" in
  let x := fresh "x" in
  let hx := fresh "hx" in
  let hx' := fresh "hx'" in
  assert (H' := H); apply obit_and_imp in H';
  destruct H' as (x & hx); remember hx as hx'; destruct hx'.

Ltac destruct_obor H :=
  let H' := fresh "H'" in
  let h1 := fresh "h1" in
  let h2 := fresh "h2" in
  assert (H' := H); apply obit_or_imp in H'; destruct H' as [h1 | h2];
  try destruct_obor h1; try destruct_oband h1; try destruct_obor h2; try destruct_oband h2.
(* TODO REM
  destruct H' as (x & hx); remember hx as hx'; destruct hx'. *)

(* TODO REM *)
Goal forall a b c, obit_or a b = Some c -> exists d, a = Some d \/ b = Some d.
  intros a b c H.
  destruct_obor H; exists c; auto.
Qed.

Ltac ingam_rel P :=
  match goal with
  | [ H : ingamma ?x P, hidx : ?i < SIZE |- _ ] =>
    let H1 := fresh "H1" in
    assert (H1 : forall b, otnum.ith P (ltprv hidx) = Some b -> v64_ith x (ltprv hidx) = b); auto
  end.

Ltac crush_invalid_and := 
  match goal with
  | [ H : bit_and zero zero = one |- _ ] => unfold bit_and in H; simpl in H; try easy
  | [ H : bit_and zero one = one |- _ ] => unfold bit_and in H; simpl in H; try easy
  | [ H : bit_and one zero = one |- _ ] => unfold bit_and in H; simpl in H; try easy
  | [ H : bit_and one one = zero |- _ ] => unfold bit_and in H; simpl in H; try easy
  end.

(* TODO Can I combine crush4_0 and crush4_1? Problem: when the context has both hypos, one masks the other. *)
(* If P is not taken, `otnum.ith Q` would mask `otnum.ith P` if the context has both. *)
Ltac crush4_0 H P :=
  match goal with
  | [ h : otnum.ith P _ = Some _ |- _ ] => repeat rewrite h in H; simpl in H; try easy
  | _ => idtac
  end.

Ltac crush4_1 H P Q :=
  match goal with
  | [ h : otnum_prvcarry P Q _ = Some _ |- _ ] => repeat rewrite h in H; simpl in H; try easy
  | _ => idtac
  end.

Ltac crush4 H P Q := try crush_invalid_and; crush4_0 H P; crush4_0 H Q; crush4_1 H P Q; simpl in H; try easy; try auto.

Lemma test_crush4 P Q b {i} (hidx : S i < SIZE) : otnum.ith P hidx = Some b /\ otnum_prvcarry P Q (ltprv hidx) = Some b -> False.
  intros. destruct H.
  assert (H1 : otnum_prvcarry P Q (ltprv hidx) = None /\ otnum.ith P hidx = None -> True). intro H'. exact I.
  crush4 H1 P Q.
Admitted.

Ltac rewrite_obit_and :=
  match goal with
  | [ h1 : ?P = _, h2 : obit_and ?P _ = _ |- _ ] => repeat rewrite h1 in h2
  | [ h1 : ?P = _, h2 : obit_and _ ?P = _ |- _ ] => repeat rewrite h1 in h2
  end.

Ltac crush_invalid_obit_and :=
  match goal with
  | [ h : obit_and None _ = Some _ |- _ ] => unfold obit_and in h; simpl in h; easy
  | [ h : obit_and _ None = Some _ |- _ ] => unfold obit_and in h; simpl in h; easy
  end.

(* Destructs unknown terms only *)
Ltac destruct_Pi P :=
  match goal with
  | [ _ : otnum.ith P ?hidx = Some _ |- _ ] => idtac
  | _ => let b0 := fresh "b0" in
         let b1 := fresh "b1" in
         match goal with
         | [ Pimpx : forall b : bit, otnum.ith P ?hidx = Some b -> v64_ith ?x ?hidx = b |- _ ] =>
             destruct (otnum.ith P hidx) as [b0|b1]; try rewrite Pimpx with (b := b0)
         end
  end.

Ltac destruct_Ci P Q :=
  match goal with
  | [ _ : otnum_prvcarry P Q ?hidx = Some _ |- _ ] => idtac
  | _ => let b0 := fresh "b0" in
         let b1 := fresh "b1" in
         match goal with
         | [ Pimpx : forall b : bit, otnum_prvcarry P Q ?hidx = Some b -> v64_prvcarry ?x ?y ?hidx = b |- _ ] =>
             destruct (otnum_prvcarry P Q hidx) as [b0|b1]; try rewrite Pimpx with (b := b0)
         end
  end.

(*
Ltac rewrite_crush H :=
  match goal with
  | [ H : bit_and zero zero = one |- _ ] => unfold bit_and in H; simpl in H; easy
*)

Ltac destruct_conj3 :=
  let x' := fresh "x'" in
  let y' := fresh "y'" in
  let z' := fresh "z'" in
  match goal with
  | [ h1 : ?x /\ ?y /\ ?z |- _ ] => destruct h1 as (x' & y' & z')
  end.

Ltac intro_obit_imp_bit :=
  let H := fresh "H" in
  match goal with
  | [ |- obit_and _ _ = Some ?x -> bit_and _ _ = ?x ] =>
      intro H; try assert_or_rel H; try assert_and_rel H; auto
  | [ |- obit_or _ _ = Some ?x -> bit_or _ _ = ?x ] =>
      intro H; try assert_or_rel H; try assert_and_rel H; auto
  end.

Ltac intro_forall_obit_imp_bit :=
  let b := fresh "b" in
  match goal with
  | [ |- forall x, obit_and _ _ = Some x -> bit_and _ _ = x ] =>
      intro b; intro_obit_imp_bit
  | [ |- forall x, obit_or _ _ = Some x -> bit_or _ _ = x ] =>
      intro b; intro_obit_imp_bit
  end.

(* TODO REM
Lamma test_intro_obit_imp_bit : forall x, obit_or (Some one) (Some one) -> 
 *)

Ltac crush13 := (* TODO rename meaningfully *)
  match goal with
    | [ H6 : obit_and ?x ?y = Some ?p,
        H8 : forall y', ?y = Some y' -> ?z = y' |-
                          obit_and ?x (Some ?z) = Some ?p ] => try rewrite H8 in H6; try assumption
  end.
(*
  H6 : obit_and (Some one) (otnum.ith Q (ltprv hidx)) = Some zero
  H7 : forall x' : bit, Some one = Some x' -> v64_ith x (ltprv hidx) = x'
  H8 : forall y' : bit, otnum.ith Q (ltprv hidx) = Some y' -> v64_ith y (ltprv hidx) = y'
  ============================
  obit_and (Some one) (Some (v64_ith y (ltprv hidx))) = Some zero
*)

(* TODO prove *)
Lemma matching_carry (P Q : otnum.t) (x y : v64) :
  ingamma x P /\ ingamma y Q ->
  forall i (hidx : i < SIZE),
    (forall b, otnum_prvcarry P Q hidx = Some b -> v64_prvcarry x y hidx = b).

  intros ingamXY i hidx.
  induction i.
  - intro b. unfold otnum_prvcarry. unfold v64_prvcarry. intro H. injection H. auto.
  - intro b.

    assert (H1 : forall b, otnum_prvcarry P Q (ltprv hidx) = Some b -> v64_prvcarry x y (ltprv hidx) = b).
    apply IHi.

    destruct ingamXY as (ingamX & ingamY).

    (* TODO subst. the new names OR remove altogether since assert_and_rel creates these hypos *)
    ingam_rel Q. assert (Qimpy := H0).
    ingam_rel P. assert (Pimpx := H2).
    
    unfold otnum_prvcarry. fold otnum_prvcarry.
    unfold v64_prvcarry. fold v64_prvcarry.

    intro_obit_imp_bit.
    intro_forall_obit_imp_bit.
    destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    intro_forall_obit_imp_bit.
    intro_forall_obit_imp_bit.
    destruct_Pi P; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    intro_forall_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    intro_forall_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    destruct (v64_ith y (ltprv hidx)); simpl; auto.
    
    intro_forall_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.
    
    destruct (v64_ith y (ltprv hidx)); simpl; auto.
    destruct (v64_ith x (ltprv hidx)); simpl; auto.
Qed.

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

