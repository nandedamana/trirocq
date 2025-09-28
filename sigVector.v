(* Started 2025-09-24 *)

From Stdlib Require Import Lia. (* TODO move (or remove if unused) *)
From Stdlib Require Import List.
From Stdlib Require Import Program.

Definition ltprv {m} {n} (h : S m < n) := PeanoNat.Nat.lt_succ_l m n h.
Definition ltS {m} {n} (hlt : m < n) := (proj1 (iff_and (PeanoNat.Nat.succ_lt_mono m n))) hlt.
Definition ltSr {m} {n} (hlt : S m < S n) := (proj2 (iff_and (PeanoNat.Nat.succ_lt_mono m n))) hlt.
Definition ltsuc := PeanoNat.Nat.lt_lt_succ_r.

(* TODO convert all possible Defined to Qed after proving everything *)
Lemma nth_no_error {A} (x : list A):
  forall {n}, length x = n -> forall {i}, i < n -> nth_error x i <> None.
Proof.
  intros.
  apply nth_error_Some. lia.
Qed.

Lemma nltz : forall n, n < 0 -> False. easy. Qed.
Lemma length_tail {A} {xs : list A} {p} {x} : S p < length (cons x xs) -> p < length xs.
  rewrite length_cons. lia.
Qed.

Fixpoint safe_nth {A} (xs : list A) {i} : i < length xs -> A :=
  match xs, i with
  | nil, n => fun (hi : n < length nil) => match nltz _ hi with end
  | cons h _, 0 => fun _ => h
  | cons h t, S p => fun (hi : S p < length (cons h t)) => safe_nth t (length_tail hi)
  end.

(* Conversion will help me reuse the lemmas from the standard library *)
Lemma safe_nth_unsafe {A} : forall (xs : list A) {i} (hi : i < length xs),
  exists x, List.nth_error xs i = Some x /\ safe_nth xs hi = x.
Proof.
  induction xs. easy.
  destruct i; simpl; eauto.
Qed.

Ltac rewrite_safe_nth xs hi1 :=
  let h1 := fresh "h1" in
  let x1 := fresh "x1" in
  let hx1 := fresh "hx1" in
  let h1' := fresh "h1'" in
  assert (h1 := safe_nth_unsafe xs hi1); destruct h1 as [x1 (hx1 & h1')]; rewrite h1'.

Ltac rewrite_safe_nth_auto_left :=
  match goal with
  | [ |- safe_nth ?xs ?hi = _ ] =>
      rewrite_safe_nth xs hi
  end.

Ltac rewrite_safe_nth_auto :=
  match goal with
  | [ |- safe_nth ?xs ?hi = safe_nth ?ys ?hj ] =>
      rewrite_safe_nth xs hi;
      rewrite_safe_nth ys hj
  end.

Lemma eqxy2Some {A} {x y : A} : Some x = Some y -> x = y.
  congruence.
Qed.

Ltac rewrite_eqxy2Some_inner :=
  match goal with
  | [ h1 : _ = Some ?x, h2 : _ = Some ?y |- Some ?x = Some ?y ] => rewrite <- h1; rewrite <- h2
  end.

Ltac rewrite_eqxy2Some :=
  match goal with
  | [ |- ?x = ?y ] => apply eqxy2Some; rewrite_eqxy2Some_inner
  end.

Lemma safe_nth_eq {A} (xs : list A) {i} (hi1 : i < length xs) (hi2 : i < length xs) :
  safe_nth xs hi1 = safe_nth xs hi2.
Proof.
  rewrite_safe_nth xs hi1.
  rewrite_safe_nth xs hi2.
  rewrite_eqxy2Some.
  reflexivity.
Qed.

(* TODO consider renaming lemmas (change nth to nth_order) if they use nth_order instead of nth *)
Module Vector.
  Definition t A n := { x : list A | length x = n }.
  Definition projlist {A} {n} (x : t A n) := proj1_sig x.
  Definition projhlen {A} {n} (x : t A n) := proj2_sig x.

  Definition nil {A} : t A 0.
    refine (exist _ nil _). auto.
  Defined.

  Definition cons {A} (x : A) {n} (v : t A n) : t A (S n).
    refine (exist _ (List.cons x (projlist v)) _).
    destruct v. simpl. auto.
  Defined.

  Definition const {A} (c : A) n : t A n.
    refine (exist _ (List.repeat c n) _).
    apply repeat_length.
  Defined.

  Definition tl {A} {n} (v : t A (S n)) : t A n.
    destruct v as [xs hlen]. destruct xs. destruct n; easy.
    refine (exist _ xs _). auto.
  Defined.

  Definition shiftin {A} (a : A) {n} (v : t A n) : t A (S n).
    destruct v as [xs hlen].
    refine (exist _ (List.app xs (List.cons a List.nil)) _).
    rewrite length_app. simpl. lia.
  Defined.

  Definition shiftout {A} {n} (v : t A (S n)) : t A n.
    destruct v as [xs hlen].
    refine (exist _ (firstn n xs) _).
    pose (H := length_firstn n xs). lia.
  Defined.

  Definition nth_error {A} {n} (v : t A n) i : option A :=
    List.nth_error (projlist v) i.

  Lemma convhi {A} {n} (v : t A n) {i} (hi : i < n) : i < length (projlist v).
    destruct v as [xs hlen]. simpl. lia.
  Qed.

  Definition nth_order {A} {n} (v : t A n) {i} (hi : i < n) : A := safe_nth (projlist v) (convhi v hi).

  (* Because two objects of the type i < n could be different, but serve
   * the same purpose in this case.
   *)
  Lemma nth_order_eq {A} {n} (v : t A n) {i} (hi1 : i < n) (hi2 : i < n) :
    nth_order v hi1 = nth_order v hi2.
  Proof.
    apply safe_nth_eq.
  Qed.

  (* TODO move out since not general *)
  Lemma nth_cons_error {A} {n} (v : t A n) x :
    forall i, nth_error (cons x v) (S i) = nth_error v i.
  Proof.
    destruct v as [xs hlen]. intros.
    unfold nth_error. simpl. reflexivity.
  Qed.

  (* TODO move out since not general *)
  Lemma nth_cons {A} {n} (v : t A n) x :
    forall {i} (hi : S i < S n), nth_order (cons x v) hi = nth_order v (ltSr hi).
  Proof.
    destruct v as [xs hlen]. intros.
    unfold nth_order. simpl. apply safe_nth_eq.
  Qed.

  Lemma const_nth {A} (c : A) {n} {i} (hi : i < n) : nth_order (const c n) hi = c.
    (* TODO *)
  Admitted.

  (* TODO move out since not general *)
  Lemma nth_shiftout {A} {n} (v : t A (S n)) {i} (hi : i < n) :
    nth_order (shiftout v) hi = nth_order v (ltsuc _ _ hi).
  Proof.
    enough (H : projlist (shiftout v) = firstn n (projlist v)).
    unfold nth_order.
    rewrite_safe_nth_auto.
    rewrite_eqxy2Some.
    rewrite H.
    destruct v as [xs hlen]. simpl.

    assert (H' := nth_error_firstn n xs i).
    destruct (PeanoNat.Nat.ltb i n).
    apply H'.
    simpl in hx1. rewrite H' in hx1. easy.

    destruct v as [xs hlen]. simpl. auto.
  Qed.
End Vector.

Module bvec.
  Definition bit := bool.
  Definition zero := false.
  Definition bvec SIZE := Vector.t bit SIZE.

  Definition bvec_ith {n} (v : bvec n) {i} (hi : i < n) := Vector.nth_order v hi.
  Definition bvec_ith_error {n} (v : bvec n) {i} := Vector.nth_error v i.

  (* Remember: head (i = 0) has the LSB *)
  Definition bvec_lshift1 {n} (v : bvec (S n)) : bvec (S n) :=
    Vector.cons zero (Vector.shiftout v).

  Lemma bvec_lshift1_ith_0 {n} (v : bvec (S n)) (hi : 0 < S n) :
    bvec_ith (bvec_lshift1 v) hi = zero.
  Proof.
    destruct v as [xs hlen].
    destruct n; try easy.
  Qed.

  (* TODO rem if not used (written in the hope that it'd simplify many other parts *)
  Lemma nth_tl_error {n} (v : bvec (S n)) {i} :
    Vector.nth_error (Vector.tl v) i = Vector.nth_error v (S i).
  Proof.
    destruct v as [xs hlen].
    destruct xs. easy. simpl.
    reflexivity.
  Qed.

  Lemma bvec_lshift1_ith_S {n} (v : bvec (S n)) {i} (hi : S i < S n) :
    bvec_ith (bvec_lshift1 v) hi = bvec_ith v (ltprv hi).
  Proof.
    destruct v as [xs hlen].
    unfold bvec_lshift1. unfold bvec_ith.
    rewrite Vector.nth_cons.
    rewrite Vector.nth_shiftout.
    apply Vector.nth_order_eq.
  Qed.

  (* Using logical shift since the type used in Linux is u64 *)
  Definition bvec_rshift1 {n} (v : bvec (S n)) : bvec (S n) :=
    Vector.shiftin zero (Vector.tl v).

  Lemma suclt {i} {n} : i < S n -> i <> n -> S i < S n. lia. Qed.

  Lemma bvec_rshift1_ith_ltn {n} (v : bvec (S n)) {i} (hi : i < S n) (hi2 : i <> n) :
    bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).
  Proof.
    destruct v as [xs hlen].
    unfold bvec_rshift1. unfold bvec_ith.
    unfold Vector.nth_order.
    destruct xs.
    - destruct i; easy.
    - rewrite_safe_nth_auto.
      rewrite_eqxy2Some.
      simpl. rewrite nth_error_app1. reflexivity.
      assert (hlen2 := length_cons xs b). rewrite hlen in hlen2.
      assert (hlen3 : n = length xs). lia.
      assert (hlen4 : i < n). lia. rewrite hlen3 in hlen4. assumption.
  Qed.

  (* TODO update the user and remove this *)
  Lemma bvec_rshift1_ith_0 {n} (v : bvec (S n)) (hi : 0 < S n) (hi2 : 0 <> n) :
    bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).
  Proof.
    apply bvec_rshift1_ith_ltn.
  Qed.

  (* TODO rem the third arg after updating the users;
   * synth with (PeanoNat.Nat.lt_succ_diag_r n)
   *)
  Lemma nth_shiftin_last {A} (a : A) {n} (v : Vector.t A n) (hi : n < S n) :
    Vector.nth_order (Vector.shiftin a v) hi = a.
  Proof.
    destruct v as [xs hlen].
    unfold Vector.nth_order.
    assert (n < length (Vector.projlist
                          (Vector.shiftin a (exist (fun x : list A => length x = n) xs hlen)))). simpl. rewrite <- hlen. rewrite length_app. simpl. lia.

    rewrite_safe_nth_auto_left. simpl in hx1.
    rewrite nth_error_app2 in hx1. rewrite hlen in hx1.
    replace (n - n) with 0 in hx1. rewrite nth_error_cons_0 in hx1.
    congruence. lia. lia.
  Qed.

  (* TODO rem the third arg after updating the users *)
  Lemma bvec_rshift1_ith_n {n} (v : bvec (S n)) (hi : n < S n) :
    bvec_ith (bvec_rshift1 v) hi = zero.
  Proof.
    apply nth_shiftin_last.
  Qed.
End bvec.
