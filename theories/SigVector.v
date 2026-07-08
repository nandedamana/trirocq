(* Started 2025-09-24 *)

From Stdlib Require Import Lia. (* TODO move (or remove if unused) *)
From Stdlib Require Import List.
From Stdlib Require Import Program.

Definition ltprv {m} {n} (h : S m < n) := PeanoNat.Nat.lt_succ_l m n h.
Definition ltS {m} {n} (hlt : m < n) := (proj1 (iff_and (PeanoNat.Nat.succ_lt_mono m n))) hlt.
Definition ltSr {m} {n} (hlt : S m < S n) := (proj2 (iff_and (PeanoNat.Nat.succ_lt_mono m n))) hlt.
Definition ltsuc := PeanoNat.Nat.lt_lt_succ_r.

Lemma nth_no_error {A} (x : list A):
  forall {n}, length x = n -> forall {i}, i < n -> nth_error x i <> None.
Proof.
  intros.
  apply nth_error_Some. lia.
Qed.

Lemma nth_error_fst_split {A} {B} : forall (xs : list (prod A B)) i,
    List.nth_error (fst (List.split xs)) i =
      match List.nth_error xs i with
      | None => None
      | Some x => Some (fst x)
      end.
Proof.
  induction xs as [|x xs IHxs].
  - destruct i; auto.
  - destruct i;
      destruct x; simpl; destruct (List.split xs); simpl; auto.
Qed.

(* Proof written by referring the source of List.split_nth. *)
Lemma nth_error_snd_split {A} {B} : forall (xs : list (prod A B)) i,
    List.nth_error (snd (List.split xs)) i =
      match List.nth_error xs i with
      | None => None
      | Some x => Some (snd x)
      end.
Proof.
  intro xs; induction xs as [|x xs IHxs].
  - intro i. destruct i; auto.
  - intro i. destruct i.
    + destruct x. simpl. destruct (List.split xs). simpl. auto.
    + destruct x. simpl. destruct (List.split xs). simpl. auto.
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

Ltac rewrite_safe_nth_anywhere :=
  match goal with
  | [ |- context[safe_nth ?xs ?hi] ] =>
      rewrite_safe_nth xs hi
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

Lemma safe_nth_cons {A} (xs : list A) {i} (hi : S i < S (length xs)) x:
  safe_nth (List.cons x xs) hi = safe_nth xs (PeanoNat.lt_S_n _ _ hi).
Proof.
  simpl. apply safe_nth_eq.
Qed.

Lemma list_all_ith_eq_cons : forall {A} {x y : list A} {xh yh},
    length x = length y ->
    (forall i (hi : i < length (List.cons xh x)) (hj : i < length (List.cons yh y)),
        (safe_nth (List.cons xh x) hi) = (safe_nth (List.cons yh y) hj)) ->
    (forall i (hi : i < length x) (hj : i < length y),
        (safe_nth x hi) = (safe_nth y hj)).
Proof.
  intros A x y xh yh hlen heq.

  intros i hi hj.
  assert (lxi : S i < length (List.cons xh x)). simpl. lia.
  assert (lyi : S i < length (List.cons yh y)). simpl. lia.
  specialize (heq (S i) lxi lyi).
  repeat rewrite safe_nth_cons in heq.

  assert (hix : safe_nth x hi = safe_nth x (PeanoNat.lt_S_n i (length x) lxi)).
  apply safe_nth_eq.

  assert (hiy : safe_nth y hj = safe_nth y (PeanoNat.lt_S_n i (length y) lyi)).
  apply safe_nth_eq.

  rewrite hix, hiy. auto.
Qed.

Lemma list_eq_by_ith : forall {A} (x y : list A),
    length x = length y ->
    (forall i (hi : i < length x) (hj : i < length y),
        (safe_nth x hi) = (safe_nth y hj)) -> x = y.
Proof.
  intros A x y.
  induction x as [|xh] in y |- *. (* "generalize over y" to sync both lists *)
  - intro hlen. destruct y; try easy.
  - intro hlen. destruct y as [|yh]; try easy.
    assert (hlen' : length x = length y). auto.
    specialize (IHx y hlen').

    intro heq.
    assert (xh = yh).
    specialize (heq 0 (PeanoNat.Nat.lt_0_succ (length x)) (PeanoNat.Nat.lt_0_succ (length y))).
    simpl in heq. auto.

    enough (x = y). congruence.

    pose (H' := list_all_ith_eq_cons hlen' heq).
    auto.
Qed.

Section map2_list.
  (* Providing custom map2 since it is no longer found in the Stdlib. *)
  Fixpoint map2_list {A} {B} {C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
    match xs, ys with
    | List.nil, List.nil => List.nil
    | List.cons xh xt, List.cons yh yt =>
        List.cons (f xh yh) (map2_list f xt yt)
    | _, _ => List.nil
    end.

  Lemma map2_list_cons {A} {B} {C} (f : A -> B -> C) :
    forall xh (xt : list A) yh (yt : list B),
      map2_list f (List.cons xh xt) (List.cons yh yt) =
        List.cons (f xh yh) (map2_list f xt yt).
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma map2_list_length {A} {B} {C} (f : A -> B -> C) {n} :
    forall (xs : list A) (ys : list B),
      length xs = n -> length ys = n -> length (map2_list f xs ys) = n.
  Proof.
    induction n.
    - intros xs ys hlenx hleny.
      destruct xs; try easy. destruct ys; try easy.
    - destruct xs; try easy. destruct ys; try easy.
      rewrite map2_list_cons. repeat rewrite length_cons.
      intros hlenx hleny.
      apply eq_add_S in hlenx. apply eq_add_S in hleny.
      apply eq_S. auto.
  Qed.

  Lemma map2_list_convhi {A} {B} {C} (f : A -> B -> C) {n} :
    forall (xs : list A) (ys : list B),
      length xs = n -> length ys = n ->
      forall {i}, i < n -> i < length (map2_list f xs ys).
  Proof.
    intros. rewrite map2_list_length with (n := n); auto.
  Qed.

  Lemma length_convhi {A} {n} (xs : list A) :
    length xs = n -> forall {i}, i < n -> i < length xs.
  Proof. intros. lia. Qed.

  Definition option_map2 {A} {B} {C}
    (f : A -> B -> C) (oa : option A) (ob : option B) :=
    match oa, ob with
    | Some a, Some b => Some (f a b)
    | _, _ => None
    end.

  Lemma nth_error_map2_list {A} {B} {C} (f : A -> B -> C) :
    forall (xs : list A) (ys : list B) i,
      nth_error (map2_list f xs ys) i = option_map2 f (nth_error xs i) (nth_error ys i).
  Proof.
    unfold map2_list.
    induction xs.
    - destruct ys; destruct i; auto.
    - destruct ys; destruct i; auto.
      unfold option_map2. simpl. destruct (nth_error xs i); auto.
      simpl. auto.
  Qed.
End map2_list.

(* TODO consider renaming lemmas (change nth to nth_order) if they use nth_order instead of nth *)
Module Vector.
  Definition t A n := { x : list A | length x = n }.
  Definition projlist {A} {n} (x : t A n) := proj1_sig x.
  Definition projhlen {A} {n} (x : t A n) := proj2_sig x.

  Definition nil A : t A 0.
    refine (exist _ nil _). auto.
  Defined.

  Definition cons A (x : A) n (v : t A n) : t A (S n).
    refine (exist _ (List.cons x (projlist v)) _).
    destruct v. simpl. auto.
  Defined.

  Definition const {A} (c : A) n : t A n.
    refine (exist _ (List.repeat c n) _).
    apply repeat_length.
  Defined.

  Lemma eqlist_imp_eqvec {A} {n} (v1 : Vector.t A n) (v2 : Vector.t A n) :
    Vector.projlist v1 = Vector.projlist v2 -> v1 = v2.
  Proof.
    destruct v1 as [xs hlenx]. destruct v2 as [ys hleny].
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  Qed.

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

  Definition map {A} {B} (f : A -> B) {n} (v : t A n) : t B n.
    destruct v as [xs hlen].
    refine (exist _ (List.map f xs) _).
    rewrite <- hlen. apply length_map.
  Defined.

  Definition map2 {A} {B} {C} (f : A -> B -> C) {n} (v1 : t A n) (v2 : t B n) : t C n.
    destruct v1 as [xs hlen1].
    destruct v2 as [ys hlen2].

    refine (exist _ (map2_list f xs ys) _).
    apply map2_list_length; auto.
  Defined.

  Definition nth_error {A} {n} (v : t A n) i : option A :=
    List.nth_error (projlist v) i.

  Lemma convhi {A} {n} (v : t A n) {i} (hi : i < n) : i < length (projlist v).
    destruct v as [xs hlen]. simpl. lia.
  Qed.

  Definition nth_order {A} {n} (v : t A n) {i} (hi : i < n) : A := safe_nth (projlist v) (convhi v hi).

  Lemma nth_order_tl {A} {n} (v : t A (S n)) {i} (hi : i < n) :
    nth_order (tl v) hi = nth_order v (ltS hi).
  Proof.
    unfold Vector.nth_order.
    destruct v as [xs hlenx].
    destruct xs.
    - easy.
    - rewrite_safe_nth_auto.
      rewrite_eqxy2Some.
      simpl. reflexivity.
  Qed.

  Lemma nth_map {A} {B} (f : A -> B) {n} (v : t A n) :
    forall {i} (hi : i < n), nth_order (map f v) hi = f (nth_order v hi).
  Proof.
    intros i hi.
    destruct v as [xs hlenx].
    unfold nth_order. unfold map. simpl.
    rewrite_safe_nth_auto_left.
    rewrite List.nth_error_map in hx1.
    rewrite_safe_nth xs (convhi (exist (fun x : list A => length x = n) xs hlenx) hi).
    rewrite hx0 in hx1. simpl in hx1. congruence.
  Qed.

  Lemma nth_map2 {A} {B} {C} (f : A -> B -> C) {n} (v1 : t A n) (v2 : t B n) :
    forall {i} (hi : i < n),
      nth_order (map2 f v1 v2) hi = f (nth_order v1 hi) (nth_order v2 hi).
  Proof.
    intros i hi.
    destruct v1 as [xs hlenx].
    destruct v2 as [ys hleny].
    unfold nth_order. unfold map2. simpl.
    rewrite_safe_nth_auto_left.
    rewrite nth_error_map2_list in hx1.
    rewrite_safe_nth xs (convhi (exist (fun x : list A => length x = n) xs hlenx) hi).
    rewrite_safe_nth ys (convhi (exist (fun y : list B => length y = n) ys hleny) hi).
    assert (H := nth_error_map2_list f xs ys i).
    rewrite hx0 in hx1. rewrite hx2 in hx1. simpl in hx1.
    congruence.
  Qed.

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
    forall i, nth_error (cons _ x _ v) (S i) = nth_error v i.
  Proof.
    destruct v as [xs hlen]. intros.
    unfold nth_error. simpl. reflexivity.
  Qed.

  (* TODO move out since not general *)
  Lemma nth_cons {A} {n} (v : t A n) x :
    forall {i} (hi : S i < S n), nth_order (cons _ x _ v) hi = nth_order v (ltSr hi).
  Proof.
    destruct v as [xs hlen]. intros.
    unfold nth_order. simpl. apply safe_nth_eq.
  Qed.

  Lemma const_nth {A} (c : A) {n} {i} (hi : i < n) : nth_order (const c n) hi = c.
    unfold nth_order. unfold const. simpl.
    rewrite_safe_nth_auto_left.
    rewrite List.nth_error_repeat in hx1.
    congruence. assumption.
  Qed.

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
