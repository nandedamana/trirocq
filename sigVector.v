(* Started 2025-09-24 *)

From Stdlib Require Import List.
From Stdlib Require Import Program.

Lemma nth_no_error {A} {i}:
  forall x : list A, forall {n}, length x = n -> i < n -> nth_error x i <> None.
Proof.
  induction i.
  - destruct x; destruct n; easy.
  - destruct n. easy. rewrite nth_error_S.
    destruct x. simpl. easy.
    simpl. intros hs1 hs2.
    assert (length x = n). auto.
    assert (i < n). apply PeanoNat.lt_S_n; assumption.
    apply (IHi x n); assumption.
Qed.

Module Vector.
  Definition t A n := { x : list A | length x = n }.
  Definition projlist {A} {n} (x : t A n) := proj1_sig x.
  Definition projhlen {A} {n} (x : t A n) := proj2_sig x.

  Program Definition nil {A} : t A 0.
  refine (exist _ nil _). auto.
  Defined.

  Program Definition cons {A} {n} (v : t A n) (x : A) : t A (S n).
  refine (exist _ (List.cons x (projlist v)) _).
  destruct v. simpl. auto.
  Defined.

  Program Definition nth_order {A} {n} (v : t A n) {i} (hi : i < n) :=
    match (List.nth_error (projlist v) i) with
    | None => !
    | Some x => x
    end.
  Next Obligation.
    destruct v.
    apply (nth_no_error x e hi). auto.
  Defined.
End Vector.
