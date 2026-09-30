From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  Bit
  BitVector.

(** printing < %\texttt{<}% *)

Ltac rewrite_if_holds H :=
  match type of H with
  | ?b = ?b -> _ => rewrite H
  end.

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t SIZE := cons (v : bvec SIZE) (m : bvec SIZE).

  Section tnum_helpers.
    Context [SIZE : nat].

    Definition v (P : t SIZE) := match P with cons _ v _ => v end.
    Definition m (P : t SIZE) := match P with cons _ _ m => m end.

    Definition ith_v (tn : t SIZE) i := bvec_ith (v tn) i.
    Definition ith_m (tn : t SIZE) i := bvec_ith (m tn) i.

    (**
     * Reasoning about the ith bit when [i >= SIZE] is not only
     * meaningless, but impossible in the presence of bvec_neg
     * (bvec_neg_rel requires i < SIZE).
     *)
    Definition wellformed (tn : t SIZE) :=
      forall i, i < SIZE ->
        bvec_ith (m tn) i = one -> bvec_ith (v tn) i = zero.

    Lemma ith_m_simplify n1 n2 i :
      ith_m (cons SIZE n1 n2) i = bvec_ith n2 i.
    Proof.
      unfold ith_m. simpl. reflexivity.
    Qed.

    Lemma ith_m_simplify2 n1 n2 i :
      bvec_ith (m (cons SIZE n1 n2)) i = bvec_ith n2 i.
    Proof.
      simpl. reflexivity.
    Qed.

    Lemma ith_v_simplify n1 n2 i :
      ith_v (cons SIZE n1 n2) i = bvec_ith n1 i.
    Proof.
      unfold ith_v. simpl. reflexivity.
    Qed.

    Lemma ith_v_simplify2 n1 n2 i :
      bvec_ith (v (cons SIZE n1 n2)) i = bvec_ith n1 i.
    Proof.
      simpl. reflexivity.
    Qed.

    (* Using `unfold m` directly could cause unwanted expansions in some places. *)
    Lemma m_cons_simplify n1 n2 : m (cons SIZE n1 n2) = n2.
      unfold m. reflexivity.
    Qed.

    Lemma v_cons_simplify n1 n2 : v (cons SIZE n1 n2) = n1.
      unfold v. reflexivity.
    Qed.

  End tnum_helpers.
End tnum.

Definition ingamma {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) :=
  forall i, i < SIZE ->
    tnum.ith_m T i = false -> bvec_ith x i = tnum.ith_v T i.

(**
 * 2-ary function F on tnum is a sound abstraction of f on bvec.
 * `sound f F` instead of `sound F f` in order to be consistent with `ingamma`.
 *)
Definition sound2 SIZE
  (f : bvec SIZE -> bvec SIZE -> bvec SIZE)
  (F : tnum.t SIZE -> tnum.t SIZE -> tnum.t SIZE) :=
  forall (p q : bvec SIZE) P Q,
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma p P -> ingamma q Q ->
    tnum.wellformed (F P Q) /\ ingamma (f p q) (F P Q).

Definition subset {SIZE} (P Q : tnum.t SIZE) :=
  forall x, ingamma x P -> ingamma x Q.

(**
 * If F is an optimal approximation of f, that means F(P, Q) is
 * a subset of F'(P, Q), for any sound approximation F' of f.
 *)
Definition optimal2 SIZE (f : bvec SIZE -> bvec SIZE -> bvec SIZE) F :=
  sound2 SIZE f F ->
  forall F', sound2 SIZE f F' ->
             forall (P Q : tnum.t SIZE),
               tnum.wellformed P -> tnum.wellformed Q -> subset (F P Q) (F' P Q).

Definition zerotnum n := tnum.cons n (zerovec n) (zerovec n).

Lemma zerotnum_wellformed {n} : tnum.wellformed (zerotnum n).
  unfold tnum.wellformed.
  intro i. simpl.
  rewrite zerovec_ith. easy.
Qed.

Lemma ingamma_value {SIZE} (P : tnum.t SIZE) : ingamma (tnum.v P) P.
  unfold ingamma.
  auto.
Qed.

Lemma ingamma_value_bitor_mask :
  forall {SIZE} (P : tnum.t SIZE),
    ingamma (bvec_or (tnum.v P) (tnum.m P)) P.
Proof.
  intros SIZE P.
  unfold ingamma, tnum.ith_m, tnum.ith_v.
  intros i.
  rewrite bvec_or_rel.
  repeat destruct (bvec_ith (_ P) i);
    auto.
Qed.

Ltac unwrap_bvec_ops := match goal with
                          _ => repeat rewrite bvec_and_rel;
                               repeat rewrite bvec_neg_rel;
                               repeat rewrite bvec_or_rel;
                               repeat rewrite bvec_xor_rel
                        end.
