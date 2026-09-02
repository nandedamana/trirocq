Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.SigVector.

From Stdlib Require Import Lia.

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

  Definition v {SIZE} (P : t SIZE) := match P with cons _ v _ => v end.
  Definition m {SIZE} (P : t SIZE) := match P with cons _ _ m => m end.

  Definition ith_v {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (v tn) hidx.
  Definition ith_m {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (m tn) hidx.

  Definition wellformed {SIZE} (tn : t SIZE) :=
    forall i (hidx : i < SIZE),
      bvec_ith (m tn) hidx = one -> bvec_ith (v tn) hidx = zero.

  Lemma ith_m_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_m (cons SIZE n1 n2) hidx = bvec_ith n2 hidx.
    unfold ith_m. simpl. reflexivity.
  Qed.

  Lemma ith_m_simplify2 {SIZE} n1 n2 i (hidx : i < SIZE) : bvec_ith (m (cons SIZE n1 n2)) hidx = bvec_ith n2 hidx.
    simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_v (cons SIZE n1 n2) hidx = bvec_ith n1 hidx.
    unfold ith_v. simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify2 {SIZE} n1 n2 i (hidx : i < SIZE) : bvec_ith (v (cons SIZE n1 n2)) hidx = bvec_ith n1 hidx.
    simpl. reflexivity.
  Qed.

  (* Using `unfold m` directly could cause unwanted expansions in some places. *)
  Lemma m_cons_simplify {SIZE} n1 n2 : m (cons SIZE n1 n2) = n2.
    unfold m. reflexivity.
  Qed.

  Lemma v_cons_simplify {SIZE} n1 n2 : v (cons SIZE n1 n2) = n1.
    unfold v. reflexivity.
  Qed.

  Definition tl {n} (tn : t (S n)) : t n :=
    cons n (Vector.tl (v tn)) (Vector.tl (m tn)).
End tnum.

Definition ingamma {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) :=
  forall i (hidx : i < SIZE),
    tnum.ith_m T hidx = zero -> bvec_ith x hidx = tnum.ith_v T hidx.

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

Section tnum_shift.
  Variable SIZE : nat.

  Definition tnum_lshift (P : tnum.t SIZE) n :=
    tnum.cons _ (bvec_lshift (tnum.v P) n) (bvec_lshift (tnum.m P) n).

  Lemma tnum_lshift_wellformed (P : tnum.t SIZE) n :
    tnum.wellformed P -> tnum.wellformed (tnum_lshift P n).
  Proof.
    intros wfp i hidx.
    unfold tnum_lshift.
    rewrite tnum.ith_m_simplify2. rewrite tnum.ith_v_simplify2.

    assert (hin : i >= n \/ i < n) by lia.
    destruct hin as [hin1 | hin2].
    - assert (hj : exists j, i = j + n). exists (i - n). lia.
      destruct hj as [j hj].
      assert (hj' : j < SIZE) by lia.
      rewrite !bvec_ith_lshift_high with (hj := hj') by auto.
      auto.
    - rewrite !bvec_ith_lshift_low by assumption. easy.
  Qed.

  Lemma tnum_lshift_sound (x : bvec SIZE) (P : tnum.t SIZE) n :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_lshift P n) /\ ingamma (bvec_lshift x n) (tnum_lshift P n).
  Proof.
    intros wfp igx.
    split. apply tnum_lshift_wellformed; auto.

    unfold ingamma.
    unfold tnum_lshift.
    intros i hidx.
    rewrite tnum.ith_m_simplify. rewrite tnum.ith_v_simplify.

    assert (hin : i >= n \/ i < n) by lia.
    destruct hin as [hin1 | hin2].
    - assert (hj : exists j, i = j + n). exists (i - n). lia.
      destruct hj as [j hj].
      assert (hj' : j < SIZE) by lia.
      rewrite !bvec_ith_lshift_high with (hj := hj') by auto.
      auto.
    - rewrite !bvec_ith_lshift_low by assumption. easy.
  Qed.

  Definition tnum_rshift (P : tnum.t SIZE) n :=
    tnum.cons _ (bvec_rshift (tnum.v P) n) (bvec_rshift (tnum.m P) n).

  Lemma tnum_rshift_wellformed (P : tnum.t SIZE) n :
    tnum.wellformed P -> tnum.wellformed (tnum_rshift P n).
  Proof.
    intros wfp i hidx.
    unfold tnum_rshift.
    rewrite tnum.ith_m_simplify2. rewrite tnum.ith_v_simplify2.

    assert (hin : i + n < SIZE \/ i + n >= SIZE) by lia.
    destruct hin as [hin1 | hin2].
    - rewrite !bvec_ith_rshift_low with (hin := hin1). apply wfp.
    - rewrite !bvec_ith_rshift_high by auto. easy.
  Qed.

  Lemma tnum_rshift_sound (x : bvec SIZE) (P : tnum.t SIZE) n :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_rshift P n) /\ ingamma (bvec_rshift x n) (tnum_rshift P n).
  Proof.
    intros wfp igx.
    split. apply tnum_rshift_wellformed; auto.

    unfold ingamma.
    unfold tnum_rshift.
    intros i hidx.
    rewrite tnum.ith_m_simplify. rewrite tnum.ith_v_simplify.

    assert (hin : i + n < SIZE \/ i + n >= SIZE) by lia.
    destruct hin as [hin1 | hin2].
    - rewrite !bvec_ith_rshift_low with (hin := hin1). auto.
    - rewrite !bvec_ith_rshift_high by auto. easy.
  Qed.

  (* TODO merge wellformed and soundness proofs? same code. *)
End tnum_shift.

Arguments tnum_lshift {SIZE}.
Arguments tnum_lshift_wellformed {SIZE}.
Arguments tnum_lshift_sound {SIZE}.

Arguments tnum_rshift {SIZE}.
Arguments tnum_rshift_wellformed {SIZE}.
Arguments tnum_rshift_sound {SIZE}.

Section tnum_shift.
  Definition tnum_rshift1_shrink {n} (P : tnum.t (S n)) : tnum.t n :=
    tnum.tl P.

  Lemma tnum_rshift1_shrink_wellformed {n} (P : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed (tnum_rshift1_shrink P).
  Proof.
    unfold tnum.wellformed.
    unfold tnum_rshift1_shrink, tnum.tl.
    destruct P as [pv pm].
    unfold tnum.m, tnum.v.
    unfold bvec_ith.
    intros wfp i hi.
    repeat rewrite Vector.nth_order_tl. auto.
  Qed.

  Lemma tnum_tl_ingamma : forall n (x : bvec (S n)) (P : tnum.t (S n)),
      ingamma x P -> ingamma (Vector.tl x) (tnum.tl P).
  Proof.
    intros n x P.
    unfold ingamma, tnum.tl, tnum.ith_m, tnum.ith_v.
    destruct P as [pv pm].
    unfold bvec_ith. simpl.
    intro igx. intros i hi.
    repeat rewrite Vector.nth_order_tl.
    auto.
  Qed.

  Lemma tnum_rshift1_shrink_sound {n} (x : bvec (S n)) (P : tnum.t (S n)) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_rshift1_shrink P) /\ ingamma (Vector.tl x) (tnum_rshift1_shrink P).
  Proof.
    intros wfp igx.
    split. apply tnum_rshift1_shrink_wellformed; auto.

    unfold tnum_rshift1_shrink.
    apply tnum_tl_ingamma; auto.
  Qed.
End tnum_shift.

Definition zerotnum n := tnum.cons n (zerovec n) (zerovec n).
Lemma zerotnum_wellformed {n} : tnum.wellformed (zerotnum n).
  unfold tnum.wellformed.
  destruct i; intro hidx; pose (H := zerovec_ith hidx); easy.
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
  intros i hidx.
  rewrite bvec_or_rel.
  destruct (bvec_ith (tnum.m P) hidx); simplify_bit_ops; easy.
Qed.
