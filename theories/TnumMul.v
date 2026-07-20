Require Import trirocq.Bit.
Require Import trirocq.BitMul.
Require Import trirocq.BitVector.
Require Import trirocq.SigVector.
Require Import trirocq.Tnum.
Require Import trirocq.TnumAdd.
Require Import trirocq.TnumUnion.

From Stdlib Require Import Lia.

Section linux_tnum_multiplication.
  (* To make another proof cleaner *)
  Lemma tnum_union_sound_l {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset P U.
  Proof.
    intros wfP wfQ.
    pose (H := tnum_union_sound P Q wfP wfQ).
    simpl in H. simpl. destruct H as (h1 & h2 & h3). auto.
  Qed.

  Lemma tnum_union_sound_r {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset Q U.
  Proof.
    intros wfP wfQ.
    pose (H := tnum_union_sound P Q wfP wfQ).
    simpl in H. simpl. destruct H as (h1 & h2 & h3). auto.
  Qed.

  (* Using a and b instead of P and Q (unlike in other parts of this project)
   * to make comparison with the in-kernel code easier.
   *)
  Fixpoint tnum_mul_loop m (a : tnum.t m) :=
    match m return tnum.t m -> forall n, tnum.t (S n) -> tnum.t (S n) -> tnum.t (S n) with
    | 0 => fun (a : tnum.t 0) n (b acc : tnum.t (S n)) => acc
    | S mp => fun (a : tnum.t (S mp)) n (b acc : tnum.t (S n)) =>
        match (bvec_denote (tnum.v a)), (bvec_denote (tnum.m a)) return (tnum.t (S n)) with
        | 0, 0 => acc
        | _, _ =>
            let nxt_acc := match bvec_lsb (tnum.v a) with
                           | one => tnum_add acc b
                           | zero => match bvec_lsb (tnum.m a) with
                                     | one => tnum_union acc (tnum_add acc b)
                                     | zero => acc
                                     end
                           end in
            let nxt_a := tnum_rshift1_shrink a in
            let nxt_b := tnum_lshift1 b in
            tnum_mul_loop _ nxt_a _ nxt_b nxt_acc
        end
    end a.

  Definition tnum_mul {n} (a b : tnum.t (S n)) :=
    tnum_mul_loop _ a _ b (zerotnum (S n)).

  Ltac crush_tnum_mul_loop_wellformed :=
    try assumption;
    try apply tnum_add_wellformed; auto;
    try apply tnum_union_wellformed; auto;
    try apply tnum_rshift1_shrink_wellformed; auto;
    try apply tnum_lshift1_wellformed; auto;
    try match goal with
    | [ IH : forall _ _ _ _,
          _ -> _ -> _ ->
          tnum.wellformed (tnum_mul_loop _ _ _ _ _) |-
            tnum.wellformed (tnum_mul_loop _ _ _ _ _) ] =>
        try apply IH
      end;
    try match goal with
      | [ |- tnum.wellformed (match ?e with
                              | zero => _
                              | one => _
                              end) ] =>
          destruct (e)
      end.

  Lemma tnum_mul_loop_wellformed : forall m (a : tnum.t m) n (b acc : tnum.t (S n)),
    tnum.wellformed a -> tnum.wellformed b -> tnum.wellformed acc ->
    tnum.wellformed (tnum_mul_loop m a n b acc).
  Proof.
    induction m.
    - auto.
    - intros a n b acc wfa wfb wfc.
      unfold tnum_mul_loop.
      fold tnum_mul_loop.
      destruct (bvec_denote (tnum.v a));
        repeat crush_tnum_mul_loop_wellformed.
      destruct (bvec_denote (tnum.m a));
        repeat crush_tnum_mul_loop_wellformed.
  Qed.

  Lemma tnum_mul_wellformed {n} (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed (tnum_mul P Q).
  Proof.
    unfold tnum_mul. intros.
    apply tnum_mul_loop_wellformed; auto.
    apply zerotnum_wellformed.
  Qed.

  Ltac crush_tnum_mul_loop_sound :=
    repeat (match goal with
            | [ |- tnum.wellformed (tnum_add ?y ?z) ] => apply tnum_add_wellformed
            | [ |- ingamma ?x (tnum_add ?y ?z) ] => apply tnum_add_sound
            | [ |- tnum.wellformed (tnum_union ?y ?z) ] => apply tnum_union_wellformed
            | [ _ : ingamma ?a ?A |- ingamma ?a (tnum_union ?A ?B) ] => apply tnum_union_sound_l
            end; auto).

  Lemma knwonlsb n (a : bvec (S n)) (A : tnum.t (S n)) :
      ingamma a A ->
      bvec_lsb (tnum.m A) = zero ->
      bvec_lsb a = bvec_lsb (tnum.v A).
  Proof.
    unfold bvec_lsb.
    unfold ingamma. unfold tnum.ith_m, tnum.ith_v.
    intro ig. specialize (ig _ (PeanoNat.Nat.lt_0_succ n)).
    assumption.
  Qed.

  Lemma lsb_wellformed n (A : tnum.t (S n)) :
      tnum.wellformed A ->
      bit_and (bvec_lsb (tnum.v A)) (bvec_lsb (tnum.m A)) = zero.
  Proof.
    unfold tnum.wellformed, bvec_lsb.
    intro ig. specialize (ig _ (PeanoNat.Nat.lt_0_succ n)).
    repeat destruct (bvec_ith _ _); auto.
  Qed.

  (* TODO move out? *)
  Lemma bvec_denote_cons : forall n (a : bvec (S n)),
      bvec_denote a =
        bit2nat (bvec_lsb a) + Nat.double (bvec_denote (Vector.tl a)).
  Proof.
    induction n.
    - destruct a as [xs hlenx].
      destruct xs; try easy.
    - intro a.
      unfold bvec_denote at 1.
      destruct a as [xs hlenx].
      destruct xs. easy. auto.
  Qed.

  Lemma lsb_denote_0 : forall n (a : bvec (S n)),
    bvec_denote a = 0 -> bvec_lsb a = zero.
  Proof.
    destruct a as [xs hlenx].
    destruct xs; try easy.
    unfold bvec_denote, bvec_lsb, bvec_ith, Vector.nth_order.
    destruct b; auto. simpl. lia.
  Qed.

  Lemma denote_known_tnum : forall n (a : bvec n) (A : tnum.t n),
    ingamma a A ->
    bvec_denote (tnum.m A) = 0 ->
    bvec_denote a = bvec_denote (tnum.v A).
  Proof.
    induction n.
    - destruct a as [xs hlenx].
      destruct A as [[vs hlenv] [ms hlenm]].
      unfold ingamma, tnum.ith_v, tnum.ith_m.
      simpl. unfold bvec_denote. simpl.
      destruct xs, vs, ms; try easy.
    - intros a A iga.

      intro h1. assert (h2 := lsb_denote_0 _ _ h1). revert h1.

      repeat rewrite bvec_denote_cons.
      destruct (bit2nat _); simpl; try easy.

      assert (h3 : forall n (A0 : tnum.t (S n)),
                 Vector.tl (tnum.v A0) = (tnum.v (tnum.tl A0))).
      destruct A0 as [v m]. unfold tnum.tl. simpl. reflexivity.
      rewrite h3.

      assert (h4 : forall n (A0 : tnum.t (S n)),
                 Vector.tl (tnum.m A0) = (tnum.m (tnum.tl A0))).
      destruct A0 as [v m]. unfold tnum.tl. simpl. reflexivity.
      rewrite h4.

      assert (hz : forall x, Nat.double x = 0 -> x = 0). lia.
      intro h5. specialize (hz _ h5).
      rewrite IHn with (A := (tnum.tl A)); auto.
      rewrite knwonlsb with (A := A); auto.
      apply tnum_tl_ingamma; auto.
  Qed.

  Lemma tnum_mul_loop_sound :
    forall m (A : tnum.t m) (a : bvec m) {n} (B C : tnum.t (S n)) (b c : bvec (S n)),
      tnum.wellformed A -> tnum.wellformed B -> tnum.wellformed C ->
      ingamma a A -> ingamma b B -> ingamma c C ->
      let R := tnum_mul_loop _ A _ B C in
      let r := bvec_mul_loop _ a _ b c in
      ingamma r R.
  Proof.
    induction m.
    - intros until c. simpl. auto.
    - intros until c. intros wfa wfb wfc iga igb igc. simpl.

      assert (H0 := denote_known_tnum _ a A iga).
      assert (htblsb := knwonlsb _ a A iga).
      assert (htlsb := lsb_wellformed _ A wfa).
      assert (hblsb := lsb_denote_0 _ a).

      assert (hig_rsh : ingamma (Vector.tl a) (tnum_rshift1_shrink A)).
      unfold tnum_rshift1_shrink.
      fold (tnum.tl A).
      apply tnum_tl_ingamma; auto.

      assert (hig_lsh :  ingamma (bvec_lshift1 b) (tnum_lshift1 B)).
      apply tnum_lshift1_sound; auto.

      assert (hbmul0 :
               bvec_denote a = 0 ->
               c = bvec_mul_loop m (Vector.tl a) n (bvec_lshift1 b) c).
      intro h.
      unfold bvec_mul_loop.
      destruct m. reflexivity.
      enough (h2 : bvec_denote a = 0 -> bvec_denote (Vector.tl a) = 0).
      rewrite h2; auto.
      destruct a as [xs hlenx]. unfold bvec_denote.
      destruct xs as [|xh xt]; try easy.
      simpl. destruct xh; unfold bit2nat; lia.

      (* So that `auto` can pick it (needed in several cases) *)
      pose (tnum_rshift1_shrink_wellformed A).
      pose (tnum_lshift1_wellformed B).

      destruct (bvec_denote (tnum.v A));
        destruct (bvec_denote (tnum.m A));
        destruct (bvec_denote a);
        destruct (bvec_lsb (tnum.v A));
        destruct (bvec_lsb (tnum.m A));
        destruct (bvec_lsb a);
        unfold bit_and in htlsb; simpl in htlsb;
        (* lia will get rid of goals where I have
         *  something like `0 = 0 -> S n0 = 0` above the line.
         *)
        try easy;
        try match goal with
        | [ H : ?x = ?x -> zero = one |- _ ] =>
            discriminate H; auto
        | [ H : ?x = ?x -> one = zero |- _ ] =>
            discriminate H; auto
        end;
        try lia;
        try (apply IHm; auto; crush_tnum_mul_loop_sound).

      + rewrite hbmul0; auto.
      + rewrite hbmul0; auto. apply IHm; auto;
        crush_tnum_mul_loop_sound.
      + apply tnum_union_sound_r; auto;
          crush_tnum_mul_loop_sound.
      + apply tnum_union_sound_r; auto;
          crush_tnum_mul_loop_sound.
      + rewrite hbmul0; auto.
      + rewrite hbmul0; auto.
        apply IHm; auto;
          crush_tnum_mul_loop_sound.
      + apply tnum_union_sound_r; auto;
          crush_tnum_mul_loop_sound.
  Qed.

  Lemma tnum_mul_sound (n : nat) : sound2 (S n) bvec_mul tnum_mul.
    unfold sound2.
    unfold tnum_mul.
    intros.
    split.
    - apply tnum_mul_loop_wellformed; auto.
      apply zerotnum_wellformed.
    - apply tnum_mul_loop_sound; auto.
      apply zerotnum_wellformed.
      unfold ingamma. auto.
  Qed.
End linux_tnum_multiplication.
