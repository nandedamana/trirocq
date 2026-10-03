From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  Bit
  BitVector
  BitMul
  Tnum
  TnumAdd
  TnumUnion.

Local Open Scope Z_scope.

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
    | 0%nat => fun (a : tnum.t 0) n (b acc : tnum.t (S n)) => acc
    | S mp => fun (a : tnum.t (S mp)) n (b acc : tnum.t (S n)) =>
                match (bvec_denote (tnum.v a)), (bvec_denote (tnum.m a)) return (tnum.t (S n)) with
                | 0, 0 => acc
                | _, _ =>
                    let nxt_acc := match bvec_lsb (tnum.v a) with
                                   | true => tnum_add acc b
                                   | false => match bvec_lsb (tnum.m a) with
                                              | true => tnum_union acc (tnum_add acc b)
                                              | false => acc
                                              end
                                   end in
                    let nxt_a := tnum_rshift1_shrink a in
                    let nxt_b := tnum_lshift b 1%nat in
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
    try apply tnum_lshift_wellformed; auto;
    try match goal with
      | [ IH : forall _ _ _ _,
            _ -> _ -> _ ->
            tnum.wellformed (tnum_mul_loop _ _ _ _ _) |-
              tnum.wellformed (tnum_mul_loop _ _ _ _ _) ] =>
          try apply IH
      end;
    try match goal with
      | [ |- tnum.wellformed (match ?e with
                              | false => _
                              | true => _
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

  Lemma knownlsb n (a : bvec (S n)) (A : tnum.t (S n)) :
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

  Lemma lsb_denote_0 : forall n (a : bvec (S n)),
      bvec_denote a = 0 -> bvec_lsb a = zero.
  Proof.
    destruct a as [xs hlenx].
    destruct xs; try easy.
  Qed.

  Lemma denote_known_tnum : forall n (a : bvec n) (A : tnum.t n),
      ingamma a A ->
      bvec_denote (tnum.m A) = 0 ->
      bvec_denote a = bvec_denote (tnum.v A).
  Proof.
    intros n a A iga msk0.
    f_equal.
    apply bvec_eq_by_ith.
    revert msk0 iga.
    destruct a as [xs hlenx].
    destruct A as [[vs hlenv] [ms hlenm]].
    unfold ingamma, tnum.ith_v, tnum.ith_m, bvec_ith.
    simpl. unfold bvec_denote. simpl.

    intros ms0 hm i hi.
    assert (ms0bits : forall n : Z, Z.testbit ms n = false).
    subst. apply Z.bits_0.
    auto.
  Qed.

  Ltac dismiss_absurd :=
    try match goal with
      | [ H : ?x = ?x -> false = true |- _ ] =>
          discriminate H; auto
      | [ H : ?x = ?x -> true = false |- _ ] =>
          discriminate H; auto
      | [ |- _ ] => try bool_imp_easy
      end.

  Lemma bvec_denote_bounded {SIZE} (a : bvec SIZE) :
    0 <= bvec_denote a < modulus SIZE.
  Proof.
    destruct a; auto.
  Qed.

  Lemma tnum_mul_loop_sound :
    forall {m} (A : tnum.t m) (a : bvec m) {n} (B C : tnum.t (S n)) (b c : bvec (S n)),
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
      assert (htblsb := knownlsb _ a A iga).
      assert (htlsb := lsb_wellformed _ A wfa).
      assert (hblsb := lsb_denote_0 _ a).

      assert (hig_rsh : ingamma (bvec_rshift1_shrink a) (tnum_rshift1_shrink A)).
      unfold tnum_rshift1_shrink.
      apply tnum_rshift1_shrink_sound; auto.

      assert (hig_lsh :  ingamma (bvec_lshift b 1%nat) (tnum_lshift B 1%nat)).
      apply tnum_lshift_sound; auto.

      assert (hbmul0 :
               bvec_denote a = 0 ->
               c = bvec_mul_loop m (bvec_rshift1_shrink a) n (bvec_lshift b 1%nat) c).
      intro h.
      unfold bvec_mul_loop.
      destruct m. reflexivity.
      assert (h2 : bvec_denote (bvec_rshift1_shrink a) = 0).
      unfold bvec_rshift1_shrink, bvec_rshift, bvec_trunc, bvec2Z. simpl.
      destruct a as [a' ha] eqn : ades in h; try easy.
      rewrite ades. cbn -[Z.pow].
      simpl in h.
      rewrite h. cbn. reflexivity.
      rewrite h2; auto.

      (* Gets rid of neg *)
      assert (hbounda := bvec_denote_bounded a).
      assert (hboundtvA := bvec_denote_bounded (tnum.v A)).
      assert (hboundtmA := bvec_denote_bounded (tnum.m A)).

      (* So that `auto` can pick it (needed in several cases) *)
      pose (tnum_rshift1_shrink_wellformed A).
      pose (tnum_lshift_wellformed B).

      destruct (bvec_denote (tnum.v A)); try easy; (* easy to get rid of neg *)
        destruct (bvec_denote (tnum.m A)); try easy;
        destruct (bvec_denote a);
        repeat destruct (bvec_lsb _);
        unfold bit_and in htlsb; simpl in htlsb;
        (* lia will get rid of goals where I have
         *  something like `0 = 0 -> S n0 = 0` in the context.
         *)
        try easy;
        unfold zero, one in htblsb, hblsb, htlsb;
        dismiss_absurd;
        try lia;
        try (apply IHm; auto; crush_tnum_mul_loop_sound).

      + rewrite hbmul0; auto.
        apply IHm; auto;
          crush_tnum_mul_loop_sound.
      + rewrite hbmul0; auto.
      + apply tnum_union_sound_r; auto;
          crush_tnum_mul_loop_sound.
      + apply tnum_union_sound_r; auto;
          crush_tnum_mul_loop_sound.
      + rewrite hbmul0; auto. apply IHm; auto;
          crush_tnum_mul_loop_sound.
      + rewrite hbmul0; auto.
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
