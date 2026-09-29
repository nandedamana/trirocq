(**
 * Bit vector implementation using Z mod 2 ^ SIZE.
 * Quirks, if any, are the remnants of the original bvec implementation
 * based on size-limited list.
 *)

From Stdlib Require Import
  Lia
  Program (* For ProofIrrelevance *)
  ZArith.

From trirocq.Z Require Import Bit.

Local Open Scope Z_scope.

Section bvec.
  Variable SIZE : nat.
  Definition modulus := 2 ^ Z.of_nat SIZE.

  Definition bvec := { x | 0 <= x < modulus }.

  Definition bvec2Z (a : bvec) := proj1_sig a.
  Coercion bvec2Z : bvec >-> Z.

  (** Using nat instead of Z for backward compatibility *)
  Definition POS := nat.
  Definition POS2Z (n : POS) := Z.of_nat n.
  Coercion POS2Z : POS >-> Z.

  Definition bvec_ith (a : bvec) (i : POS) := Z.testbit a (POS2Z i).

  Lemma bvec_and_pf (a b : bvec) :
    0 <= Z.land a b < modulus.
  Proof.
    split.
    - apply Z.land_nonneg. destruct a, b. cbn. lia.
    -
      destruct a as [a ha], b as [b hb]. cbn.

      (* Many lemmas used here from the stdlib require
       * this due to how log2 works.
       *)
      assert (hsiz : (SIZE <= 1)%nat \/ (SIZE > 1)%nat). lia.
      destruct hsiz.
      + assert (hsiz' : (SIZE = 0)%nat \/ (SIZE = 1)%nat). lia.
        destruct hsiz' as [hsiz'1 | hsiz'2].
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (a = 0). lia. assert (b = 0). lia.
          destruct a, b; try easy; compute.
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (ha' : a = 0 \/ a = 1). lia. assert (hb' : b = 0 \/ b = 1). lia.
          destruct ha', hb'; subst; cbn [Z.land]; reflexivity.
      +
        (* Z.log2_lt_pow2 can only handle the latter *)
        assert (hge0 : 0 = Z.land a b \/ 0 < Z.land a b).
        assert (h : 0 <= Z.land a b).
        apply Z.land_nonneg. lia.
        apply Z.le_lteq in h. lia.

        destruct hge0.
        unfold modulus. lia.

        apply Z.log2_lt_pow2. assumption.

        assert (ha0le : 0 <= a) by lia.
        assert (ha1le : 0 <= b) by lia.
        assert (h := Z.log2_land a b ha0le ha1le).

        apply Z.le_lt_trans with (m := Z.min (Z.log2 a) (Z.log2 b)).
        assumption.

        assert (ham : a < modulus) by lia.
        assert (hbm : b < modulus) by lia.
        unfold modulus in ha, hb, ham, hbm.

        apply Z.min_lt_iff. constructor.

        assert (ha0gt : 0 = a \/ 0 < a). lia.
        destruct ha0gt as [ha0 | hagt].
        * rewrite <- ha0. cbn. destruct SIZE; lia.
        * apply Z.log2_lt_pow2. assumption. lia.
  Qed.

  Definition bvec_and (a b : bvec) : bvec.
    exists (Z.land a b).
    apply bvec_and_pf.
  Defined.

  Lemma bvec_and_rel (a b : bvec) i :
    bvec_ith (bvec_and a b) i = andb (bvec_ith a i) (bvec_ith b i).
  Proof.
    unfold bvec_ith, bvec_and. cbn.
    rewrite Z.land_spec.
    unfold bvec2Z. cbn.
    reflexivity.
  Qed.

  Lemma bvec_neg_pf (a : bvec) :
    0 <= (Z.lnot a) mod modulus < modulus.
  Proof.
    apply Z.mod_pos_bound. unfold modulus. lia.
  Qed.

  Definition bvec_neg (a : bvec) : bvec.
    exists ((Z.lnot a) mod modulus).
    apply bvec_neg_pf.
  Defined.

  Lemma bvec_neg_rel (a : bvec) (i : POS) :
    (i < SIZE)%nat ->
    bvec_ith (bvec_neg a) i = negb (bvec_ith a i).
  Proof.
    unfold bvec_ith, bvec_neg. cbn.
    unfold modulus, POS2Z.
    intro hi.
    rewrite Z.mod_pow2_bits_low.
    apply Z.lnot_spec.
    lia. lia.
  Qed.

  Lemma Z_lor_bounded (a b : Z) (ha : 0 <= a < modulus) (hb : 0 <= b < modulus) :
    0 <= Z.lor a b < modulus.
  Proof.
    split.
    - apply Z.lor_nonneg. split; lia.
    -
      (* Many lemmas used here from the stdlib require
       * this due to how log2 works.
       *)
      assert (hsiz : (SIZE <= 1)%nat \/ (SIZE > 1)%nat). lia.
      destruct hsiz.
      + assert (hsiz' : (SIZE = 0)%nat \/ (SIZE = 1)%nat). lia.
        destruct hsiz' as [hsiz'1 | hsiz'2].
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (a = 0). lia. assert (b = 0). lia.
          destruct a, b; try easy; compute.
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (ha' : a = 0 \/ a = 1). lia. assert (hb' : b = 0 \/ b = 1). lia.
          destruct ha', hb'; subst; cbn; reflexivity.
      +
        (* Z.log2_lt_pow2 can only handle the latter *)
        assert (hge0 : 0 = Z.lor a b \/ 0 < Z.lor a b).
        assert (h : 0 <= Z.lor a b).
        apply Z.lor_nonneg. lia.
        apply Z.le_lteq in h. lia.

        destruct hge0.
        unfold modulus. lia.

        apply Z.log2_lt_pow2. assumption.

        assert (ha0le : 0 <= a) by lia.
        assert (ha1le : 0 <= b) by lia.
        assert (h := Z.log2_lor a b ha0le ha1le).

        apply Z.le_lt_trans with (m := Z.max (Z.log2 a) (Z.log2 b)). lia.

        assert (ham : a < modulus) by lia.
        assert (hbm : b < modulus) by lia.
        unfold modulus in ha, hb, ham, hbm.

        apply Z.max_lub_lt.
        *
          assert (ha0gt : 0 = a \/ 0 < a). lia.
          destruct ha0gt as [ha0 | hagt].
          rewrite <- ha0. cbn. destruct SIZE; lia.
          apply Z.log2_lt_pow2. assumption. lia.
        *
          assert (hb0gt : 0 = b \/ 0 < b). lia.
          destruct hb0gt as [hb0 | hbgt].
          rewrite <- hb0. cbn. destruct SIZE; lia.
          apply Z.log2_lt_pow2. assumption. lia.
  Qed.

  Lemma bvec_or_pf (a b : bvec) :
    0 <= Z.lor a b < modulus.
  Proof.
    apply Z_lor_bounded;
      destruct a, b; auto.
  Qed.

  Definition bvec_or (a b : bvec) : bvec.
    exists (Z.lor a b).
    apply bvec_or_pf.
  Defined.

  Lemma bvec_or_rel (a b : bvec) i :
    bvec_ith (bvec_or a b) i = orb (bvec_ith a i) (bvec_ith b i).
  Proof.
    unfold bvec_ith, bvec_or. cbn.
    rewrite Z.lor_spec.
    unfold bvec2Z. cbn.
    reflexivity.
  Qed.

  Lemma bvec_xor_pf (a b : bvec) :
    0 <= Z.lxor a b < modulus.
  Proof.
    split.
    - apply Z.lxor_nonneg; destruct a, b; cbn; lia.
    -
      destruct a as [a ha], b as [b hb]. cbn.

      (* Many lemmas used here from the stdlib require
       * this due to how log2 works.
       *)
      assert (hsiz : (SIZE <= 1)%nat \/ (SIZE > 1)%nat). lia.
      destruct hsiz.
      + assert (hsiz' : (SIZE = 0)%nat \/ (SIZE = 1)%nat). lia.
        destruct hsiz' as [hsiz'1 | hsiz'2].
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (a = 0). lia. assert (b = 0). lia.
          destruct a, b; try easy; compute.
        * revert ha hb.
          unfold modulus. subst.
          intros.
          assert (ha' : a = 0 \/ a = 1). lia. assert (hb' : b = 0 \/ b = 1). lia.
          destruct ha', hb'; subst; cbn; reflexivity.
      +
        (* Z.log2_lt_pow2 can only handle the latter *)
        assert (hge0 : 0 = Z.lxor a b \/ 0 < Z.lxor a b).
        assert (h : 0 <= Z.lxor a b).
        apply Z.lxor_nonneg. lia.
        apply Z.le_lteq in h. lia.

        destruct hge0.
        unfold modulus. lia.

        apply Z.log2_lt_pow2. assumption.

        assert (ha0le : 0 <= a) by lia.
        assert (ha1le : 0 <= b) by lia.
        assert (h := Z.log2_lxor a b ha0le ha1le).

        apply Z.le_lt_trans with (m := Z.max (Z.log2 a) (Z.log2 b)). lia.

        assert (ham : a < modulus) by lia.
        assert (hbm : b < modulus) by lia.
        unfold modulus in ha, hb, ham, hbm.

        apply Z.max_lub_lt.
        *
          assert (ha0gt : 0 = a \/ 0 < a). lia.
          destruct ha0gt as [ha0 | hagt].
          rewrite <- ha0. cbn. destruct SIZE; lia.
          apply Z.log2_lt_pow2. assumption. lia.
        *
          assert (hb0gt : 0 = b \/ 0 < b). lia.
          destruct hb0gt as [hb0 | hbgt].
          rewrite <- hb0. cbn. destruct SIZE; lia.
          apply Z.log2_lt_pow2. assumption. lia.
  Qed.

  Definition bvec_xor (a b : bvec) : bvec.
    exists (Z.lxor a b).
    apply bvec_xor_pf.
  Defined.

  Lemma bvec_xor_rel (a b : bvec) i :
    bvec_ith (bvec_xor a b) i = xorb (bvec_ith a i) (bvec_ith b i).
  Proof.
    unfold bvec_ith, bvec_xor. cbn.
    rewrite Z.lxor_spec.
    unfold bvec2Z. cbn.
    reflexivity.
  Qed.

  Lemma bvec_lshift_pf (a : bvec) (n : POS) :
    0 <= (Z.shiftl a n) mod modulus < modulus.
  Proof.
    split.
    - apply Z.mod_pos_bound. unfold modulus. lia.
    - apply Z.mod_bound_pos; try (unfold modulus; lia).
      rewrite Z.shiftl_mul_pow2; try (unfold POS2Z; lia).
      destruct a. cbn. unfold modulus in a. lia.
  Qed.

  Definition bvec_lshift (a : bvec) (n : POS) : bvec.
    exists ((Z.shiftl a n) mod modulus).
    apply bvec_lshift_pf.
  Defined.

  Lemma bvec_rshift_pf (a : bvec) (n : POS) :
    0 <= Z.shiftr a n < modulus.
  Proof.
    rewrite Z.shiftr_div_pow2.
    destruct a as [a ha]. simpl.
    unfold modulus in ha.
    unfold modulus, POS2Z.

    split.
    - apply Z.div_pos. lia.
      apply Z.pow_pos_nonneg; try lia.
    - apply Z.div_lt_upper_bound; nia.
    - unfold POS2Z. lia.
  Qed.

  Definition bvec_rshift (a : bvec) (n : POS) : bvec.
    exists (Z.shiftr a n).
    apply bvec_rshift_pf.
  Defined.

  Definition zerovec : bvec.
    exists 0. unfold modulus. lia.
  Defined.

  Lemma zerovec_ith i : bvec_ith zerovec i = false.
    unfold bvec_ith, zerovec. simpl.
    apply Z.bits_0.
  Qed.
End bvec.

Arguments bvec_ith {SIZE} _ _.
Arguments bvec_and {SIZE} _ _.
Arguments bvec_neg {SIZE} _.
Arguments bvec_or {SIZE} _ _.
Arguments bvec_xor {SIZE} _ _.
Arguments bvec_lshift {SIZE} _ _.
Arguments bvec_rshift {SIZE} _ _.

Lemma eq_by_POS_imp_eq_by_Z x y :
  (forall i : POS, Z.testbit x (Z.of_nat i) = Z.testbit y (Z.of_nat i)) ->
    (forall i : Z, Z.testbit x i = Z.testbit y i).
Proof.
  intros H i.
  destruct i as [i0 | pi | ni] eqn : hi.
  - specialize (H 0%nat). auto.
  - specialize (H (Z.to_nat i)).
    rewrite Z2Nat.id in H by lia.
    rewrite <- hi. assumption.
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma bvec_eq_by_ith : forall {SIZE} (x y : bvec SIZE),
    (forall i, (bvec_ith x i) = (bvec_ith y i)) -> x = y.
Proof.
  destruct x as [x hx], y as [y hy].
  unfold bvec_ith. cbn.
  intro H. assert (H' := Z.bits_inj x y).
  Set Printing Coercions.
  unfold Z.eqf in H'.
  assert (hnat := eq_by_POS_imp_eq_by_Z x y H).
  apply H' in hnat.
  apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  assumption.
Qed.
