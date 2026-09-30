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
  destruct i eqn : hi.
  - specialize (H 0%nat). auto.
  - specialize (H (Z.to_nat i)).
    rewrite Z2Nat.id in H by lia.
    rewrite <- hi. assumption.
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
Qed.

(* Many proofs will be range-bound, unable to show bitwise equality
 * for the whole range. This lemma helps them establish numerical
 * equality without passing in proof of unbounded bitwise equality.
 *)
Lemma bvec_eq_by_ith : forall {SIZE} (x y : bvec SIZE),
    (forall i, (i < SIZE)%nat -> (bvec_ith x i) = (bvec_ith y i)) -> x = y.
Proof.
  destruct x as [x hx], y as [y hy].
  unfold bvec_ith. cbn.
  intro H. assert (H' := Z.bits_inj x y).
  Set Printing Coercions.
  unfold Z.eqf in H'.

  assert (H'' : forall i : nat, Z.testbit x (POS2Z i) = Z.testbit y (POS2Z i)).
  intro i.
  assert (hi : (i < SIZE)%nat \/ (i >= SIZE)%nat) by lia.
  destruct hi as [hi1 | hi2].
  - exact (H i hi1).
  -
    replace x with (Z.land x (Z.ones (Z.of_nat SIZE))).
    replace y with (Z.land y (Z.ones (Z.of_nat SIZE))).
    rewrite !Z.land_spec.
    rewrite !Z.ones_spec_high.
    rewrite !Bool.andb_false_r. reflexivity.

    unfold POS2Z. lia.

    assert (hy' : y < 2 ^ Z.of_nat SIZE). unfold modulus in hy. lia.
    rewrite Z.land_ones.
    apply Z.mod_small. lia. lia.

    assert (hx' : x < 2 ^ Z.of_nat SIZE). unfold modulus in hx. lia.
    rewrite Z.land_ones.
    apply Z.mod_small. lia. lia.
  -
    assert (hnat := eq_by_POS_imp_eq_by_Z x y H'').
    apply H' in hnat.
    apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    assumption.
Qed.

Section bvec_addition.
  Context {SIZE : nat}.

  Lemma bvec_add_pf (x y : Z) :
    0 <= x < modulus SIZE ->
    0 <= y < modulus SIZE ->
    0 <= (x + y) mod (modulus SIZE) < modulus SIZE.
  Proof.
    intros.
    apply Z.mod_pos_bound. lia.
  Qed.

  Definition bvec_add (x y : bvec SIZE) : bvec SIZE.
    destruct x as [x hx], y as [y hy].
    exists ((x + y) mod (modulus SIZE)).
    apply bvec_add_pf; lia.
  Defined.

  Lemma bvec_add_commutative (x y : bvec SIZE) :
    bvec_add x y = bvec_add y x.
  Proof.
    (* Don't unfold and read the goal first; it's too cluttered. *)
    assert (hcomm : (x + y) mod (modulus SIZE) = (x + y) mod (modulus SIZE)) by lia.
    unfold bvec_add.
    destruct x as [x hx], y as [y hy].
    apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    replace (x + y) with (y + x) by lia.
    reflexivity.
  Qed.

  (* TODO rename as bvec_ith_incarry *)
  Definition bvec_incarry (x y : bvec SIZE) (i : POS) :=
    Z.testbit (Z.addcarries x y) i.

  Lemma bvec_incarry_0_addcarries (x y : bvec SIZE) :
    bvec_incarry x y 0%nat = Z.testbit (Z.addcarries x y) 0.
  Proof.
    destruct x, y; auto.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma bvec_incarry_Si_addcarries (x y : bvec SIZE) (i : POS) :
    bvec_incarry x y (S i) = Z.testbit (Z.addcarries x y) (i + 1).
  Proof.
    destruct x, y.
    unfold bvec_incarry.
    replace (POS2Z (S i)) with (POS2Z i + 1) by (unfold POS2Z; lia).
    reflexivity.
  Qed.

  Lemma bvec_incarry_0 (x y : bvec SIZE) :
    bvec_incarry x y 0%nat = false.
  Proof.
    rewrite bvec_incarry_0_addcarries.
    apply Z.testbit_addcarries_0.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma bvec_incarry_Si (x y : bvec SIZE) (i : POS) :
    bvec_incarry x y (S i) = let a := bvec_ith x i in
                         let b := bvec_ith y i in
                         let cin := bvec_incarry x y i in
                         orb (orb (andb a b) (andb a cin)) (andb b cin).
  Proof.
    unfold bvec_incarry.
    rewrite Z.testbit_addcarries_pos.

    destruct x, y. unfold bvec_ith. simpl bvec2Z.
    replace (POS2Z (S i) - 1) with (POS2Z i).
    repeat destruct (Z.testbit _ _); auto.

    unfold POS2Z. lia.
    unfold POS2Z. lia.
  Qed.

  Lemma bvec_fulladd_result : forall x y (i : POS),
      (i < SIZE)%nat ->
      bvec_ith (bvec_add x y) i =
        xorb (bvec_incarry x y i) (xorb (bvec_ith x i) (bvec_ith y i)).
  Proof.
    intros x y i hi.
    unfold bvec_add, bvec_ith.
    destruct x as [x hx], y as [y hy]. simpl.

      unfold modulus.
      rewrite Z.testbit_mod_pow2 by lia.

      replace (POS2Z i <? Z.of_nat SIZE) with true by (unfold POS2Z; lia).
      simpl.

      assert (hsum : forall x y, x + y = Z.lxor (Z.addcarries x y) (Z.lxor x y)).
      unfold Z.addcarries.
      intros x' y'.
      rewrite Z.lxor_assoc.
      rewrite Z.lxor_nilpotent.
      rewrite Z.lxor_0_r. reflexivity.

      rewrite hsum.
      rewrite Z.lxor_spec.

      destruct i.
      - replace (POS2Z 0%nat) with 0 by (unfold POS2Z; lia).
        rewrite bvec_incarry_0_addcarries.
        rewrite !Z.testbit_addcarries_0.
        rewrite Z.lxor_spec.
        auto.
      - replace (POS2Z (S i)) with (POS2Z i + 1) by (unfold POS2Z; lia).
        rewrite bvec_incarry_Si_addcarries.
        unfold bvec2Z. simpl.
        rewrite Z.lxor_spec.
        reflexivity.
  Qed.
End bvec_addition.

Section poking.
  Definition bvec_set_ith {SIZE} (x : bvec SIZE) (i : POS) : bvec SIZE.
    destruct x as [xs hlen].
    exists ((Z.setbit xs i) mod (2 ^ Z.of_nat SIZE)).
    unfold modulus. unfold modulus in hlen.
    apply Z.mod_pos_bound. lia.
  Defined.

  Lemma bvec_ith_set_is_one {SIZE} (x : bvec SIZE) (i : POS) (hi : (i < SIZE)%nat) :
    bvec_ith (bvec_set_ith x i) i = one.
  Proof.
    destruct x as [x hx].
    unfold bvec_set_ith, bvec_ith. cbn.
    unfold one.
    rewrite <- Z.setbit_eq with (a := x) (n := Z.of_nat i).
    rewrite Z.mod_pow2_bits_low. unfold POS2Z. reflexivity.

    unfold POS2Z. lia.
    lia.
  Qed.

  Lemma bvec_ith_unset_is_id {SIZE} (x : bvec SIZE)
    i (hi : (i < SIZE)%nat) j (hj : (j < SIZE)%nat) :
    j <> i ->
    bvec_ith (bvec_set_ith x i) j = bvec_ith x j.
  Proof.
    destruct x as [x hx].
    unfold bvec_ith, bvec_set_ith. cbn.
    intro hij.

    rewrite Z.mod_pow2_bits_low. unfold POS2Z.
    rewrite Z.setbit_neq. reflexivity.
    lia. lia. unfold POS2Z. lia.
  Qed.
End poking.
