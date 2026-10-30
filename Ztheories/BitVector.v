(**
 * Bit vector implementation using Z mod 2 ^ SIZE.
 * Quirks, if any, are the remnants of the original uint implementation
 * based on size-limited list.
 *)

(** printing < %\texttt{<}% *)

From Stdlib Require Import
  Lia
  Program (* For ProofIrrelevance *)
  ZArith.

From trirocq.Z Require Import Bit.

Local Open Scope Z_scope.

Section uint.
  Variable SIZE : nat.
  Definition modulus := 2 ^ Z.of_nat SIZE.

  Definition uint := { x | 0 <= x < modulus }.

  Definition uint2Z (a : uint) := proj1_sig a.
  Coercion uint2Z : uint >-> Z.

  Definition Z2uint (n : Z) : uint.
    exists (n mod modulus).
    apply Z.mod_pos_bound.
    unfold modulus. lia.
  Defined.

  (** Using nat instead of Z for backward compatibility *)
  Definition POS := nat.
  Definition POS2Z (n : POS) := Z.of_nat n.
  Coercion POS2Z : POS >-> Z.

  Definition uint_ith (a : uint) (i : POS) := Z.testbit a (POS2Z i).

  Lemma uint_and_pf (a b : uint) :
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

  Definition uint_and (a b : uint) : uint.
    exists (Z.land a b).
    apply uint_and_pf.
  Defined.

  Lemma uint_and_rel (a b : uint) i :
    uint_ith (uint_and a b) i = andb (uint_ith a i) (uint_ith b i).
  Proof.
    unfold uint_ith, uint_and. cbn.
    rewrite Z.land_spec.
    unfold uint2Z. cbn.
    reflexivity.
  Qed.

  Lemma uint_neg_pf (a : uint) :
    0 <= (Z.lnot a) mod modulus < modulus.
  Proof.
    apply Z.mod_pos_bound. unfold modulus. lia.
  Qed.

  Definition uint_neg (a : uint) : uint.
    exists ((Z.lnot a) mod modulus).
    apply uint_neg_pf.
  Defined.

  Lemma uint_neg_rel (a : uint) (i : POS) :
    (i < SIZE)%nat ->
    uint_ith (uint_neg a) i = negb (uint_ith a i).
  Proof.
    unfold uint_ith, uint_neg. cbn.
    unfold modulus, POS2Z.
    intro hi.
    rewrite Z.mod_pow2_bits_low.
    apply Z.lnot_spec.
    lia. lia.
  Qed.

  Lemma Z_land_bounded (a b : Z) (ha : 0 <= a < modulus) (hb : 0 <= b < modulus) :
    0 <= Z.land a b < modulus.
  Proof.
    split.
    - apply Z.land_nonneg. constructor; lia.
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

  Lemma uint_or_pf (a b : uint) :
    0 <= Z.lor a b < modulus.
  Proof.
    apply Z_lor_bounded;
      destruct a, b; auto.
  Qed.

  Definition uint_or (a b : uint) : uint.
    exists (Z.lor a b).
    apply uint_or_pf.
  Defined.

  Lemma uint_or_rel (a b : uint) i :
    uint_ith (uint_or a b) i = orb (uint_ith a i) (uint_ith b i).
  Proof.
    unfold uint_ith, uint_or. cbn.
    rewrite Z.lor_spec.
    unfold uint2Z. cbn.
    reflexivity.
  Qed.

  Lemma uint_xor_pf (a b : uint) :
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

  Definition uint_xor (a b : uint) : uint.
    exists (Z.lxor a b).
    apply uint_xor_pf.
  Defined.

  Lemma uint_xor_rel (a b : uint) i :
    uint_ith (uint_xor a b) i = xorb (uint_ith a i) (uint_ith b i).
  Proof.
    unfold uint_ith, uint_xor. cbn.
    rewrite Z.lxor_spec.
    unfold uint2Z. cbn.
    reflexivity.
  Qed.

  Definition uint_repr (a : Z) : uint.
    exists (a mod modulus).
    apply Z.mod_pos_bound.
    unfold modulus. lia.
  Defined.

  Definition uint_lshift (a : uint) (n : POS) : uint :=
    uint_repr (Z.shiftl a n).

  Lemma uint_rshift_pf (a : uint) (n : POS) :
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

  Definition uint_rshift (a : uint) (n : POS) : uint.
    exists (Z.shiftr a n).
    apply uint_rshift_pf.
  Defined.

  Definition zerovec : uint.
    exists 0. unfold modulus. lia.
  Defined.

  Lemma zerovec_ith i : uint_ith zerovec i = false.
    unfold uint_ith, zerovec. simpl.
    apply Z.bits_0.
  Qed.

  Definition uint_lsb (x : uint) :=
    uint_ith x 0%nat.
End uint.

(* TODO use uint_denote instead of uint2Z in all files
 * to be compatible with the list-based theories.
 *)
Definition uint_denote {SIZE} (a : uint SIZE) :=
  uint2Z _ a.

Arguments uint_ith {SIZE} _ _.
Arguments uint_lsb {SIZE} _.
Arguments uint_and {SIZE} _ _.
Arguments uint_neg {SIZE} _.
Arguments uint_or {SIZE} _ _.
Arguments uint_xor {SIZE} _ _.
Arguments uint_lshift {SIZE} _ _.
Arguments uint_rshift {SIZE} _ _.

Section uint_trunc.
  Definition uint_trunc {n} (p : uint n) {m} (hm : (m <= n)%nat) : uint m.
    destruct p as [p hp].
    exists (p mod modulus m).
    apply Z.mod_pos_bound.
    unfold modulus. lia.
  Defined.
End uint_trunc.

Section uint_rshift1_shrink.
  Variable m : nat.

  Definition uint_rshift1_shrink (a : uint (S m)) : uint m :=
    uint_trunc (uint_rshift a 1%nat) (Nat.le_succ_diag_r m).
End uint_rshift1_shrink.

Arguments uint_rshift1_shrink {m} _.

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
Lemma uint_eq_by_ith : forall {SIZE} (x y : uint SIZE),
    (forall i, (i < SIZE)%nat -> (uint_ith x i) = (uint_ith y i)) -> x = y.
Proof.
  destruct x as [x hx], y as [y hy].
  unfold uint_ith. cbn.
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

Section uint_addition.
  Context {SIZE : nat}.

  Lemma uint_add_pf (x y : Z) :
    0 <= x < modulus SIZE ->
    0 <= y < modulus SIZE ->
    0 <= (x + y) mod (modulus SIZE) < modulus SIZE.
  Proof.
    intros.
    apply Z.mod_pos_bound. lia.
  Qed.

  Definition uint_add (x y : uint SIZE) : uint SIZE.
    destruct x as [x hx], y as [y hy].
    exists ((x + y) mod (modulus SIZE)).
    apply uint_add_pf; lia.
  Defined.

  Lemma uint_add_commutative (x y : uint SIZE) :
    uint_add x y = uint_add y x.
  Proof.
    (* Don't unfold and read the goal first; it's too cluttered. *)
    assert (hcomm : (x + y) mod (modulus SIZE) = (x + y) mod (modulus SIZE)) by lia.
    unfold uint_add.
    destruct x as [x hx], y as [y hy].
    apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    replace (x + y) with (y + x) by lia.
    reflexivity.
  Qed.

  (* TODO rename as uint_ith_incarry *)
  Definition uint_incarry (x y : uint SIZE) (i : POS) :=
    Z.testbit (Z.addcarries x y) i.

  Lemma uint_incarry_0_addcarries (x y : uint SIZE) :
    uint_incarry x y 0%nat = Z.testbit (Z.addcarries x y) 0.
  Proof.
    destruct x, y; auto.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma uint_incarry_Si_addcarries (x y : uint SIZE) (i : POS) :
    uint_incarry x y (S i) = Z.testbit (Z.addcarries x y) (i + 1).
  Proof.
    destruct x, y.
    unfold uint_incarry.
    replace (POS2Z (S i)) with (POS2Z i + 1) by (unfold POS2Z; lia).
    reflexivity.
  Qed.

  Lemma uint_incarry_0 (x y : uint SIZE) :
    uint_incarry x y 0%nat = false.
  Proof.
    rewrite uint_incarry_0_addcarries.
    apply Z.testbit_addcarries_0.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma uint_incarry_Si (x y : uint SIZE) (i : POS) :
    uint_incarry x y (S i) = let a := uint_ith x i in
                             let b := uint_ith y i in
                             let cin := uint_incarry x y i in
                             orb (orb (andb a b) (andb a cin)) (andb b cin).
  Proof.
    unfold uint_incarry.
    rewrite Z.testbit_addcarries_pos.

    destruct x, y. unfold uint_ith. simpl uint2Z.
    replace (POS2Z (S i) - 1) with (POS2Z i).
    repeat destruct (Z.testbit _ _); auto.

    unfold POS2Z. lia.
    unfold POS2Z. lia.
  Qed.

  Lemma uint_fulladd_result : forall x y (i : POS),
      (i < SIZE)%nat ->
      uint_ith (uint_add x y) i =
        xorb (uint_incarry x y i) (xorb (uint_ith x i) (uint_ith y i)).
  Proof.
    intros x y i hi.
    unfold uint_add, uint_ith.
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
      rewrite uint_incarry_0_addcarries.
      rewrite !Z.testbit_addcarries_0.
      rewrite Z.lxor_spec.
      auto.
    - replace (POS2Z (S i)) with (POS2Z i + 1) by (unfold POS2Z; lia).
      rewrite uint_incarry_Si_addcarries.
      unfold uint2Z. simpl.
      rewrite Z.lxor_spec.
      reflexivity.
  Qed.
End uint_addition.

Section poking.
  Definition uint_set_ith {SIZE} (x : uint SIZE) (i : POS) : uint SIZE.
    destruct x as [xs hlen].
    exists ((Z.setbit xs i) mod (2 ^ Z.of_nat SIZE)).
    unfold modulus. unfold modulus in hlen.
    apply Z.mod_pos_bound. lia.
  Defined.

  Lemma uint_ith_set_is_one {SIZE} (x : uint SIZE) (i : POS) (hi : (i < SIZE)%nat) :
    uint_ith (uint_set_ith x i) i = one.
  Proof.
    destruct x as [x hx].
    unfold uint_set_ith, uint_ith. cbn.
    unfold one.
    rewrite <- Z.setbit_eq with (a := x) (n := Z.of_nat i).
    rewrite Z.mod_pow2_bits_low. unfold POS2Z. reflexivity.

    unfold POS2Z. lia.
    lia.
  Qed.

  Lemma uint_ith_unset_is_id {SIZE} (x : uint SIZE)
    i (hi : (i < SIZE)%nat) j (hj : (j < SIZE)%nat) :
    j <> i ->
    uint_ith (uint_set_ith x i) j = uint_ith x j.
  Proof.
    destruct x as [x hx].
    unfold uint_ith, uint_set_ith. cbn.
    intro hij.

    rewrite Z.mod_pow2_bits_low. unfold POS2Z.
    rewrite Z.setbit_neq. reflexivity.
    lia. lia. unfold POS2Z. lia.
  Qed.
End poking.
