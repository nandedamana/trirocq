From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  BitVector.

Require Import VST.floyd.proofauto.

Local Open Scope Z_scope.

Definition u64 := uint 64.

Lemma uint64_not_repr :
  forall x,
    Int64.repr ((Z.lnot x) mod modulus 64) = Int64.not (Int64.repr x).
Proof.
  intro x.
  unfold Int64.not.
  unfold Int64.xor.
  f_equal.
  rewrite <- Z.lxor_m1_r.
  rewrite Int64.unsigned_repr_eq.
  rewrite Int64.unsigned_mone.
  apply Z.bits_inj'.
  intros i hi.
  replace Int64.modulus with (modulus 64) by (compute; auto).
  unfold modulus.
  destruct (zlt i 64).
  -
    rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_low by lia.

    replace (- (1)) with (-0 - 1) by lia.
    rewrite Zbits.Z_one_complement by lia.
    replace (2 ^ Z.of_nat 64 - 1) with (Z.ones 64).

    rewrite Z.bits_0.
    rewrite Z.ones_spec_low by lia. auto.
    rewrite Z.ones_equiv. lia.
  -
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_high by lia.
    replace (2 ^ Z.of_nat 64 - 1) with (Z.ones 64).
    rewrite Z.ones_spec_high by lia. auto.
    rewrite Z.ones_equiv. lia.
Qed.

Module Int64.
  Lemma not_to_uint_neg :
    forall (x : uint 64),
      Int64.not (Int64.repr (uint2Z 64 x)) = Int64.repr (uint2Z 64 (uint_neg x)).
  Proof.
    destruct x as [x hx].
    unfold uint_neg. cbn.
    rewrite uint64_not_repr.
    reflexivity.
  Qed.

  Section Int64bin.
    Variable x y : uint 64.

    Lemma or_repruint :
        Int64.or (Int64.repr (uint2Z _ x)) (Int64.repr (uint2Z _ y)) =
          Int64.repr (uint_or x y).
    Proof.
      destruct x, y. cbn.
      unfold Int64.or.
      rewrite !Int64.unsigned_repr_eq.
      replace Int64.modulus with (modulus 64).
      rewrite !Z.mod_small by lia. reflexivity.
      compute. reflexivity.
    Qed.

    Lemma and_repruint :
      Int64.and (Int64.repr (uint2Z _ x)) (Int64.repr (uint2Z _ y)) =
        Int64.repr (uint_and x y).
    Proof.
      destruct x, y. cbn.
      unfold Int64.and.
      rewrite !Int64.unsigned_repr_eq.
      replace Int64.modulus with (modulus 64).
      rewrite !Z.mod_small by lia. reflexivity.
      compute. reflexivity.
    Qed.

    Lemma lshift_repruint {ssz} (shift : uint ssz) :
      (ssz < 64)%nat ->
      Int64.shl (Int64.repr (uint2Z _ x)) (Int64.repr (uint2Z _ shift)) =
        Int64.repr (uint_lshift x (Z.to_nat shift)).
    Proof.
      intro hssz.
      destruct x, y, shift. cbn.
      unfold Int64.shl.
      apply Int64.eqm_samerepr.
      apply Int64.eqm_same_bits.
      intros i hi.

      replace 18446744073709551616 with (2 ^ 64) by lia.
      rewrite Z.mod_pow2_bits_low.

      rewrite !Int64.unsigned_repr.
      unfold POS2Z.
      rewrite Z2Nat.id. reflexivity.

      lia.

      assert (x2 < modulus 64).
      assert (modulus ssz < modulus 64).
      unfold modulus in *.
      apply Z.pow_lt_mono_r; try lia.
      lia.

      unfold Int64.max_unsigned.
      replace Int64.modulus with (modulus 64) by (compute; lia).
      split; try lia.

      unfold Int64.max_unsigned.
      replace Int64.modulus with (modulus 64) by (compute; lia).
      split; try lia.

      revert hi. compute. destruct i; try easy.
    Qed.

    Lemma rshift_repruint {ssz} (shift : uint ssz) :
      (ssz < 64)%nat ->
      Int64.shru (Int64.repr (uint2Z _ x)) (Int64.repr (uint2Z _ shift)) =
        Int64.repr (uint_rshift x (Z.to_nat shift)).
    Proof.
      intro hssz.
      destruct x, y, shift. cbn.
      unfold Int64.shru.
      apply Int64.eqm_samerepr.
      apply Int64.eqm_same_bits.
      intros i hi.

      rewrite !Int64.unsigned_repr.
      unfold POS2Z.
      rewrite Z2Nat.id. reflexivity.

      lia.

      assert (x2 < modulus 64).
      assert (modulus ssz < modulus 64).
      unfold modulus in *.
      apply Z.pow_lt_mono_r; try lia.
      lia.

      unfold Int64.max_unsigned.
      replace Int64.modulus with (modulus 64) by (compute; lia).
      split; try lia.

      unfold Int64.max_unsigned.
      replace Int64.modulus with (modulus 64) by (compute; lia).
      split; try lia.
    Qed.
  End Int64bin.
End Int64.

Module Z.
  Section Zbin.
    Variable SIZE : nat.
    Variable av bv : uint SIZE.

    Lemma land_uint :
      Z.land (uint2Z _ av) (uint2Z _ bv) = uint2Z _ (uint_and av bv).
    Proof.
      destruct av, bv. cbn. reflexivity.
    Qed.

    Lemma lxor_uint :
      Z.lxor (uint2Z _ av) (uint2Z _ bv) = uint2Z _ (uint_xor av bv).
    Proof.
      destruct av, bv. cbn. reflexivity.
    Qed.
  End Zbin.
End Z.

Lemma mod_uint2Z x : uint2Z 64 x mod Int64.modulus = uint2Z 64 x.
  destruct x as [x hx]. cbn.
  replace Int64.modulus with (modulus 64).
  rewrite !Z.mod_small by lia. reflexivity.
  compute. reflexivity.
Qed.
