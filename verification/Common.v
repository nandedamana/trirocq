From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  BitVector.

Require Import VST.floyd.proofauto.

Local Open Scope Z_scope.

Definition u64 := bvec 64.

Lemma bvec64_not_repr :
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
  Lemma not_to_bvec_neg :
    forall (x : bvec 64),
      Int64.not (Int64.repr (bvec2Z 64 x)) = Int64.repr (bvec2Z 64 (bvec_neg x)).
  Proof.
    destruct x as [x hx].
    unfold bvec_neg. cbn.
    rewrite bvec64_not_repr.
    reflexivity.
  Qed.

  Section Int64bin.
    Variable x y : bvec 64.

    Lemma or_reprbvec :
        Int64.or (Int64.repr (bvec2Z _ x)) (Int64.repr (bvec2Z _ y)) =
          Int64.repr (bvec_or x y).
    Proof.
      destruct x, y. cbn.
      unfold Int64.or.
      rewrite !Int64.unsigned_repr_eq.
      replace Int64.modulus with (modulus 64).
      rewrite !Z.mod_small by lia. reflexivity.
      compute. reflexivity.
    Qed.

    Lemma and_reprbvec :
      Int64.and (Int64.repr (bvec2Z _ x)) (Int64.repr (bvec2Z _ y)) =
        Int64.repr (bvec_and x y).
    Proof.
      destruct x, y. cbn.
      unfold Int64.and.
      rewrite !Int64.unsigned_repr_eq.
      replace Int64.modulus with (modulus 64).
      rewrite !Z.mod_small by lia. reflexivity.
      compute. reflexivity.
    Qed.
  End Int64bin.
End Int64.

Module Z.
  Section Zbin.
    Variable SIZE : nat.
    Variable av bv : bvec SIZE.

    Lemma land_bvec :
      Z.land (bvec2Z _ av) (bvec2Z _ bv) = bvec2Z _ (bvec_and av bv).
    Proof.
      destruct av, bv. cbn. reflexivity.
    Qed.

    Lemma lxor_bvec :
      Z.lxor (bvec2Z _ av) (bvec2Z _ bv) = bvec2Z _ (bvec_xor av bv).
    Proof.
      destruct av, bv. cbn. reflexivity.
    Qed.
  End Zbin.
End Z.

Lemma mod_bvec2Z x : bvec2Z 64 x mod Int64.modulus = bvec2Z 64 x.
  destruct x as [x hx]. cbn.
  replace Int64.modulus with (modulus 64).
  rewrite !Z.mod_small by lia. reflexivity.
  compute. reflexivity.
Qed.
