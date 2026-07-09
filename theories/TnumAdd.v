From Stdlib Require Import Lia. (* TODO rem if not needed *)

Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.Tnum.

(** printing < %\texttt{<}% *)

Ltac specialize_wf_ig hi :=
  match goal with
  |[ H : forall i (hi' : i < _), bvec_ith _ hi' = _ -> bvec_ith _ _ = _ |- _ ] =>
     specialize (H _ hi); try specialize_wf_ig hi
  |[ H : forall i (hi' : i < _), bvec_incarry _ _ hi' = _ -> bvec_incarry _ _ _ = _ |- _ ] =>
     specialize (H _ hi); try specialize_wf_ig hi
  |[ H : forall i (hi' : i < _), bvec_inborrow _ _ hi' = _ -> bvec_inborrow _ _ _ = _ |- _ ] =>
     specialize (H _ hi); try specialize_wf_ig hi
  end.

Ltac dismiss_absurd :=
  try match goal with
    | [ H : ?x = ?x -> zero = one |- _ ] =>
        discriminate H; auto
    | [ H : ?x = ?x -> one = zero |- _ ] =>
        discriminate H; auto
    end.

(* TODO rename *)
Ltac crush11 :=
  match goal with
    [ |- _ ] =>
      repeat (destruct (bvec_ith _ _); dismiss_absurd;
              simplify_bit_ops; try easy);
      repeat (destruct (bvec_incarry _ _ _); dismiss_absurd;
              simplify_bit_ops; try easy);
      repeat (destruct (bvec_inborrow _ _ _); dismiss_absurd;
              simplify_bit_ops; try easy);
      intuition
  end.

Section linux_tnum_addition.
  (* Mirrors the Linux kernel definition *)

  Definition tnum_ith_chi {SIZE} P Q [i] (hidx : i < SIZE) :=
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    bvec_ith chi hidx.

  Definition tnum_add {SIZE} P Q :=
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    let eta := bvec_or chi (bvec_or (tnum.m P) (tnum.m Q)) in
    tnum.cons SIZE (bvec_and sv (bvec_neg eta)) eta.

  Definition value_sum {SIZE} (P Q : tnum.t SIZE) :=
    bvec_add (tnum.v P) (tnum.v Q).

  Definition mask_sum {SIZE} (P Q : tnum.t SIZE) :=
    bvec_add (tnum.m P) (tnum.m Q).

  Definition ith_mask_incarry {SIZE} P Q {i} (hidx : i < SIZE) :=
    bvec_incarry (tnum.m P) (tnum.m Q) hidx.

  Definition ith_value_incarry {SIZE} P Q {i} (hidx : i < SIZE) :=
    bvec_incarry (tnum.v P) (tnum.v Q) hidx.

  Definition ith_value_mask_incarry {SIZE} P Q {i} (hidx : i < SIZE) :=
    bvec_incarry (value_sum P Q) (mask_sum P Q) hidx.

  Ltac unfold_tnum_goodies :=
    unfold tnum.wellformed; unfold ingamma;
    unfold tnum_ith_chi;
    unfold tnum.ith_v; unfold tnum.ith_m;
    unfold ith_value_mask_incarry;
    unfold ith_mask_incarry; unfold ith_value_incarry;
    unfold value_sum; unfold mask_sum.

  (* Is chi is the mask bit of the incoming carry? No; it considers v bits
   * as well. chi[i] in fact `tnum.ith_m (tnum_add P Q) hidx` excluding
   * P.m[i] | Q.m[i]
   *)
  Lemma hlp_tnum_add_no_mask_imp_known_inputs {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      tnum.ith_m P hidx = zero /\ tnum.ith_m Q hidx = zero /\
        tnum_ith_chi P Q hidx = zero.
  Proof.
    unfold_tnum_goodies.
    intros wf1 wf2 i hidx.
    specialize (wf1 i hidx).
    specialize (wf2 i hidx).

    destruct i;
      unfold tnum_add;
      rewrite tnum.ith_m_simplify2;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fulladd_result;
      unfold bvec_incarry;
      repeat destruct (bvec_ith (tnum.m _) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  Lemma hlp_tnum_add_incarry_exmv {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (ith_mask_incarry P Q hidx) (ith_value_incarry P Q hidx) = zero.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq.
    induction i.
    - intro. repeat rewrite bvec_incarry_0. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.

      specialize (IHi (ltprv hidx)).
      specialize_wf_ig (ltprv hidx).
      crush11.
  Qed.

  (* Interesting: proving only one side would seem easier, but it is actually
   * difficult, if not impossible. I suppose it is because that way the
   * induction hypothesis becomes weaker.
   *)
  Lemma helper63 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      let vm_incarry := ith_value_mask_incarry P Q hidx in
      bit_and (ith_mask_incarry P Q hidx) vm_incarry = zero /\
        bit_and (ith_value_incarry P Q hidx) vm_incarry = zero.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq.
    induction i.
    - intro. repeat rewrite bvec_incarry_0. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si.
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 := hlp_tnum_add_incarry_exmv _ _ wfp wfq (ltprv hidx)).
      revert h66. unfold_tnum_goodies.

      specialize_wf_ig (ltprv hidx).

      repeat destruct (bvec_ith _ _);
        repeat destruct (bvec_incarry _ _ _);
        simplify_bit_ops; try easy; intuition.
  Qed.

  Lemma specialize_wf_ig {SIZE} {x y} {P Q : tnum.t SIZE} :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall  {i} (hidx : i < SIZE),
      (bvec_ith (tnum.m P) hidx = one -> bvec_ith (tnum.v P) hidx = zero) /\
        (bvec_ith (tnum.m Q) hidx = one -> bvec_ith (tnum.v Q) hidx = zero) /\
        (bvec_ith (tnum.m P) hidx = zero -> bvec_ith x hidx = bvec_ith (tnum.v P) hidx) /\
        (bvec_ith (tnum.m Q) hidx = zero -> bvec_ith y hidx = bvec_ith (tnum.v Q) hidx).
  Proof.
    auto.
  Qed.

  Lemma helper45 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : S i < SIZE),
      ith_mask_incarry P Q hidx = zero ->
      ith_value_mask_incarry P Q hidx = zero ->
      bvec_incarry x y hidx = ith_value_incarry P Q hidx.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq igp igq.

    induction i.
    - intro hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.
      repeat rewrite bvec_incarry_0. repeat simplify_bit_ops.

      specialize_wf_ig (ltprv hidx).
      crush11.
    - intro hidx.
      rewrite bvec_incarry_Si.
      rewrite bvec_incarry_Si with (x := x).
      repeat rewrite bvec_incarry_Si with (hidx := hidx).
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      pose (H := specialize_wf_ig wfp wfq igp igq (ltprv hidx)).
      destruct H as (wfps & wfqs & igps & igqs).

      assert (h66 := hlp_tnum_add_incarry_exmv P Q wfp wfq (ltprv hidx)).
      assert (h64 := helper63 P Q wfp wfq (ltprv hidx)).
      revert h66. revert h64. unfold_tnum_goodies.

      crush11.
  Qed.

  Lemma helper82 [x] [y] : bit_xor x y = zero -> bit_and y x = zero -> x = zero /\ y = zero.
    unfold bit_xor. unfold bit_and. destruct x; destruct y; auto.
  Qed.

  Lemma helper33 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      bvec_incarry x y hidx = ith_value_incarry P Q hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq igP igQ.
    destruct i.
    - intro. unfold ith_value_incarry. repeat rewrite bvec_incarry_0.
      auto.
    -
      intros hidx.
      unfold tnum_add.
      rewrite tnum.ith_m_simplify.
      unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.

      intro H.
      assert (hmp : bvec_ith (tnum.m P) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m P) hidx);
        repeat simplify_bit_ops; try easy.

      assert (hmq : bvec_ith (tnum.m Q) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m Q) hidx);
        repeat simplify_bit_ops; try easy.

      apply bit_or_zero_zero in H as (H1 & H2).
      apply bit_xor_x_y_zero in H1.
      apply bit_xor_x_y_z_y in H1.

      revert H1. rewrite hmp. rewrite hmq. repeat simplify_bit_ops.

      pose (h63 := helper63 P Q wfp wfq hidx).
      destruct h63 as (h1 & h2). intro h3.
      pose (h82 := helper82 h3 h1). destruct h82.
      apply helper45; auto.
  Qed.

  Lemma wellformed_general {SIZE} inval mu :
    forall [i] (hidx : i < SIZE),
      bvec_ith mu hidx = one -> bvec_ith (bvec_and inval (bvec_neg mu)) hidx = zero.
  Proof.
    intros i hidx H.
    unwrap_bvec_ops. rewrite H. simpl.
    destruct (bvec_ith inval hidx); auto.
  Qed.

  Lemma tnum_add_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed (tnum_add P Q).
  Proof.
    unfold tnum.wellformed.
    intros h1 h2.
    unfold tnum_add.
    apply wellformed_general.
  Qed.

  (* Soundness: the result of adding abstract numbers P and Q include the results
   * of adding any concrete p and q (written less formally for simplicity).
   *)
  Lemma tnum_add_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    tnum.wellformed (tnum_add P Q) /\
      ingamma (bvec_add x y) (tnum_add P Q).
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq igP igQ.

    split. apply tnum_add_wellformed; auto.

    intros i hidx rmskz.

    assert (H33 := helper33 x y P Q wfp wfq igP igQ hidx rmskz).
    assert (H32 := hlp_tnum_add_no_mask_imp_known_inputs P Q wfp wfq hidx rmskz).
    revert H32 H33. unfold_tnum_goodies. intros H32 H33.

    destruct H32 as (xmskz & ymskz & cinmskz).
    revert cinmskz rmskz.

    unfold tnum_add.
    rewrite tnum.ith_m_simplify2.
    rewrite tnum.ith_v_simplify2.

    unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
    rewrite xmskz. rewrite ymskz. rewrite igP; auto. rewrite igQ; auto. simpl.

    intros H1 H2.

    (* Replaces the subexpression H2 from the goal with zero because it is
     * the ith bit of `mu` (the `mu` from `sv & ~mu`), which is zero as per
     * the assumption.
     *)
    rewrite H2. simpl.
    rewrite H33.
    rewrite bit_and_right_one.
    auto.
  Qed.

  (* TODO rem/archive the optimality lemma that follows Vishwanathan et al. *)
  Section tnum_add_optimality_me.

    (* - Recall: chi is `tnum.ith_m (tnum_add P Q) hidx` excluding P.m[i] | Q.m[i]
     * - Comparable to hlp_tnum_add_no_mask_imp_known_inputs.
     *)
    Lemma tnum_add_mu_imp_inputs_mu {SIZE} P Q :
      forall [i] (hidx : i < SIZE),
        tnum.ith_m (tnum_add P Q) hidx = one ->
        tnum.ith_m P hidx = one \/ tnum.ith_m Q hidx = one \/
          tnum_ith_chi P Q hidx = one.
    Proof.
      unfold_tnum_goodies.
      intros i hidx.

      destruct i;
        unfold tnum_add;
        rewrite tnum.ith_m_simplify2;
        unwrap_bvec_ops; unfold tnum.ith_m;
        rewrite bvec_fulladd_result;
        unfold bvec_incarry;
        repeat destruct (bvec_ith (tnum.m _) hidx); try auto;
        repeat simplify_bit_ops; try auto.
    Qed.

    Lemma ingamma_value_bitor_mask :
      forall SIZE (P : tnum.t SIZE),
        ingamma (bvec_or (tnum.v P) (tnum.m P)) P.
    Proof.
      intros SIZE P.
      unfold ingamma. unfold_tnum_goodies.
      intros i hidx.
      rewrite bvec_or_rel.
      destruct (bvec_ith (tnum.m P) hidx); simplify_bit_ops; easy.
    Qed.

    Lemma bit_xor_one_imp x y :
      bit_xor x y = one -> bit_or x y = one /\ bit_and x y = zero.
    Proof.
      destruct x, y; auto.
    Qed.

    (* TODO not just to prove the new optimality lemma;
     * might be useful simplify some existing helpers I wrote for
     * tnum_add_sound.
     *)
    Lemma tnum_incarry_v_m_0 {SIZE} P i (hidx : i < SIZE) :
      tnum.wellformed P ->
      bvec_incarry (tnum.v P) (tnum.m P) hidx = zero.
    Proof.
      induction i.
      - rewrite bvec_incarry_0. reflexivity.
      - rewrite bvec_incarry_Si. simpl.
        intro wfp.
        rewrite IHi; auto.
        simplify_bit_ops.
        unfold tnum.wellformed in wfp.
        specialize (wfp i (ltprv hidx)).
        repeat destruct (bvec_ith _ _); auto.
    Qed.

    (* TODO try to simplify tnum_add_sound and sublemmas using bvec_eq_by_ith *)

    (* OR eqiv. ADD since both value and mask cannot be 1 at i *)
    (* TODO doc better: the need for this lemma is the fact that
     * the min(P) is (P.v) and [IMPORTANT] max(P) is (P.v | P.m).
     * Rewriting this as P.v + P.m is an optimization that
     * tnum_add uses.
     *)
    (* TODO see if I can improve othe proofs based on this. *)
    Lemma tnum_add_v_m_is_or {SIZE} (P : tnum.t SIZE) :
      tnum.wellformed P ->
      bvec_or (tnum.v P) (tnum.m P) =
        bvec_add (tnum.v P) (tnum.m P).
    Proof.
      intro wfp.
      apply bvec_eq_by_ith.
      intros i hidx.
      rewrite bvec_fulladd_result.
      rewrite tnum_incarry_v_m_0; auto.
      simplify_bit_ops.
      rewrite bvec_or_rel.
      unfold tnum.wellformed in wfp.
      specialize (wfp i hidx).
      destruct (bvec_ith (tnum.m P) _).
      - destruct (bvec_ith (tnum.v P) _); auto.
      - rewrite wfp; auto.
    Qed.

    Lemma bvec_add_regroup : forall {SIZE} (a b c d : bvec SIZE),
        bvec_add (bvec_add a b) (bvec_add c d) =
          bvec_add (bvec_add a c) (bvec_add b d).
    Proof.
      intros. apply eqdenote_imp_eqvec.
      repeat rewrite bvec_add_correct.
      repeat rewrite <- PeanoNat.Nat.Div0.add_mod.
      replace (bvec_denote a + bvec_denote b + (bvec_denote c + bvec_denote d)) with
        (bvec_denote a + bvec_denote c + (bvec_denote b + bvec_denote d)).
      lia. lia.
    Qed.

    Lemma tnum_add_sv_sm_as_or {SIZE} P Q i (hidx : i < SIZE) :
      tnum.wellformed P -> tnum.wellformed Q ->
      bvec_ith
        (bvec_add (bvec_add (tnum.v P) (tnum.v Q))
           (bvec_add (tnum.m P) (tnum.m Q)))
        hidx =
        bvec_ith (bvec_add (bvec_or (tnum.v P) (tnum.m P))
                    (bvec_or (tnum.v Q) (tnum.m Q)))
          hidx.
    Proof.
      rewrite bvec_add_regroup.
      intros.
      repeat rewrite tnum_add_v_m_is_or; auto.
    Qed.

    Lemma tnum_ingamma_set_at_mask {SIZE} P i (hidx : i < SIZE) :
      tnum.wellformed P ->
      tnum.ith_m P hidx = one ->
      ingamma (BitVector.bvec_set_ith (tnum.v P) hidx) P.

    Proof.
      unfold_tnum_goodies.
      intros wfp msk1.
      intros i' hi'.
      assert (hiex : i' = i \/ i' <> i). lia.
      destruct hiex as [hieq | hine].
      - replace (bvec_ith (tnum.m P) hi') with (bvec_ith (tnum.m P) hidx).
        rewrite msk1. easy.
        unfold bvec_ith. subst. apply SigVector.Vector.nth_order_eq.
      - enough (igv : ingamma (tnum.v P) P).
        revert igv. unfold_tnum_goodies.
        pose (H := bvec_ith_unset_is_id (tnum.v P) hidx hi').
        intros; auto.
        split.
    Qed.

    Lemma bvec_ith_set_prv_carry_intact {SIZE} (x y : bvec SIZE) i (hi : i < SIZE) j (hj : j < SIZE) :
      j < i ->
      bvec_incarry x y hj = bvec_incarry (BitVector.bvec_set_ith x hi) y hj.
    Proof.
      induction j.
      - repeat rewrite bvec_incarry_0. auto.
      - repeat rewrite bvec_incarry_Si.

        intro sjlti. assert (j < i). lia.

        rewrite bvec_ith_unset_is_id.
        rewrite IHj.
        auto. auto. lia.
    Qed.

    Lemma bvec_ith_set_sets_ith_sum {SIZE} (x y : bvec SIZE) i (hidx : i < SIZE) :
      bvec_ith x hidx = zero ->
      bvec_ith (bvec_add x y) hidx <>
        bvec_ith (bvec_add (BitVector.bvec_set_ith x hidx) y) hidx.
    Proof.
      repeat rewrite bvec_fulladd_result.
      destruct i.
      - repeat rewrite bvec_incarry_0.
        rewrite bvec_ith_set_is_one.
        simplify_bit_ops.
        repeat destruct (bvec_ith _ _); easy.
      - repeat rewrite bvec_incarry_Si. simpl.
        rewrite bvec_ith_unset_is_id; auto.
        repeat rewrite bvec_ith_set_is_one.
        rewrite bvec_ith_set_prv_carry_intact with (hi := hidx); auto.

        repeat destruct (bvec_ith _ _);
          destruct (bvec_incarry _ _ _); simplify_bit_ops; discriminate.
    Qed.

    Lemma bvec_ith_set_sets_ith_sum_comm {SIZE} (x y : bvec SIZE) i (hidx : i < SIZE) :
      bvec_ith x hidx = zero ->
      bvec_ith (bvec_add y x) hidx <>
        bvec_ith (bvec_add y (BitVector.bvec_set_ith x hidx)) hidx.
    Proof.
      rewrite bvec_add_commutative with (y := x).
      rewrite bvec_add_commutative with (y := (BitVector.bvec_set_ith x hidx)).
      apply bvec_ith_set_sets_ith_sum.
    Qed.

    (* If the abstract result indicates uncertainty at some bit, there
     * should be concrete sums with mismatching bits at that position.
     * Note: Either x <> m or y <> n should hold, but both need not.
     *)
    Lemma tnum_add_optimal {SIZE} P Q i (hidx : i < SIZE) :
      tnum.wellformed P -> tnum.wellformed Q ->
      tnum.ith_m (tnum_add P Q) hidx = one ->
      exists x y m n, ingamma x P /\ ingamma y Q /\
                        ingamma m P /\ ingamma n Q /\
                        bvec_ith (bvec_add x y) hidx <> bvec_ith (bvec_add m n) hidx.
    Proof.
      intros wfp wfq sum_mu.
      apply (tnum_add_mu_imp_inputs_mu P Q) in sum_mu.

      destruct sum_mu as [ pm | [ qm | chim ] ].
      - exists (tnum.v P), (tnum.v Q).
        exists (BitVector.bvec_set_ith (tnum.v P) hidx), (tnum.v Q).
        repeat split.
        + apply tnum_ingamma_set_at_mask; auto.
        + apply bvec_ith_set_sets_ith_sum. auto.

      - exists (tnum.v P), (tnum.v Q).
        exists (tnum.v P), (BitVector.bvec_set_ith (tnum.v Q) hidx).
        repeat split.
        + apply tnum_ingamma_set_at_mask; auto.
        + apply bvec_ith_set_sets_ith_sum_comm. auto.

      - unfold tnum_ith_chi in chim.
        revert chim.

        unwrap_bvec_ops.

        intro chim. apply bit_xor_one_imp in chim.
        destruct (bvec_ith (bvec_add (tnum.v P) (tnum.v Q)) hidx) eqn : hv; simplify_bit_ops;
          revert chim; simplify_bit_ops.
        + (* Pm[i] = Qm[i] = sv[i] = 0; (sv + sm)[i] = 1 *)

          rewrite tnum_add_sv_sm_as_or.

          exists (tnum.v P). (* x *)
          exists (tnum.v Q). (* y *)
          exists (bvec_or (tnum.v P) (tnum.m P)). (* m *)
          exists (bvec_or (tnum.v Q) (tnum.m Q)). (* n *)

          repeat split.
          * apply ingamma_value_bitor_mask.
          * apply ingamma_value_bitor_mask.
          * destruct chim as (h1 & h2).
            rewrite hv, h1.
            discriminate.
          * assumption.
          * assumption.
        + (* Pm[i] = Qm[i] = 0; sv[i] = 1; (sv + sm)[i] = 0 *)

          rewrite tnum_add_sv_sm_as_or.

          exists (tnum.v P). (* x *)
          exists (tnum.v Q). (* y *)
          exists (bvec_or (tnum.v P) (tnum.m P)). (* m *)
          exists (bvec_or (tnum.v Q) (tnum.m Q)). (* n *)

          repeat split.
          * apply ingamma_value_bitor_mask.
          * apply ingamma_value_bitor_mask.
          * destruct chim as (h1 & h2).
            rewrite hv, h2.
            discriminate.
          * assumption.
          * assumption.
    Qed.
  End tnum_add_optimality_me.

  Section tnum_add_optimality_hari.
    (* Finding the bits that can be uncertain (by propagation) involves taking the
     * difference of the maximum concrete sum and the minimum concrete sum of P and Q.
     * The idea comes from https://dougallj.wordpress.com/2020/01/13/bit-twiddling-addition-with-unknown-bits/
     *)

    Definition minsum {SIZE} (P : tnum.t SIZE) Q :=
      bvec_add (tnum.v P) (tnum.v Q).

    Definition maxval {SIZE} (P : tnum.t SIZE) :=
      bvec_or (tnum.v P) (tnum.m P).

    Definition maxsum {SIZE} (P : tnum.t SIZE) Q :=
      bvec_add (maxval P) (maxval Q).

    Definition sumdiff {SIZE} (P : tnum.t SIZE) Q :=
      bvec_xor (minsum P Q) (maxsum P Q).

    (* sumdiff considers minsum and maxsum only. We need to show that that's enough to find the
     * minimum uncertainty by carry.
     *)

    (* Mirrors Harishankar et al. *)
    Lemma minimum_carries {SIZE} x y P Q :
      tnum.wellformed P -> tnum.wellformed Q ->
      ingamma x P -> ingamma y Q ->
      forall [i] (hidx : i < SIZE),
        bvec_incarry (tnum.v P) (tnum.v Q) hidx = one ->
        bvec_incarry x y hidx = one.
    Proof.
      unfold tnum.wellformed. unfold ingamma.
      unfold tnum.ith_m. unfold tnum.ith_v.
      intros wfp wfq igp igq.
      induction i.
      - intro. rewrite bvec_incarry_0. easy.
      -
        intro hidx.
        rewrite bvec_incarry_Si. simpl.

        specialize (IHi (ltprv hidx)).
        specialize_wf_ig (ltprv hidx).
        rewrite bvec_incarry_Si. simpl.
        crush11.
    Qed.

    Lemma maximum_carries {SIZE} x y P Q :
      tnum.wellformed P -> tnum.wellformed Q ->
      ingamma x P -> ingamma y Q ->
      forall [i] (hidx : i < SIZE),
        bvec_incarry (maxval P) (maxval Q) hidx = zero ->
        bvec_incarry x y hidx = zero.
    Proof.
      unfold maxval. unfold tnum.wellformed. unfold ingamma.
      unfold tnum.ith_m. unfold tnum.ith_v.
      intros wfp wfq igp igq.
      induction i.
      - intro. repeat rewrite bvec_incarry_0. auto.
      -
        intro hidx.
        rewrite bvec_incarry_Si. simpl.

        specialize (IHi (ltprv hidx)).
        specialize_wf_ig (ltprv hidx).
        unwrap_bvec_ops.
        rewrite bvec_incarry_Si.
        crush11.
    Qed.

    (* This lemma essentially shows the optimization of chi is correct.
     * chi is meant to be the minimum mask via carry, which is the xor of minsum and maxsum.
     * The fact that minsum and maxsum are enough to find the uncertainty propagated by carry
     * is established by the lemmas minimum_carries and maximum_carries.
     *)
    Lemma tnum_add_optimal_hari {SIZE} P Q :
      tnum.wellformed P -> tnum.wellformed Q ->
      forall [i] (hidx : i < SIZE),
        tnum_ith_chi P Q hidx = bvec_ith (sumdiff P Q) hidx.
    Proof.
      unfold tnum.wellformed.
      intros wfp wfq i hidx.
      unfold tnum_ith_chi. unfold sumdiff. unfold maxsum. unfold maxval. unfold minsum.
      induction i.
      - specialize_wf_ig hidx.
        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        repeat rewrite bvec_incarry_0.
        unwrap_bvec_ops.
        crush11.
      -
        assert (wfpi := wfp _ hidx).
        assert (wfqi := wfq _ hidx).
        assert (wfpp := wfp _ (ltprv hidx)).
        assert (wfqp := wfq _ (ltprv hidx)).
        specialize (IHi (ltprv hidx)).

        assert (h66 := hlp_tnum_add_incarry_exmv P Q wfp wfq (ltprv hidx)).
        assert (h63 := helper63 P Q wfp wfq (ltprv hidx)).
        revert h66. revert h63. unfold_tnum_goodies.
        specialize_wf_ig (ltprv hidx).

        revert IHi.
        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        repeat rewrite bvec_incarry_Si. unwrap_bvec_ops. repeat simplify_bit_ops.
        repeat rewrite bvec_fulladd_result.

        (* TODO FIXME crush11 to replace this whole part is painfully slow *)
        repeat destruct (bvec_incarry _ _ (ltprv hidx));
          simplify_bit_ops; crush11.
    Qed.
  End tnum_add_optimality_hari.
End linux_tnum_addition.
