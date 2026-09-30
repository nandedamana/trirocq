From Stdlib Require Import
  Lia
  Program (* For ProofIrrelevance *)
  ZArith.

From trirocq.Z Require Import
  Bit
  BitVector
  Tnum.

(** printing < %\texttt{<}% *)

Ltac specialize_wf_ig j :=
  match goal with
  | [ H : forall _, _ < _ -> bvec_ith _ _ = _ -> bvec_ith _ _ = _ |- _ ] =>
     specialize (H j); try specialize_wf_ig j
  | [ H1 : ?p < ?q, H2 : ?p < ?q -> bvec_ith _ _ = _ -> bvec_ith _ _ = _ |- _ ] =>
     specialize (H2 H1); try specialize_wf_ig j
  | [ H : forall i, i < _ -> bvec_incarry _ _ i = _ -> bvec_incarry _ _ _ = _ |- _ ] =>
      specialize (H j); try specialize_wf_ig j
  (* TODO
  | [ H : forall i, bvec_inborrow _ _ i = _ -> bvec_inborrow _ _ _ = _ |- _ ] =>
     specialize (H j); try specialize_wf_ig j
   *)
  end.

(* TODO dedup with TnumUnion.v *)
Ltac bool_imp_easy :=
  match goal with
  | [ H : true = true -> true = false |- _ ] => specialize (H eq_refl); discriminate H
  | [ H : true = true -> false = true |- _ ] => specialize (H eq_refl); discriminate H
  | [ H : false = false -> true = false |- _ ] => specialize (H eq_refl); discriminate H
  | [ H : false = false -> false = true |- _ ] => specialize (H eq_refl); discriminate H
  end.

Ltac dismiss_absurd :=
  try match goal with
    | [ H : ?x = ?x -> zero = one |- _ ] =>
        discriminate H; auto
    | [ H : ?x = ?x -> one = zero |- _ ] =>
        discriminate H; auto
    | [ H : ?h |- (?h -> true = false) -> _ ] => (* TODO rem if unused *)
        let h' := fresh "h'" in
        intro h'; specialize (h' H); easy
    | [ |- _ ] => try bool_imp_easy
    end.

Ltac crush_bvec_add :=
  match goal with
    [ |- _ ] =>
      repeat (destruct (bvec_ith _ _); dismiss_absurd;
              cbn; try easy);
      repeat (destruct (bvec_incarry _ _ _); dismiss_absurd;
              cbn; try easy);
      (* TODO
      repeat (destruct (bvec_inborrow _ _ _); dismiss_absurd;
              cbn; try easy);
       *)
      intuition
  end.

Section linux_tnum_addition.
  (* Mirrors the Linux kernel definition *)

  Definition tnum_ith_chi {SIZE} (P Q : tnum.t SIZE) i :=
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    bvec_ith chi i.

  Definition tnum_add {SIZE} P Q :=
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    let eta := bvec_or (bvec_or chi (tnum.m P)) (tnum.m Q) in
    tnum.cons SIZE (bvec_and sv (bvec_neg eta)) eta.

  Definition value_sum {SIZE} (P Q : tnum.t SIZE) :=
    bvec_add (tnum.v P) (tnum.v Q).

  Definition mask_sum {SIZE} (P Q : tnum.t SIZE) :=
    bvec_add (tnum.m P) (tnum.m Q).

  Definition ith_mask_incarry {SIZE} (P Q : tnum.t SIZE) i :=
    bvec_incarry (tnum.m P) (tnum.m Q) i.

  Definition ith_value_incarry {SIZE} (P Q : tnum.t SIZE) i :=
    bvec_incarry (tnum.v P) (tnum.v Q) i.

  Definition ith_value_mask_incarry {SIZE} (P Q : tnum.t SIZE) i :=
    bvec_incarry (value_sum P Q) (mask_sum P Q) i.

  Ltac unfold_tnum_goodies :=
    unfold tnum.wellformed; unfold ingamma;
    unfold tnum_ith_chi;
    unfold tnum.ith_v; unfold tnum.ith_m;
    unfold ith_value_mask_incarry;
    unfold ith_mask_incarry; unfold ith_value_incarry;
    unfold value_sum; unfold mask_sum.

  Ltac bvec_incarry_Si_iify :=
    match goal with
      [ |- context[bvec_incarry _ _ (S ?i)] ] =>
        rewrite !bvec_incarry_Si with (i := S i);
        replace (S i - 1) with i by lia
    end.

  Ltac simplify_tnum_add_context i :=
    repeat match goal with
      | [ H : context[zero] |- _ ] => unfold zero in H
      | [ H : context[one] |- _ ] => unfold one in H
      | [ _ : S ?i < ?SIZE |- _ ] =>
          match goal with
            | [ _ : i < ?SIZE |- _ ] => idtac
            | _ => assert (i < SIZE) by lia
            end
      end; try specialize_wf_ig i.

  (* Is chi is the mask bit of the incoming carry? No; it considers v bits
   * as well. chi[i] in fact `tnum.ith_m (tnum_add P Q) hidx` excluding
   * P.m[i] | Q.m[i]
   *)
  Lemma hlp_tnum_add_no_mask_imp_known_inputs {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall i, i < SIZE ->
      tnum.ith_m (tnum_add P Q) i = zero ->
      tnum.ith_m P i = zero /\ tnum.ith_m Q i = zero /\
        tnum_ith_chi P Q i = zero.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq i hi.

    destruct i;
      match goal with
      | [ _ : 0 < SIZE |- _ ] =>
            simplify_tnum_add_context 0
      | _ => simplify_tnum_add_context i
      end;
      unfold tnum_add;
      rewrite tnum.ith_m_simplify2;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fulladd_result;
      unfold bvec_incarry;
      repeat destruct (bvec_ith (tnum.m _) _);
      repeat simplify_bit_ops; try easy.
  Qed.

  Lemma hlp_tnum_add_incarry_exmv1 {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall (i : POS), i < SIZE ->
      bit_and (ith_mask_incarry P Q i) (ith_value_incarry P Q i) = zero.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq.
    induction i.
    - repeat rewrite bvec_incarry_0. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      simplify_tnum_add_context i.
      specialize (IHi H).
      crush_bvec_add.
  Qed.

  (* Interesting: proving only one side would seem easier, but it is actually
   * difficult, if not impossible. I suppose it is because that way the
   * induction hypothesis becomes weaker.
   *)
  Lemma hlp_tnum_add_incarry_exmv2 {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall (i : POS), i < SIZE ->
      let vm_incarry := ith_value_mask_incarry P Q i in
      bit_and (ith_mask_incarry P Q i) vm_incarry = zero /\
        bit_and (ith_value_incarry P Q i) vm_incarry = zero.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq i hi.
    induction i.
    - repeat rewrite bvec_incarry_0. auto.
    -
      repeat rewrite bvec_incarry_Si.
      repeat rewrite bvec_fulladd_result.
      assert (h66 := hlp_tnum_add_incarry_exmv1 _ _ wfp wfq i).
      simplify_tnum_add_context i.

      specialize (h66 H).
      revert h66. unfold_tnum_goodies.
      specialize (IHi H).
      revert IHi.

      repeat destruct (bvec_incarry _ _ _);
        repeat destruct (bvec_ith _ _);
        simplify_bit_ops;
        try dismiss_absurd; try easy.

      lia. lia.
  Qed.

  Lemma specialize_wf_ig {SIZE} {x y} {P Q : tnum.t SIZE} :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall i, i < SIZE ->
      (bvec_ith (tnum.m P) i = one -> bvec_ith (tnum.v P) i = zero) /\
        (bvec_ith (tnum.m Q) i = one -> bvec_ith (tnum.v Q) i = zero) /\
        (bvec_ith (tnum.m P) i = zero -> bvec_ith x i = bvec_ith (tnum.v P) i) /\
        (bvec_ith (tnum.m Q) i = zero -> bvec_ith y i = bvec_ith (tnum.v Q) i).
  Proof.
    auto.
  Qed.

  Lemma hlp_xy_incarry_eq_minsum_incarry_internal {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    forall i, i < SIZE ->
      ith_mask_incarry P Q i = zero ->
      ith_value_mask_incarry P Q i = zero ->
      bvec_incarry x y i = ith_value_incarry P Q i.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq igp igq i hi.

    induction i.
    - simplify_tnum_add_context 0.
      rewrite !bvec_incarry_0. auto.
    -
      assert (hi' : i < SIZE) by lia.

      rewrite bvec_incarry_Si.
      rewrite bvec_incarry_Si with (x := x).
      rewrite !bvec_incarry_Si with (i := i).
      rewrite !bvec_fulladd_result by assumption.

      specialize (IHi hi').

      pose (H := specialize_wf_ig wfp wfq igp igq i hi').
      destruct H as (wfps & wfqs & igps & igqs).

      assert (h66 := hlp_tnum_add_incarry_exmv1 P Q wfp wfq i).
      assert (h64 := hlp_tnum_add_incarry_exmv2 P Q wfp wfq i).
      revert h66. revert h64. unfold_tnum_goodies.

      crush_bvec_add.
  Qed.

  Lemma bit_xor_and_and_imp [x] [y] :
    bit_xor x y = zero -> bit_and y x = zero -> x = zero /\ y = zero.
  Proof.
    unfold bit_xor. unfold bit_and. destruct x; destruct y; auto.
  Qed.

  (* TODO dedup with hlp_xy_incarry_eq_minsum_incarry if possible *)
  Lemma hlp_xy_incarry_eq_minsum_incarry {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall i, i < SIZE ->
      tnum.ith_m (tnum_add P Q) i = zero ->
      bvec_incarry x y i = ith_value_incarry P Q i.
  Proof.
    unfold_tnum_goodies.
    intros wfp wfq igP igQ i hi.
    destruct i.
    - intro. unfold ith_value_incarry. repeat rewrite bvec_incarry_0.
      auto.
    -
      cbn [tnum_add tnum.m].
      unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.

      intro H.
      assert (hmp : bvec_ith (tnum.m P) (S i) = zero). revert H.
      destruct (bvec_ith (tnum.m P) (S i));
        repeat simplify_bit_ops; try easy.

      assert (hmq : bvec_ith (tnum.m Q) (S i) = zero). revert H.
      destruct (bvec_ith (tnum.m Q) (S i));
        repeat simplify_bit_ops; try easy.

      apply bit_or_zero_zero in H as (H1 & H2).
      apply bit_or_zero_zero in H1 as (H11 & H12).
      apply bit_xor_x_y_zero in H11.
      apply bit_xor_x_y_z_eq_y in H11.

      revert H11. rewrite hmp. rewrite hmq. repeat simplify_bit_ops.

      pose (h63 := hlp_tnum_add_incarry_exmv2 P Q wfp wfq _ hi).
      destruct h63 as (h1 & h2). intro h3.

      pose (h82 := bit_xor_and_and_imp h3 h1). destruct h82.
      apply hlp_xy_incarry_eq_minsum_incarry_internal; auto.

      lia. lia. lia.
  Qed.

  Lemma wellformed_general {SIZE} (inval : bvec SIZE) mu :
    forall i, i < SIZE ->
      bvec_ith mu i = one -> bvec_ith (bvec_and inval (bvec_neg mu)) i = zero.
  Proof.
    intros i hi H.
    unwrap_bvec_ops. rewrite H. simpl.
    destruct (bvec_ith inval i); auto.
    assumption.
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
  Lemma tnum_add_sound {SIZE} : sound2 SIZE bvec_add tnum_add.
    unfold sound2.
    unfold_tnum_goodies.
    intros p q P Q wfp wfq igP igQ.

    split. apply tnum_add_wellformed; auto.

    intros i hi rmskz.

    assert (knownip := hlp_tnum_add_no_mask_imp_known_inputs P Q wfp wfq i hi rmskz).
    unfold tnum.ith_m, tnum.ith_v, tnum_ith_chi in knownip.
    destruct knownip as (hpmi & hqmi & hchimi).

    assert (hxycarry := hlp_xy_incarry_eq_minsum_incarry p q P Q wfp wfq igP igQ i hi rmskz).
    revert hxycarry. unfold_tnum_goodies. intro hxycarry.

    unfold tnum_add. simpl.

    rewrite bvec_and_rel. rewrite bvec_neg_rel by assumption. rewrite !bvec_or_rel.
    rewrite hchimi.

    rewrite hpmi, hqmi.
    simplify_bit_ops.

    (* Goal at this point:
     * bvec_ith (bvec_add p q) i = bvec_ith (bvec_add (tnum.v P) (tnum.v Q)) i
     *)
    repeat rewrite bvec_fulladd_result by assumption.
    rewrite hxycarry.

    rewrite (igP i hi hpmi).
    rewrite (igQ i hi hqmi). auto.
  Qed.

  Section tnum_add_optimality_me.

    (* - Recall: chi is `tnum.ith_m (tnum_add P Q) hidx` excluding P.m[i] | Q.m[i]
     * - Comparable to hlp_tnum_add_no_mask_imp_known_inputs.
     *)
    Lemma tnum_add_mu_imp_inputs_mu {SIZE} (P Q : tnum.t SIZE) :
      forall (i : POS), i < SIZE ->
        tnum.ith_m (tnum_add P Q) i = one ->
        tnum.ith_m P i = one \/ tnum.ith_m Q i = one \/
          tnum_ith_chi P Q i = one.
    Proof.
      unfold_tnum_goodies.
      intros i hi.

      destruct i;
        cbn [tnum_add tnum.m];
        unwrap_bvec_ops; unfold tnum.ith_m;
        rewrite bvec_fulladd_result;
        unfold bvec_incarry;
        repeat destruct (bvec_ith (tnum.m _) 0);
        repeat destruct (bvec_ith (tnum.m _) (S _));
        try auto;
        repeat simplify_bit_ops; try auto.
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
    Lemma tnum_incarry_v_m_0 {SIZE} (P : tnum.t SIZE) (i : POS) (hi : i < SIZE) :
      tnum.wellformed P ->
      bvec_incarry (tnum.v P) (tnum.m P) i = zero.
    Proof.
      induction i.
      - rewrite bvec_incarry_0. reflexivity.
      - unfold_tnum_goodies.
        intro wfp.
        rewrite bvec_incarry_Si.
        replace (S i - 1) with i by lia.
        rewrite IHi; auto.
        simplify_tnum_add_context i.
        repeat destruct (bvec_ith _ _);
          dismiss_absurd; auto.
        lia.
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
      intros i hi.
      rewrite bvec_fulladd_result by assumption.
      rewrite tnum_incarry_v_m_0; auto.
      simplify_bit_ops.
      rewrite bvec_or_rel.
      unfold tnum.wellformed in wfp.
      specialize (wfp i).
      destruct (bvec_ith (tnum.m P) _).
      - destruct (bvec_ith (tnum.v P) _); auto.
      - simplify_bit_ops. reflexivity.
    Qed.

    Lemma bvec_add_regroup : forall {SIZE} (a b c d : bvec SIZE),
        bvec_add (bvec_add a b) (bvec_add c d) =
          bvec_add (bvec_add a c) (bvec_add b d).
    Proof.
      intros.
      destruct a as [a ah], b as [b bh], c as [c ch], d as [d dh].
      unfold bvec_add at 1.
      apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
      rewrite <- !Z.add_mod by lia.
      replace (a + b + (c + d))%Z with (a + c + (b + d))%Z. reflexivity.

      lia.
    Qed.

    Lemma tnum_add_sv_sm_as_or {SIZE} (P Q : tnum.t SIZE) i :
      tnum.wellformed P -> tnum.wellformed Q ->
      bvec_ith
        (bvec_add (bvec_add (tnum.v P) (tnum.v Q))
           (bvec_add (tnum.m P) (tnum.m Q)))
        i =
        bvec_ith (bvec_add (bvec_or (tnum.v P) (tnum.m P))
                    (bvec_or (tnum.v Q) (tnum.m Q)))
          i.
    Proof.
      rewrite bvec_add_regroup.
      intros.
      repeat rewrite tnum_add_v_m_is_or; auto.
    Qed.

    Lemma tnum_ingamma_set_at_mask {SIZE} (P : tnum.t SIZE) i (hi : i < SIZE) :
      tnum.wellformed P ->
      tnum.ith_m P i = one ->
      ingamma (bvec_set_ith (tnum.v P) i) P.
    Proof.
      unfold_tnum_goodies.
      intros wfp msk1.
      intros i' hi'.
      assert (hiex : i' = i \/ i' <> i). lia.
      destruct hiex as [hieq | hine].
      - replace (bvec_ith (tnum.m P) i') with (bvec_ith (tnum.m P) i).
        rewrite msk1. easy.
        unfold bvec_ith. subst. reflexivity.
      - enough (igv : ingamma (tnum.v P) P).
        revert igv. unfold_tnum_goodies.
        pose (H := bvec_ith_unset_is_id (tnum.v P) _ hi _ hi').
        intros; auto.
        split.
    Qed.

    Lemma bvec_ith_set_prv_carry_intact {SIZE} (x y : bvec SIZE) i (hi : i < SIZE) j (hj : j < SIZE) :
      j < i ->
      bvec_incarry x y j = bvec_incarry (bvec_set_ith x i) y j.
    Proof.
      induction j.
      - repeat rewrite bvec_incarry_0. auto.
      - repeat rewrite bvec_incarry_Si.

        intro sjlti. assert (j < i). lia.

        rewrite bvec_ith_unset_is_id by lia.
        rewrite IHj by lia.
        reflexivity.
    Qed.

    Lemma bvec_ith_set_sets_ith_sum {SIZE} (x y : bvec SIZE) i (hidx : i < SIZE) :
      bvec_ith x i = zero ->
      bvec_ith (bvec_add x y) i <>
        bvec_ith (bvec_add (BitVector.bvec_set_ith x i) y) i.
    Proof.
      repeat rewrite bvec_fulladd_result by lia.
      destruct i.
      - repeat rewrite bvec_incarry_0.
        rewrite bvec_ith_set_is_one.
        simplify_bit_ops.
        repeat destruct (bvec_ith _ _); easy. lia.
      - repeat rewrite bvec_incarry_Si. simpl.
        rewrite bvec_ith_unset_is_id; auto.
        repeat rewrite bvec_ith_set_is_one.
        rewrite bvec_ith_set_prv_carry_intact with (i := S i); auto.

        repeat destruct (bvec_ith _ _);
          destruct (bvec_incarry _ _ _); simplify_bit_ops; try easy.

        lia. lia. lia.
    Qed.

    Lemma bvec_ith_set_sets_ith_sum_comm {SIZE} (x y : bvec SIZE) i  (hidx : i < SIZE) :
      bvec_ith x i = zero ->
      bvec_ith (bvec_add y x) i <>
        bvec_ith (bvec_add y (bvec_set_ith x i)) i.
    Proof.
      rewrite bvec_add_commutative with (y := x).
      rewrite bvec_add_commutative with (y := (bvec_set_ith x i)).
      apply bvec_ith_set_sets_ith_sum. lia.
    Qed.

    (* If the abstract result indicates uncertainty at some bit, there
     * should be concrete sums with mismatching bits at that position.
     * Note: Either p <> p' or q <> q' should hold, but both need not.
     *)
    Lemma tnum_add_optimal : forall [SIZE] (P Q : tnum.t SIZE) i (hidx : i < SIZE),
      tnum.wellformed P -> tnum.wellformed Q ->
      tnum.ith_m (tnum_add P Q) i = one ->
      exists p q p' q',
        ingamma p P /\ ingamma q Q /\
          ingamma p' P /\ ingamma q' Q /\
          bvec_ith (bvec_add p q) i <> bvec_ith (bvec_add p' q') i.
    Proof.
      unfold_tnum_goodies.
      intros SIZE P Q i hidx wfp wfq sum_mu.
      apply (tnum_add_mu_imp_inputs_mu P Q) in sum_mu.

      destruct sum_mu as [ pm | [ qm | chim ] ].
      - exists (tnum.v P), (tnum.v Q).
        exists (bvec_set_ith (tnum.v P) i), (tnum.v Q).
        repeat split.
        + apply tnum_ingamma_set_at_mask; auto.
        + apply bvec_ith_set_sets_ith_sum.
          simplify_tnum_add_context i; auto. auto.

      - exists (tnum.v P), (tnum.v Q).
        exists (tnum.v P), (BitVector.bvec_set_ith (tnum.v Q) i).
        repeat split.
        + apply tnum_ingamma_set_at_mask; auto.
        + apply bvec_ith_set_sets_ith_sum_comm. auto.
          simplify_tnum_add_context i; auto.

      - unfold tnum_ith_chi in chim.
        revert chim.

        unwrap_bvec_ops.

        intro chim. apply bit_xor_one_imp in chim.
        destruct (bvec_ith (bvec_add (tnum.v P) (tnum.v Q)) i) eqn : hv; simplify_bit_ops;
          revert chim; simplify_bit_ops.
        + (* Pm[i] = Qm[i] = 0; sv[i] = 1; (sv + sm)[i] = 0 *)

          rewrite tnum_add_sv_sm_as_or.

          exists (tnum.v P). (* p *)
          exists (tnum.v Q). (* q *)
          exists (bvec_or (tnum.v P) (tnum.m P)). (* p' *)
          exists (bvec_or (tnum.v Q) (tnum.m Q)). (* q' *)

          repeat split.
          * apply ingamma_value_bitor_mask.
          * apply ingamma_value_bitor_mask.
          * destruct chim as (h1 & h2).
            rewrite hv, h2.
            discriminate.
          * assumption.
          * assumption.
        + (* Pm[i] = Qm[i] = sv[i] = 0; (sv + sm)[i] = 1 *)

          rewrite tnum_add_sv_sm_as_or.

          exists (tnum.v P). (* p *)
          exists (tnum.v Q). (* q *)
          exists (bvec_or (tnum.v P) (tnum.m P)). (* p' *)
          exists (bvec_or (tnum.v Q) (tnum.m Q)). (* q' *)

          repeat split.
          * apply ingamma_value_bitor_mask.
          * apply ingamma_value_bitor_mask.
          * destruct chim as (h1 & h2).
            rewrite hv, h1.
            discriminate.
          * assumption.
          * assumption.
      - assumption.
    Qed.

    Lemma tnum_add_optimal_by_subset [SIZE] : optimal2 SIZE bvec_add tnum_add.
      unfold optimal2. unfold sound2.
      intros soundF F' soundF' P Q wfp wfq.
      pose (hopt := tnum_add_optimal P Q).
      unfold subset. unfold ingamma.
      intros x' igxF i hidx.
      specialize (hopt i hidx wfp wfq).
      specialize (igxF i hidx).

      (* Goal: tnum.ith_m (F' P Q) hidx = zero -> bvec_ith x hidx = tnum.ith_v (F' P Q) hidx *)

      destruct (tnum.ith_m (tnum_add P Q) i) eqn : Fim.
      -
        destruct (tnum.ith_m (F' P Q) i) eqn : F'im.
        + (* F(P, Q).m[i] = 1; F'(P, Q).m[i] = 1 *)
          easy. (* Uncertainty includes uncertainty. *)

        + (* F(P, Q).m[i] = 1; F'(P, Q).m[i] = 0 *)
          (* If F is optimal, F is uncertain at i and F' is certain at i
           * cannot happen. We need to show that it is the case.
           *)
          destruct hopt as [p [q [p' [q' [igp [igq [igp' [igq' hopt]]]]]]]]; auto.

          (* Now hopt says bvec_ith (bvec_add x y) hidx <> bvec_ith (bvec_add m n) hidx.
           * But this contradicts the precondition that F'(P, Q).m[i] = 0
           * (given F' is also a sound abstraction of bvec_add).
           *)

          assert (hF'pq := soundF' p q P Q wfp wfq igp igq).
          assert (hF'p'q' := soundF' p' q' P Q wfp wfq igp' igq').
          destruct hF'pq as [wfF'pq hF'pq].
          destruct hF'p'q' as [wfF'p'q' hF'p'q'].
          unfold ingamma in hF'pq, hF'p'q'.

          specialize (hF'pq i hidx F'im).
          specialize (hF'p'q' i hidx F'im).
          rewrite <- hF'p'q' in hF'pq.
          easy.
      - rewrite igxF; auto.
        destruct (tnum.ith_m (F' P Q) i) eqn : F'im.
        + (* F(P, Q).m[i] = 0; F'(P, Q).m[i] = 1 *)
          easy. (* F'(P, Q) is uncertain; F(P, Q)[i] is auto-included. *)

        + (* F(P, Q).m[i] = F'(P, Q).m[i] = 0 *)

          (* In this case, P.m[i] = Q.m[i] = 0.
           * I can specialize soundF and soundF' with
           * p = (tnum.v P) and q = (tnum.v Q) to obtain
           * preconditions that will help me rewrite and discharge the goal.
           *)

          assert (igvp : ingamma (tnum.v P) P). unfold ingamma. auto.
          assert (igvq : ingamma (tnum.v Q) Q). unfold ingamma. auto.

          specialize (soundF (tnum.v P) (tnum.v Q) P Q wfp wfq igvp igvq).
          destruct soundF as (wfF & igF).
          unfold ingamma in igF.
          rewrite <- igF; auto.

          specialize (soundF' (tnum.v P) (tnum.v Q) P Q wfp wfq igvp igvq).
          destruct soundF' as (wfF' & igF').
          unfold ingamma in igF.
          rewrite <- igF'; auto.
    Qed.
  End tnum_add_optimality_me.
End linux_tnum_addition.
