Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.Tnum.

(* TODO rename *)
Ltac crush10 := match goal with
                | [ H : ?x = ?x -> zero = one |- _ ] => specialize (H eq_refl); easy
                | [ H : ?x = ?x -> one = zero |- _ ] => specialize (H eq_refl); easy
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

  (* TODO rename *)
  (* Unused, but still an interesting observation. *)
  Lemma helper14 {SIZE} v1 v2 {i} (hidx : i < SIZE) :
    bvec_ith (bvec_xor (bvec_add v1 v2) v1) hidx = bit_xor (bvec_ith v2 hidx) (bvec_incarry v1 v2 hidx).
  Proof.
    unwrap_bvec_ops.
    rewrite bvec_fulladd_result with (x := v1) (y := v2).
    destruct (bvec_ith v1 hidx); destruct (bvec_ith v2 hidx); destruct (bvec_incarry v1 v2 hidx); auto.
  Qed.

  (* Is chi is the mask bit of the incoming carry? No; it considers v bits as well. chi[i] in fact `tnum.ith_m (tnum_add P Q) hidx` excluding P.m[i] | Q.m[i] *)
  Lemma helper32 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      tnum.ith_m P hidx = zero /\ tnum.ith_m Q hidx = zero /\
        tnum_ith_chi P Q hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold tnum_ith_chi.
    intros wf1 wf2 i hidx.
    specialize (wf1 i hidx).
    specialize (wf2 i hidx).

    destruct i;
      unfold tnum_add;
      rewrite tnum.ith_m_simplify;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fulladd_result;
      unfold bvec_incarry;
      destruct (bvec_ith (tnum.m P) hidx);
      destruct (bvec_ith (tnum.m Q) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  Lemma helper66 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_incarry (tnum.m P) (tnum.m Q) hidx)
        (bvec_incarry (tnum.v P) (tnum.v Q) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
      destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  (* Interesting: proving only one side would seem easier, but it is actually
   * difficult, if not impossible. I suppose it is because that way the
   * induction hypothesis becomes weaker.
   *)
  Lemma helper63 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_incarry (tnum.m P) (tnum.m Q) hidx)
        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
           (bvec_add (tnum.m P) (tnum.m Q)) hidx) = zero /\
        bit_and (bvec_incarry (tnum.v P) (tnum.v Q) hidx)
          (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
             (bvec_add (tnum.m P) (tnum.m Q)) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                    (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  Lemma helper45 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : S i < SIZE),
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero ->
      let sv := bvec_add (tnum.v P) (tnum.v Q) in
      let sm := bvec_add (tnum.m P) (tnum.m Q) in
      bvec_incarry sv sm hidx = zero ->
      bvec_incarry x y hidx = bvec_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed.
    unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq igp igq.

    induction i.
    - intro hidx.
      rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.
      unfold bvec_incarry.
      repeat simplify_bit_ops.

      specialize (wfp 0 (ltprv hidx)).
      specialize (wfq 0 (ltprv hidx)).
      specialize (igp 0 (ltprv hidx)).
      specialize (igq 0 (ltprv hidx)).

      destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
    - intro hidx.
      rewrite bvec_incarry_Si.
      rewrite bvec_incarry_Si with (x := x).
      repeat rewrite bvec_incarry_Si with (hidx := hidx).
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      assert (h64 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                         (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero /\
                      bit_and (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx))
                        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                           (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero).
      apply helper63; auto.


      specialize (wfp (S i) (ltprv hidx)).
      specialize (wfq (S i) (ltprv hidx)).
      specialize (igp (S i) (ltprv hidx)).
      specialize (igq (S i) (ltprv hidx)).

      destruct(bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                    (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
        destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));

        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;

        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;

        destruct (bvec_ith x (ltprv hidx));
        destruct (bvec_ith y (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try crush10.
  Qed.

  Lemma helper82 [x] [y] : bit_xor x y = zero -> bit_and y x = zero -> x = zero /\ y = zero.
    unfold bit_xor. unfold bit_and. destruct x; destruct y; auto.
  Qed.

  Lemma helper33 {SIZE} x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      bvec_incarry x y hidx = bvec_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.
    destruct H as (wfp & wfq & igP & igQ).
    destruct i.
    - unfold bvec_incarry. auto.
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
    tnum.wellformed P /\ tnum.wellformed Q -> tnum.wellformed (tnum_add P Q).
  Proof.
    unfold tnum.wellformed.
    intro H.
    unfold tnum_add.
    apply wellformed_general.
  Qed.

  (* Soundness: the result of adding abstract numbers P and Q include the results
   * of adding any concrete p and q (written less formally for simplicity).
   *)
  Lemma tnum_add_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_add P Q) /\
      ingamma (bvec_add x y) (tnum_add P Q).
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.

    pose (H'1 := helper33 x y P Q H).

    unfold tnum.ith_m in H.
    destruct H as (wf1 & wf2 & igP & igQ).

    split. apply tnum_add_wellformed; auto.

    pose (H'2 := helper32 P Q wf1 wf2). unfold tnum.ith_m in H'2. (* TODO rename *)
    unfold ingamma.

    intros i hidx rmskz.

    specialize (H'2 i hidx rmskz) as (xmskz & ymskz & cinmskz).
    specialize (H'1 i hidx rmskz).
    revert rmskz.

    revert cinmskz.

    unfold tnum_add.
    rewrite tnum.ith_m_simplify.
    rewrite tnum.ith_v_simplify.

    unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
    rewrite xmskz. rewrite ymskz. rewrite igP; auto. rewrite igQ; auto. simpl.

    unfold tnum.ith_v.

    intros H1 H2.

    (* Replaces the subexpression H2 from the goal with zero because it is
     * the ith bit of `mu` (the `mu` from `sv & ~mu`), which is zero as per
     * the assumption.
     *)
    rewrite H2. simpl.
    rewrite H'1.
    rewrite bit_and_right_one.
    auto.
  Qed.

  Section tnum_add_optimality.
    (* Finding the bits that can be uncertain (by propagation) involves taking the
     * difference of the maximum concrete sum and the minimum concrete sum of P and Q.
     * The idea comes from https://dougallj.wordpress.com/2020/01/13/bit-twiddling-addition-with-unknown-bits/
     *)
    Definition minsum {SIZE} (P : tnum.t SIZE) Q := bvec_add (tnum.v P) (tnum.v Q).
    Definition maxsum {SIZE} (P : tnum.t SIZE) Q :=
      bvec_add (bvec_or (tnum.v P) (tnum.m P)) (bvec_or (tnum.v Q) (tnum.m Q)).
    Definition minmask {SIZE} (P : tnum.t SIZE) Q := bvec_xor (minsum P Q) (maxsum P Q).

    (* TODO better, directly work on the result of tnum_add(). *)
    (* TODO FIXME wait, why just chi? ith `mu = chi | a.mask | b.mask`, right?
     * does this mean `a.mask | b.mask` is irrelevant? Not according to my brute-force experi.
     * Also, this looks unprovable:
     * bit_or (tnum_ith_chi P Q hidx) (bit_or (bvec_ith (tnum.m P) hidx) (bvec_ith (tnum.m Q) hidx)) = bvec_ith (minmask P Q) hidx.
     *)
    Lemma tnum_add_optimal {SIZE} P Q :
      tnum.wellformed P -> tnum.wellformed Q ->
      forall [i] (hidx : i < SIZE),
        tnum_ith_chi P Q hidx = bvec_ith (minmask P Q) hidx.
    Proof.
      unfold tnum.wellformed.
      intros wfp wfq i hidx.
      unfold tnum_ith_chi. unfold minmask. unfold maxsum. unfold minsum.
      induction i.
      -
        specialize (wfp 0 hidx).
        specialize (wfq 0 hidx).

        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        unfold bvec_incarry. unwrap_bvec_ops. repeat simplify_bit_ops.

        destruct (bvec_ith (tnum.m P) hidx);
        destruct (bvec_ith (tnum.m Q) hidx);
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) hidx);
        destruct (bvec_ith (tnum.v Q) hidx);
        repeat simplify_bit_ops; try easy.
      -
        assert (wfpi : bvec_ith (tnum.m P) hidx = one -> bvec_ith (tnum.v P) hidx = zero). apply wfp.
        assert (wfqi : bvec_ith (tnum.m Q) hidx = one -> bvec_ith (tnum.v Q) hidx = zero). apply wfq.
        assert (wfpp : bvec_ith (tnum.m P) (ltprv hidx) = one -> bvec_ith (tnum.v P) (ltprv hidx) = zero). apply wfp.
        assert (wfqp : bvec_ith (tnum.m Q) (ltprv hidx) = one -> bvec_ith (tnum.v Q) (ltprv hidx) = zero). apply wfq.
        specialize (IHi (ltprv hidx)).

        assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                        (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
        apply helper66; auto.

        assert (h64 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                           (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero /\
                        bit_and (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx))
                          (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                             (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero).
        apply helper63; auto.

        revert IHi.
        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        repeat rewrite bvec_incarry_Si. unwrap_bvec_ops. repeat simplify_bit_ops.
        repeat rewrite bvec_fulladd_result.

        destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
          destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
          destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q)) (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
          destruct (bvec_incarry (bvec_or (tnum.v P) (tnum.m P)) (bvec_or (tnum.v Q) (tnum.m Q)) (ltprv hidx)); try easy;
          destruct (bvec_ith (tnum.m P) (ltprv hidx));
          destruct (bvec_ith (tnum.m Q) (ltprv hidx));
          try rewrite_if_holds wfpp;
          try rewrite_if_holds wfqp;
          destruct (bvec_ith (tnum.v P) (ltprv hidx));
          destruct (bvec_ith (tnum.v Q) (ltprv hidx)); try easy;
          destruct (bvec_ith (tnum.m P) hidx);
          destruct (bvec_ith (tnum.m Q) hidx);
          try rewrite_if_holds wfpi;
          try rewrite_if_holds wfqi;
          destruct (bvec_ith (tnum.v P) hidx);
          destruct (bvec_ith (tnum.v Q) hidx); try easy.
    Qed.
  End tnum_add_optimality.
End linux_tnum_addition.

Section linux_tnum_subtraction.
  (* Mirrors the Linux kernel definition *)

  Definition tnum_sub_ith_chi {SIZE} P Q [i] (hidx : i < SIZE) :=
    let dv := bvec_sub (tnum.v P) (tnum.v Q) in
    let alpha := bvec_add dv (tnum.m P) in
    let beta := bvec_sub dv (tnum.m Q) in
    let chi := bvec_xor alpha beta in
    bvec_ith chi hidx.

  Definition tnum_sub {SIZE} P Q :=
    let dv := bvec_sub (tnum.v P) (tnum.v Q) in
    let alpha := bvec_add dv (tnum.m P) in
    let beta := bvec_sub dv (tnum.m Q) in
    let chi := bvec_xor alpha beta in
    let mu := bvec_or chi (bvec_or (tnum.m P) (tnum.m Q)) in
    tnum.cons SIZE (bvec_and dv (bvec_neg mu)) mu.

  Lemma sublemma32 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_sub P Q) hidx = zero ->
      tnum.ith_m P hidx = zero /\ tnum.ith_m Q hidx = zero /\
        tnum_sub_ith_chi P Q hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold tnum_sub_ith_chi.
    intros wf1 wf2 i hidx.
    specialize (wf1 i hidx).
    specialize (wf2 i hidx).

    destruct i;
      unfold tnum_sub;
      rewrite tnum.ith_m_simplify;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fullsub_result;
      unfold bvec_inborrow;
      destruct (bvec_ith (tnum.m P) hidx);
      destruct (bvec_ith (tnum.m Q) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  Lemma xor_x_y_eq_z_y x y z : bit_xor x y = bit_xor z y -> x = z.
    unfold bit_xor; destruct x; destruct y; destruct z; try easy.
  Qed.

  Ltac easy_neg :=
    let H := fresh "H" in
    match goal with
    | [ |- ?x = bit_not ?x -> _ ] => unfold bit_not; easy
    end.

  (* concerns the borrows generated by dv and beta *)
  Lemma sublemma64 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) hidx)
        (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - auto.
    -
      intros hidx.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      repeat rewrite bvec_inborrow_Si. simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  (* TODO fuse with sublemma64? *)
  (* concerns the borrow generated by dv and the carry generated by alpha *)
  Lemma sublemma67 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bvec_inborrow (tnum.v P) (tnum.v Q) hidx = zero ->
        bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - auto.
    -
      intros hidx.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      repeat rewrite bvec_incarry_Si. repeat rewrite bvec_inborrow_Si. simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  Lemma sublemma42 {SIZE} P Q :
    forall [i] (hidx : S i < SIZE),
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero ->
      bit_and (bvec_ith (tnum.m P) (ltprv hidx)) (bvec_ith (tnum.m Q) (ltprv hidx)) = zero.
  Proof.
    unfold tnum.wellformed.
    intros i hidx.
    rewrite bvec_incarry_Si.
    destruct (bvec_ith (tnum.m P) (ltprv hidx));
      destruct (bvec_ith (tnum.m Q) (ltprv hidx));
      repeat simplify_bit_ops; try easy.
  Qed.

  Lemma sublemma43 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
        bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx ->
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    -
      intro hidx.

      assert (bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx))
              (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx)) = zero).
      apply sublemma64; auto.

      assert (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx) = zero ->
              bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx) = zero).
      apply sublemma67; auto.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      rewrite bvec_incarry_Si.
      simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        try crush10; try easy.
  Qed.

  (* Turns out inborrow = incarry if the result has mask = 0. *)
  Lemma sublemma45 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
        bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx ->
      bvec_inborrow x y hidx = bvec_inborrow (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq igP igQ.
    induction i.
    - unfold bvec_inborrow. auto.
    -
      intro hidx.

      intro H.
      (* Not true for borrow. TODO note: why is this the case? Consider the case of `mu - mu`; `P.mask - Q.mask` = `1 - 1 = 0`, no borrow; but the uncertainty should actually propagate; hence carry. *)
      assert (h43 : bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero).
      apply sublemma43; auto.
      revert H. revert h43.
      intro H.

      assert (H1 : bit_and (bvec_ith (tnum.m P) (ltprv hidx)) (bvec_ith (tnum.m Q) (ltprv hidx)) = zero). apply sublemma42; auto. revert H.

      assert (bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx))
              (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx)) = zero).
      apply sublemma64; auto.

      assert (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx) = zero ->
              bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx) = zero).
      apply sublemma67; auto.

      repeat rewrite bvec_incarry_Si.
      repeat rewrite bvec_inborrow_Si.
      (* simpl. *) (* TODO see if doing this here makes some assertions unnecessary. *)
      repeat rewrite bvec_fullsub_result. simpl.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).
      specialize (igP i (ltprv hidx)).
      specialize (igQ i (ltprv hidx)).

      destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igP;
        try rewrite_if_holds igQ;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops_ex_not; try easy;
        try easy_neg;
        destruct (bvec_ith x (ltprv hidx));
        destruct (bvec_ith y (ltprv hidx));
        destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try auto; try crush10.
  Qed.

  Lemma sublemma33 {SIZE} x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_sub P Q) hidx = zero ->
      bvec_inborrow x y hidx = bvec_inborrow (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intro H.
    destruct H as (wfp & wfq & igP & igQ).
    induction i.
    - unfold bvec_inborrow. auto.
    -
      intros hidx.
      unfold tnum_sub.
      rewrite tnum.ith_m_simplify2.
      unwrap_bvec_ops.
      repeat rewrite bvec_fulladd_result. repeat rewrite bvec_fullsub_result.

      (* TODO why don't reuse sublemma32 here? If doing, do the same for addition as well. *)

      intro H.
      assert (hmp : bvec_ith (tnum.m P) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m P) hidx);
        repeat simplify_bit_ops; try easy.

      assert (hmq : bvec_ith (tnum.m Q) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m Q) hidx);
        repeat simplify_bit_ops; try easy.

      apply bit_or_zero_zero in H as (H1 & H2).
      apply bit_xor_x_y_zero in H1.

      rewrite hmp in H1. rewrite hmq in H1.
      apply xor_x_y_eq_z_y in H1.

      (* H1 seems interesting at this point:
         bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
         bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx
       *)
      apply sublemma45; auto.
  Qed.

  Lemma tnum_sub_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q -> tnum.wellformed (tnum_sub P Q).
  Proof.
    unfold tnum.wellformed.
    intro H.
    unfold tnum_sub.
    apply wellformed_general.
  Qed.

  Lemma tnum_sub_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_sub P Q) /\
      ingamma (bvec_sub x y) (tnum_sub P Q).
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.

    pose (H'1 := sublemma33 x y P Q H).

    unfold tnum.ith_m in H.
    destruct H as (wf1 & wf2 & igP & igQ).

    split. apply tnum_sub_wellformed; auto.

    pose (H'2 := sublemma32 P Q wf1 wf2). unfold tnum.ith_m in H'2. (* TODO rename *)
    unfold ingamma.

    intros i hidx rmskz.

    specialize (H'2 i hidx rmskz) as (xmskz & ymskz & binmskz).
    specialize (H'1 i hidx rmskz).
    revert rmskz.

    revert binmskz.

    unfold tnum_sub.
    rewrite tnum.ith_m_simplify.
    rewrite tnum.ith_v_simplify.

    unwrap_bvec_ops. repeat rewrite bvec_fullsub_result.
    rewrite xmskz. rewrite ymskz. rewrite igP; auto. rewrite igQ; auto. simpl.

    unfold tnum.ith_v.

    intros H1 H2.

    (* Replaces the subexpression H2 from the goal with zero because it is
     * the ith bit of `mu` (the `mu` from `sv & ~mu`), which is zero as per
     * the assumption.
     *)
    rewrite H2. simpl.
    rewrite H'1.
    rewrite bit_and_right_one.
    auto.
  Qed.
End linux_tnum_subtraction.
