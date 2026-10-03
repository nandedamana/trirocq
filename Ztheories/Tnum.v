From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  Bit
  BitVector.

(** printing < %\texttt{<}% *)

Ltac rewrite_if_holds H :=
  match type of H with
  | ?b = ?b -> _ => rewrite H
  end.

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t SIZE := cons (v : bvec SIZE) (m : bvec SIZE).

  Section tnum_helpers.
    Context [SIZE : nat].

    Definition v (P : t SIZE) := match P with cons _ v _ => v end.
    Definition m (P : t SIZE) := match P with cons _ _ m => m end.

    Definition ith_v (tn : t SIZE) i := bvec_ith (v tn) i.
    Definition ith_m (tn : t SIZE) i := bvec_ith (m tn) i.

    (**
     * Reasoning about the ith bit when [i >= SIZE] is not only
     * meaningless, but impossible in the presence of bvec_neg
     * (bvec_neg_rel requires i < SIZE).
     *)
    Definition wellformed (tn : t SIZE) :=
      forall i, i < SIZE ->
                bvec_ith (m tn) i = one -> bvec_ith (v tn) i = zero.

    Lemma ith_m_simplify n1 n2 i :
      ith_m (cons SIZE n1 n2) i = bvec_ith n2 i.
    Proof.
      unfold ith_m. simpl. reflexivity.
    Qed.

    Lemma ith_m_simplify2 n1 n2 i :
      bvec_ith (m (cons SIZE n1 n2)) i = bvec_ith n2 i.
    Proof.
      simpl. reflexivity.
    Qed.

    Lemma ith_v_simplify n1 n2 i :
      ith_v (cons SIZE n1 n2) i = bvec_ith n1 i.
    Proof.
      unfold ith_v. simpl. reflexivity.
    Qed.

    Lemma ith_v_simplify2 n1 n2 i :
      bvec_ith (v (cons SIZE n1 n2)) i = bvec_ith n1 i.
    Proof.
      simpl. reflexivity.
    Qed.

    (* Using `unfold m` directly could cause unwanted expansions in some places. *)
    Lemma m_cons_simplify n1 n2 : m (cons SIZE n1 n2) = n2.
      unfold m. reflexivity.
    Qed.

    Lemma v_cons_simplify n1 n2 : v (cons SIZE n1 n2) = n1.
      unfold v. reflexivity.
    Qed.

  End tnum_helpers.
End tnum.

Definition ingamma {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) :=
  forall i, i < SIZE ->
            tnum.ith_m T i = false -> bvec_ith x i = tnum.ith_v T i.

(**
 * 2-ary function F on tnum is a sound abstraction of f on bvec.
 * `sound f F` instead of `sound F f` in order to be consistent with `ingamma`.
 *)
Definition sound2 SIZE
  (f : bvec SIZE -> bvec SIZE -> bvec SIZE)
  (F : tnum.t SIZE -> tnum.t SIZE -> tnum.t SIZE) :=
  forall (p q : bvec SIZE) P Q,
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma p P -> ingamma q Q ->
    tnum.wellformed (F P Q) /\ ingamma (f p q) (F P Q).

Definition subset {SIZE} (P Q : tnum.t SIZE) :=
  forall x, ingamma x P -> ingamma x Q.

(**
 * If F is an optimal approximation of f, that means F(P, Q) is
 * a subset of F'(P, Q), for any sound approximation F' of f.
 *)
Definition optimal2 SIZE (f : bvec SIZE -> bvec SIZE -> bvec SIZE) F :=
  sound2 SIZE f F ->
  forall F', sound2 SIZE f F' ->
             forall (P Q : tnum.t SIZE),
               tnum.wellformed P -> tnum.wellformed Q -> subset (F P Q) (F' P Q).

Section tnum_shift.
  Variable SIZE : nat.

  Definition tnum_lshift (P : tnum.t SIZE) (n : POS) : tnum.t SIZE :=
    tnum.cons _ (bvec_lshift (tnum.v P) n) (bvec_lshift (tnum.m P) n).

  Lemma tnum_lshift_wellformed (P : tnum.t SIZE) (n : POS) :
    tnum.wellformed P -> tnum.wellformed (tnum_lshift P n).
  Proof.
    unfold tnum.wellformed.
    intros wfp i hi.
    unfold tnum_lshift, bvec_ith, bvec_lshift. cbn.

    assert (hin : (n <= i)%nat \/ (i < n)%nat) by lia.
    destruct hin as [hin1 | hin2].
    -
      pose (h := Z.shiftl_spec_high (bvec2Z SIZE (tnum.m P)) (POS2Z n)).
      unfold modulus, POS2Z.
      rewrite !Z.mod_pow2_bits_low by lia.
      rewrite h by (unfold POS2Z; lia).
      rewrite Z.shiftl_spec_high by lia.
      unfold POS2Z.
      assert (hsub : i - n < SIZE) by lia.
      specialize (wfp (i - n) hsub).
      unfold bvec_ith in wfp.
      rewrite Nat2Z.inj_sub in wfp by lia.
      auto.
    -
      unfold modulus, POS2Z.
      rewrite !Z.mod_pow2_bits_low by lia.
      rewrite Z.shiftl_spec_low by lia. easy.
  Qed.

  Lemma tnum_lshift_sound (x : bvec SIZE) (P : tnum.t SIZE) (n : POS) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_lshift P n) /\ ingamma (bvec_lshift x n) (tnum_lshift P n).
  Proof.
    unfold tnum.wellformed, ingamma.
    unfold tnum.ith_m, tnum.ith_v, bvec_ith.
    cbn.
    intros wfp igx.
    split.
    - apply tnum_lshift_wellformed. auto.
    -
      revert wfp igx.
      destruct P. cbn.
      intros wfp igx.
      intro i.

      assert (hin : (n <= i)%nat \/ (i < n)%nat) by lia.
      destruct hin as [hin1 | hin2].
      +
        pose (h := Z.shiftl_spec_high m (POS2Z n)).
        unfold modulus, POS2Z.
        intro hi.
        rewrite !Z.mod_pow2_bits_low by lia.
        rewrite !Z.shiftl_spec_high by lia.
        intro hm.
        repeat rewrite <- Nat2Z.inj_sub by lia.
        apply igx.
        lia.
        rewrite Nat2Z.inj_sub by lia. assumption.
      +
        unfold modulus, POS2Z.
        intro hi.
        rewrite !Z.mod_pow2_bits_low by lia.
        rewrite Z.shiftl_spec_low by lia.
        rewrite !Z.shiftl_spec_low by lia.
        auto.
  Qed.

  Local Open Scope Z_scope.

  Definition tnum_rshift (P : tnum.t SIZE) (n : POS) : tnum.t SIZE.
  Proof.
    exists.
    - exists (bvec_rshift (tnum.v P) n).
      apply bvec_rshift_pf.
    - exists (bvec_rshift (tnum.m P) n).
      apply bvec_rshift_pf.
  Defined.

  Lemma highbits_pos_bound_Z x :
    0 <= x < 2 ^ Z.of_nat SIZE ->
    forall i n, i + n >= Z.of_nat SIZE ->
                Z.testbit x (i + n) = false.
  Proof.
    intro hbounds.
    intros i n hin.

    (* Z.bits_above_log2 can only handle the former *)
    assert (hge0 : 0 = x \/ 0 < x). lia.

    destruct hge0 as [h0 | hgt].
    + rewrite <- h0.
      apply Z.bits_0.
    + apply Z.bits_above_log2.
      lia.

      apply Z.log2_lt_pow2.
      simpl in hgt. lia.

      apply Z.lt_le_trans with (m := 2 ^ Z.of_nat SIZE). lia.
      apply Z.pow_le_mono_r; lia.
  Qed.

  Lemma tnum_rshift_wellformed (P : tnum.t SIZE) (n : POS) :
    tnum.wellformed P -> tnum.wellformed (tnum_rshift P n).
  Proof.
    unfold tnum.wellformed.
    intros wfp i hi.
    unfold tnum_rshift, bvec_ith, bvec_rshift. cbn.

    pose (h := Z.shiftr_spec (bvec2Z SIZE (tnum.m P)) (POS2Z n)).
    unfold modulus, POS2Z.
    rewrite h by (unfold POS2Z; lia).
    rewrite Z.shiftr_spec by lia.
    unfold POS2Z.
    rewrite <- Nat2Z.inj_add.

    assert (hin : (i + n < SIZE)%nat \/ (i + n >= SIZE)%nat) by lia.
    destruct hin as [hin1 | hin2].
    - apply wfp. assumption.
    -
      rewrite Nat2Z.inj_add.
      rewrite highbits_pos_bound_Z.
      easy.
      destruct P as [v m]. cbn. destruct m; auto.
      lia.
  Qed.

  Lemma tnum_rshift_sound (x : bvec SIZE) (P : tnum.t SIZE) (n : POS) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_rshift P n) /\ ingamma (bvec_rshift x n) (tnum_rshift P n).
  Proof.
    unfold tnum.wellformed, ingamma.
    unfold tnum.ith_m, tnum.ith_v, bvec_ith.
    cbn.
    intros wfp igx.
    split.
    - apply tnum_rshift_wellformed. auto.
    -
      revert wfp igx.
      destruct P. cbn.
      intros wfp igx.
      intro i.

      assert (hin : (i + n < SIZE)%nat \/ (i + n >= SIZE)%nat) by lia.
      destruct hin as [hin1 | hin2].
      +
        pose (h := Z.shiftr_spec m (POS2Z n)).
        unfold modulus, POS2Z.
        intro hi.
        rewrite !Z.shiftr_spec by lia.
        specialize (igx (i + n)%nat).
        rewrite Nat2Z.inj_add in igx. auto.
      +
        rewrite !Z.shiftr_spec; try (unfold POS2Z; lia).
        destruct x as [x hx], v as [v hv], m as [m hm].

        intro hi.

        cbn.
        unfold modulus in hx, hv, hm.
        rewrite !highbits_pos_bound_Z; (unfold POS2Z; try lia).
  Qed.

(* TODO merge wellformed and soundness proofs?
 * Not so easy. Well, converting the goal `wellformed T /\ ingamma x T`
 * to `forall i, (wellformed_ith T /\ ingamma_ith x T)` is easy
 * (after which the same steps in tnum_*shift_sound proves the
 * wellformedness as well), but the issue is that, `wellformed T`
 * alone cannot be derived from it without giving some x.
 *)
End tnum_shift.

Arguments tnum_lshift {SIZE}.
Arguments tnum_lshift_wellformed {SIZE}.
Arguments tnum_lshift_sound {SIZE}.

Arguments tnum_rshift {SIZE}.
Arguments tnum_rshift_wellformed {SIZE}.
Arguments tnum_rshift_sound {SIZE}.

Local Open Scope Z_scope.

Section tnum_shift.
  Definition tnum_trunc {n} (P : tnum.t n) {m} (hm : (m <= n)%nat) : tnum.t m.
    destruct P as [pv pm].
    split.
    - destruct pv as [pv hpv].
      exists (pv mod modulus m).
      apply Z.mod_pos_bound.
      unfold modulus. lia.
    - destruct pm as [pm hpm].
      exists (pm mod modulus m).
      apply Z.mod_pos_bound.
      unfold modulus. lia.
  Defined.

  Lemma tnum_trunc_wellformed {n} (P : tnum.t n) {m} (hm : (m <= n)%nat) :
    tnum.wellformed P -> tnum.wellformed (tnum_trunc P hm).
  Proof.
    destruct P as [pv pm].
    destruct pv as [pv hpv], pm as [pm hpm].
    unfold tnum.wellformed, bvec_ith, tnum.v, tnum.m. cbn.
    intros wfp i him.
    unfold modulus.
    rewrite !Z.mod_pow2_bits_low. apply wfp.
    lia.
    unfold POS2Z. lia.
    unfold POS2Z. lia.
  Qed.

  Lemma tnum_trunc_sound {n} (x : bvec n) (P : tnum.t n) {m} (hm : (m <= n)%nat) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_trunc P hm) /\
      ingamma (bvec_trunc x hm) (tnum_trunc P hm).
  Proof.
    intros wfp igx.
    split.
    - apply tnum_trunc_wellformed. assumption.
    - revert wfp igx.
      unfold tnum.wellformed, ingamma.
      destruct P as [pv pm].
      destruct pv as [pv hpv], pm as [pm hpm].
      destruct x as [x hx].
      unfold tnum.v, tnum.m.
      unfold tnum.ith_m, tnum.ith_v, bvec_ith. cbn.
      unfold bvec_trunc.

      intros wfp igx i hi.
      unfold modulus.
      rewrite !Z.mod_pow2_bits_low by (unfold POS2Z; lia).
      assert (i < n)%nat. lia.
      apply igx. assumption.
  Qed.

  Definition tnum_rshift1_shrink {n} (P : tnum.t (S n)) : tnum.t n :=
    tnum_trunc (tnum_rshift P 1%nat) (Nat.le_succ_diag_r n).

  Lemma tnum_rshift1_shrink_wellformed {n} (P : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed (tnum_rshift1_shrink P).
  Proof.
    intro wfp.
    unfold tnum_rshift1_shrink.
    apply tnum_trunc_wellformed.
    apply tnum_rshift_wellformed.
    assumption.
  Qed.

  Lemma tnum_rshift1_shrink_sound {n} (x : bvec (S n)) (P : tnum.t (S n)) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_rshift1_shrink P) /\
      ingamma (bvec_rshift1_shrink x) (tnum_rshift1_shrink P).
  Proof.
    intros wfp igx.

    split.
    - apply tnum_rshift1_shrink_wellformed; auto.
    -
      unfold tnum_rshift1_shrink, bvec_rshift1_shrink.
      apply tnum_trunc_sound.
      apply tnum_rshift_wellformed. assumption.
      apply tnum_rshift_sound; auto.
  Qed.
End tnum_shift.

Definition zerotnum n := tnum.cons n (zerovec n) (zerovec n).

Lemma zerotnum_wellformed {n} : tnum.wellformed (zerotnum n).
  unfold tnum.wellformed.
  intro i. simpl.
  rewrite zerovec_ith. easy.
Qed.

Lemma ingamma_value {SIZE} (P : tnum.t SIZE) : ingamma (tnum.v P) P.
  unfold ingamma.
  auto.
Qed.

Lemma ingamma_value_bitor_mask :
  forall {SIZE} (P : tnum.t SIZE),
    ingamma (bvec_or (tnum.v P) (tnum.m P)) P.
Proof.
  intros SIZE P.
  unfold ingamma, tnum.ith_m, tnum.ith_v.
  intros i.
  rewrite bvec_or_rel.
  repeat destruct (bvec_ith (_ P) i);
    auto.
Qed.

Ltac unwrap_bvec_ops := match goal with
                          _ => repeat rewrite bvec_and_rel;
                               repeat rewrite bvec_neg_rel;
                               repeat rewrite bvec_or_rel;
                               repeat rewrite bvec_xor_rel
                        end.
