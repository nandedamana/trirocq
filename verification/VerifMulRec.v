(* Boilerplate copied from Software Foundations Verifiable C *)
(* See https://vst.cs.princeton.edu/download/VC.pdf for refman *)
Require Import VST.floyd.proofauto.
Require Import trirocq.Verification.tnumPtrDotC.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

From Stdlib Require Import
  Arith
  ZArith.

From trirocq.Z Require Import
  BitVector
  Tnum
  TnumMul.

From trirocq.Verification Require Import
  Common
  VerifAdd
  VerifShift
  VerifUnion.

Definition u64_to_Z (x : u64) := uint2Z 64 x.
Coercion u64_to_Z : u64 >-> Z.

(* TODO move out *)
Section uint_helpers.
  Context (n : nat).

  Lemma uint2Z_pos (x : uint n) : uint2Z _ x >= 0.
    destruct x as [x hx].
    cbn. lia.
  Qed.

  Lemma hbvzid m : 0 <= m < modulus n -> uint2Z n (Z2uint n m) = m.
    intro hm.
    cbn.
    auto.
    apply Z.mod_small; auto.
  Qed.

  Lemma hbvzid_mod m : uint2Z n (Z2uint n m) = m mod modulus n.
    auto.
  Qed.

  Lemma Z2uint_uint2Z (x : uint n) : Z2uint n (uint2Z n x) = x.
    apply uint_eq_by_ith.
    intros i hi.
    destruct x.
    unfold uint_ith. cbn.
    unfold modulus.
    rewrite Z.mod_pow2_bits_low; auto.
    apply Nat2Z.inj_lt; auto.
  Qed.
End uint_helpers.

Lemma Z2nat_of_u64_of_Z x :
  0 <= x < modulus 64 -> Z.to_nat (u64_to_Z (Z2uint 64 x)) = Z.to_nat x.
Proof.
  cbn.
  intro hx.
  rewrite Z.mod_small by lia. auto.
Qed.

Hint Rewrite hbvzid : convuint_db.
Hint Rewrite hbvzid_mod : convuint_db.
Hint Rewrite Z2uint_uint2Z : convuint_db.
Hint Rewrite Z2nat_of_u64_of_Z : convuint_db.

Definition trunctnum (n : nat) (v m : u64) : tnum.t n :=
  tnum.cons n (Z2uint n v) (Z2uint n m).

(* TODO simplify using u64_to_Z (coercion) *)
(* TODO port the improvements made in this proof to other proofs:
 * - u64_to_Z
 * - removal of rv, rm
 * - use of `hint`
 *)
Definition tnum_mul_loop_spec : ident * funspec :=
  DECLARE _tnum_mul_loop
    WITH m : u64,
         a : val, sha : share,
         b : val, shb : share,
         r : val, shr : share,
         av : u64, am : u64, bv : u64, bm : u64, rv : u64, rm : u64
    PRE [ tulong, tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr) ]
    PROP ( readable_share sha; readable_share shb; writable_share shr;
           ((Z.to_nat m) <= 64)%nat;
           (* In the rocq version, av gets truncated with each call; in C, I cannot change the
            * word size.
            *)
           (uint2Z _ av) = av mod (modulus (Z.to_nat m)); (uint2Z _ am) = am mod (modulus (Z.to_nat m))
    )
    PARAMS (Vlong (Int64.repr m); a; b; r)
    GLOBALS ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ av)), Vlong (Int64.repr (uint2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ bv)), Vlong (Int64.repr (uint2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ rv)), Vlong (Int64.repr (uint2Z _ rm))) r
    )
    POST [ tvoid ]
    (* TODO prove that the use of trunctnum is fine. Make use of tnum_trunc, etc. if needed. *)
    EX (expacc : tnum.t 64), PROP (expacc = tnum_mul_loop (Z.to_nat m) (trunctnum (Z.to_nat m) av am) _ (tnum.cons _ bv bm) (tnum.cons _ rv rm))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ av)), Vlong (Int64.repr (uint2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ bv)), Vlong (Int64.repr (uint2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ (tnum.v expacc))), Vlong (Int64.repr (uint2Z _ (tnum.m expacc)))) r
    ).

Definition Gprog := [ tnum_add_spec; tnum_lshift_spec; tnum_mul_loop_spec; tnum_rshift_spec; tnum_union_spec ].

Lemma trq_mod64_is_cc_mod64 : modulus 64 = Int64.modulus.
  compute. lia.
Qed.

From Stdlib.ZArith Require Import Zbitwise.

Lemma hlsbavnz (av : u64) :
  Int64.and (Int64.repr av) (Int64.repr 1) <> Int64.zero ->
  uint_lsb av = true.
Proof.
  destruct av as [av avh].
  unfold Int64.and, Int64.zero. cbn.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite trq_mod64_is_cc_mod64 in avh.
  rewrite Z.mod_small by auto.
  intro ccne.
  apply repr64_neq_e in ccne.
  change 1 with (Z.ones 1) in ccne.
  rewrite Z.land_ones in ccne by lia.
  rewrite <- Z.bit0_odd.
  rewrite <- Z.mod_pow2_bits_low with (n := 1) by lia.
  change (2 ^ 1) with 2 in *.
  assert (H : Z.b2z (Z.testbit (av mod 2) 0) <> 0).
  rewrite Z.bit0_mod. rewrite Z.mod_mod by lia; auto.
  unfold Z.b2z in H.
  destruct (Z.testbit (av mod 2) 0); auto.
Qed.

Lemma TODO92 n : 0 <= n < modulus 64 -> 0 <= n <= Int64.max_unsigned.
  unfold modulus, Int64.max_unsigned.
  change (Z.of_nat 64) with 64.
  change Int64.modulus with (2 ^ 64).
  intro h. lia.
Qed.

Lemma TODO93 n : 0 <= n < Int64.modulus -> 0 <= n < modulus 64.
  unfold modulus.
  change (Z.of_nat 64) with 64.
  change Int64.modulus with (2 ^ 64).
  intro h. lia.
Qed.

Lemma hlsbavz (av : u64) :
  Int64.and (Int64.repr av) (Int64.repr 1) = Int64.zero ->
  uint_lsb av = false.
Proof.
  destruct av as [av avh].
  unfold Int64.and, Int64.zero. cbn.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite trq_mod64_is_cc_mod64 in avh.
  rewrite Z.mod_small by auto.
  intro ccne.

  apply repr_inj_unsigned64 in ccne.
  change 1 with (Z.ones 1) in ccne.
  rewrite Z.land_ones in ccne by lia.
  rewrite <- Z.bit0_odd.
  rewrite <- Z.mod_pow2_bits_low with (n := 1) by lia.
  change (2 ^ 1) with 2 in *.
  assert (H : Z.b2z (Z.testbit (av mod 2) 0) = 0).
  rewrite Z.bit0_mod. rewrite Z.mod_mod by lia; auto.
  unfold Z.b2z in H.
  destruct (Z.testbit (av mod 2) 0); easy.
  apply TODO92.
  apply BitVector.Z_land_bounded.
  apply TODO93; auto.
  split; try lia. compute. auto.
  split; try lia. unfold Int64.max_unsigned.
  change Int64.modulus with (2 ^ 64). lia.
Qed.

(* TODO rename and move *)
Lemma TODO91 : forall n m,
    0 <= m <= u64_to_Z n ->
    Z.of_nat (Z.to_nat (u64_to_Z n - m)) = u64_to_Z n - m.
Proof.
  destruct n as [n hn].
  cbn.
  intros m' hn'.
  rewrite Z2Nat.inj_sub by lia.
  rewrite Nat2Z.inj_sub by lia.
  cbn.
  rewrite !Z2Nat.id; lia.
Qed.

(* TODO rename and move *)
Lemma hmodpre (m : u64) (av : Z) : 1 <= m -> av < 2 ^ m -> Z.div2 av < 2 ^ (m - 1).
Proof.
  destruct m as [m mh]. cbn.
  intros hm' h'.
  replace (2 ^ m) with (2 * (2 ^ (m - 1))) in h'.
  rewrite Z.div2_div.
  apply Z.div_lt_upper_bound; lia.
  replace m with (Z.succ (m - 1)) at 2 by lia.
  rewrite Z.pow_succ_r by lia. reflexivity.
Qed.

Lemma hrshift :
  forall (m : u64) (h : 1 <= m) av (avtrunc : uint2Z 64 av = u64_to_Z av mod modulus (Z.to_nat (u64_to_Z m))),
    uint2Z 64 (uint_rshift av 1%nat) =
      uint2Z 64 (uint_rshift av 1%nat) mod modulus (Z.to_nat (u64_to_Z m - 1)).
Proof.
  intros m hm av' avtrunc'.
  destruct av' as [av' avh']. cbn.
  rewrite Z.mod_small. reflexivity.

  unfold modulus. rewrite TODO91.
  split. rewrite Z.div2_div. change 0 with (0 / 2). apply Z.div_le_mono; lia.

  Set Printing Coercions.
  apply hmodpre; try lia.
  cbn in avtrunc'. rewrite avtrunc'.
  replace (modulus (Z.to_nat (u64_to_Z m))) with (2 ^ m).
  apply Z.mod_pos_bound. lia.
  unfold modulus.
  rewrite Z2Nat.id. reflexivity.
  lia. lia.
Qed.

Lemma body_tnum_mul_spec : semax_body Vprog Gprog f_tnum_mul_loop tnum_mul_loop_spec.
Proof.
  start_function.

  forward_if.
  - (* m != 0 *)
    Set Printing Coercions.

    assert (u64_to_Z m <> 0) by (apply repr64_neq_e; auto).
    assert (u64_to_Z m >= 0) by apply uint2Z_pos.
    assert (u64_to_Z m > 0) by lia.
    assert (Z.to_nat m <> 0%nat). lia.

    assert (hm : exists mp, Z.to_nat m = S mp).
    destruct (Z.to_nat m); try easy; try eauto.
    destruct hm as [mp hm].

    (* Just to give manual names *)
    assert (avtrunc :
             uint2Z 64 av = u64_to_Z av mod modulus (Z.to_nat (u64_to_Z m))) by auto.
    assert (amtrunc :
             uint2Z 64 am = u64_to_Z am mod modulus (Z.to_nat (u64_to_Z m))) by auto.

    repeat forward.
    forward_if.
    + (* (a.value | a.mask) != 0 *)

      (* Give a fixed name *)
      assert (havmcc :
               Int64.or (Int64.repr (uint2Z 64 av)) (Int64.repr (uint2Z 64 am)) <> Int64.zero) by auto.

      assert (havm : Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                       (uint_denote (tnum.m (trunctnum (S mp) av am))) <> 0).
      rewrite or64_repr in havmcc.
      unfold tnum.v, tnum.m, trunctnum.
      apply repr64_neq_e in havmcc.
      replace (S mp) with (Z.to_nat m).
      cbn.
      rewrite avtrunc, amtrunc in havmcc. auto.

      repeat forward.

      (* TODO move out *)
      assert (uint_denote_nonneg : forall SIZE (x : uint SIZE), 0 <= uint_denote x).
      intros. destruct x. cbn. lia.

      (* TODO combine with havm somehow *)
      (* Helps eliminate the neg branch during destruction. *)
      assert (havmpos0 : 0 <= Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                          (uint_denote (tnum.m (trunctnum (S mp) av am)))).
      apply Z.lor_nonneg.
      split; apply uint_denote_nonneg.

      (* TODO REM *)
      (*
      assert (havmpos : Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                          (uint_denote (tnum.m (trunctnum (S mp) av am))) > 0).
       *)

      forward_if.
      *
        (* LSB(a.v) = 1 *)
        apply hlsbavnz in H8.

        assert (hlsbav : uint_lsb (tnum.v (trunctnum (S mp) av am)) = true).
        unfold uint_lsb in H8.
        unfold uint_lsb, tnum.v, trunctnum, uint_ith.
        unfold uint_ith in H8.
        autorewrite with convuint_db using auto.
        rewrite <- hm.
        rewrite <- avtrunc.
        auto.

        (* tnum_add *)
        forward_call (r, shr, &v_bp, Tsh, &v_sum, Tsh, rv, rm, bv, bm).

        Intro vret.
        repeat forward.

        (* tnum_rshift *)
        forward_call (&v_ap, Tsh, Z2uint 8 1, &v_apsh, Tsh, av, am).
        Intros vret_rsh.

        (* tnum_lshift *)
        forward_call (&v_bp, Tsh, Z2uint 8 1, &v_bpsh, Tsh, bv, bm).
        Intros vret_lsh.

        (* tnum_mul_loop *)
        forward_call ((Z2uint 64 (m - 1) : u64), &v_apsh, Tsh, &v_bpsh, Tsh, r, shr,
                       (tnum.v (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                       (tnum.m (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                       (tnum.v (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                       (tnum.m (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                       tnum.v vret, tnum.m vret
                     ).
        entailer!.
        cbn.

        autorewrite with convuint_db using auto.

        rewrite Z.mod_small. reflexivity.
        lia.

        entailer!.

        assert (hrshift' :
                 forall av (avtrunc : uint2Z 64 av = u64_to_Z av mod modulus (Z.to_nat (u64_to_Z m))),
                   uint2Z 64 (uint_rshift av 1%nat) =
                     uint2Z 64 (uint_rshift av 1%nat) mod modulus (Z.to_nat (u64_to_Z m - 1))).
        apply hrshift; lia.

        repeat split.
        ** autorewrite with convuint_db using auto. lia. auto.
           unfold modulus. nia.
        ** autorewrite with convuint_db using auto.
           unfold tnum_rshift. cbn -[uint_rshift].
           apply (hrshift' _ avtrunc).

           (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor *)
           split; try lia.
           assert (u64_to_Z m < modulus 64).
           destruct m as [m hm']; cbn. cbn in hm'. lia.
           lia.
        ** autorewrite with convuint_db using auto.
           unfold tnum_rshift. cbn -[uint_rshift].
           apply (hrshift' _ amtrunc).

           (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
           split; try lia.
           assert (u64_to_Z m < modulus 64).
           destruct m as [m hm']; cbn. cbn in hm'. lia.
           lia.
        **
          Exists (tnum_mul_loop (Z.to_nat (u64_to_Z m)) (trunctnum (Z.to_nat (u64_to_Z m)) av am)
                    63 (tnum.cons 64 bv bm) (tnum.cons 64 rv rm)).
          Intros vret_mul.
          entailer!.

          (* rewrite only in the RHS *)
          rewrite !tnum_mul_loop_less_branchify with (m := (Z.to_nat (u64_to_Z m))).

          rewrite !hm.

          (* TODO simplify based on havm *)
          unfold tnum_mul_loop_less_branch.
          rewrite hlsbav.
          fold tnum_mul_loop_less_branch.

          (* To simplify the match inside the unfolded function *)
          destruct (Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                      (uint_denote (tnum.m (trunctnum (S mp) av am)))); try easy.

          assert (cancel_tnum_cons : forall n P, tnum.cons n (tnum.v P) (tnum.m P) = P).
          intros. destruct P. auto.

          rewrite !cancel_tnum_cons.

          rewrite <- tnum_mul_loop_less_branchify.

          autorewrite with convuint_db using auto.

          replace (Z.to_nat (u64_to_Z m - 1)) with mp.

          replace (trunctnum mp
                     (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
                     (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat)))
            with (tnum_rshift1_shrink (trunctnum (S mp) av am)).

          unfold tnum_rshift1_shrink.
          entailer!.

          (* TODO move out *)
          (* tnum_rshift1_shrink (trunctnum (S mp) av am) =
               trunctnum mp (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
               (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat))
           *)
          unfold tnum_rshift1_shrink.
          unfold trunctnum.

          unfold tnum_rshift, tnum.m, tnum.v.
          unfold tnum_trunc. f_equal.
          ***
            apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
            cbn -[Z.pow].
            rewrite avtrunc.
            rewrite hm. reflexivity.
          ***
            apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
            cbn -[Z.pow].
            rewrite amtrunc.
            rewrite hm. reflexivity.
          (* ------------------------------------------------------------------- *)

          *** lia.
          ***
           (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
           split; try lia.
           assert (u64_to_Z m < modulus 64).
           destruct m as [m hm']; cbn. cbn in hm'. lia.
           lia.
      *
        (* LSB(a.v) = 0 *)
        repeat forward.
        (* H8 : Int64.and (Int64.repr (uint2Z 64 av)) (Int64.repr 1) = Int64.zero *)
        apply hlsbavz in H8.

        assert (hlsbav : uint_lsb (tnum.v (trunctnum (S mp) av am)) = false).
        unfold uint_lsb in H8.
        unfold uint_lsb, tnum.v, trunctnum, uint_ith.
        unfold uint_ith in H8.
        autorewrite with convuint_db using auto.
        rewrite <- hm.
        rewrite <- avtrunc.
        auto.

        forward_if.
        **
          (* LSB(a.m) = 1 *)
          apply hlsbavnz in H9.

          assert (hlsbam : uint_lsb (tnum.m (trunctnum (S mp) av am)) = true).
          unfold uint_lsb in H9.
          unfold uint_lsb, tnum.m, trunctnum, uint_ith.
          unfold uint_ith in H9.
          autorewrite with convuint_db using auto.
          rewrite <- hm.
          rewrite <- amtrunc.
          auto.

          (* tnum_add *)
          forward_call (r, shr, &v_bp, Tsh, &v_sum__1, Tsh, rv, rm, bv, bm).

          Intro vret.
          repeat forward.

          (* tnum_union *)
          forward_call (r, shr, &v_sum__1, Tsh, &v_joined, Tsh, rv, rm,
                         (tnum.v vret : u64),
                         (tnum.m vret : u64)).
          Intro vret_union.

          repeat forward.

          (* tnum_rshift *)
          forward_call (&v_ap, Tsh, Z2uint 8 1, &v_apsh__1, Tsh, av, am).
          Intros vret_rsh.

          (* tnum_lshift *)
          forward_call (&v_bp, Tsh, Z2uint 8 1, &v_bpsh__1, Tsh, bv, bm).
          Intros vret_lsh.

          (* tnum_mul_loop *)
          forward_call ((Z2uint 64 (m - 1) : u64), &v_apsh__1, Tsh, &v_bpsh__1, Tsh, r, shr,
                         (tnum.v (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                         (tnum.m (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                         (tnum.v (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                         (tnum.m (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                         tnum.v vret_union, tnum.m vret_union
                       ).
          entailer!.
          cbn.
          rewrite Z.mod_small. reflexivity.
          lia.

          entailer!.

          assert (hrshift' :
                   forall av (avtrunc : uint2Z 64 av = u64_to_Z av mod modulus (Z.to_nat (u64_to_Z m))),
                     uint2Z 64 (uint_rshift av 1%nat) =
                       uint2Z 64 (uint_rshift av 1%nat) mod modulus (Z.to_nat (u64_to_Z m - 1))).
          apply hrshift; lia.

          repeat split.
          *** autorewrite with convuint_db using auto. lia. auto.
              unfold modulus. nia.
          *** autorewrite with convuint_db using auto.
              unfold tnum_rshift. cbn -[uint_rshift].
              apply (hrshift' _ avtrunc).

              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
          *** autorewrite with convuint_db using auto.
              unfold tnum_rshift. cbn -[uint_rshift].
              apply (hrshift' _ amtrunc).

              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
          ***
            Exists (tnum_mul_loop (Z.to_nat (u64_to_Z m)) (trunctnum (Z.to_nat (u64_to_Z m)) av am)
                      63 (tnum.cons 64 bv bm) (tnum.cons 64 rv rm)).
            Intros vret_mul.
            entailer!.

            (* rewrite only in the RHS *)
            rewrite !tnum_mul_loop_less_branchify with (m := (Z.to_nat (u64_to_Z m))).

            rewrite !hm.

            (* TODO simplify based on havm *)
            unfold tnum_mul_loop_less_branch.
            rewrite hlsbam.
            fold tnum_mul_loop_less_branch.

            (* To simplify the match inside the unfolded function *)
            destruct (Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                        (uint_denote (tnum.m (trunctnum (S mp) av am)))); try easy.

            assert (cancel_tnum_cons : forall n P, tnum.cons n (tnum.v P) (tnum.m P) = P).
            intros. destruct P. auto.

            rewrite !cancel_tnum_cons.

            rewrite <- tnum_mul_loop_less_branchify.

            autorewrite with convuint_db using auto.

            replace (Z.to_nat (u64_to_Z m - 1)) with mp.

            replace (trunctnum mp
                       (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
                       (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat)))
              with (tnum_rshift1_shrink (trunctnum (S mp) av am)).

            unfold tnum_rshift1_shrink.

            replace (uint_lsb (tnum.v (trunctnum (S mp) av am))) with false.
            entailer!.

            (* TODO move out *)
            (* tnum_rshift1_shrink (trunctnum (S mp) av am) =
               trunctnum mp (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
               (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat))
             *)
            unfold tnum_rshift1_shrink.
            unfold trunctnum.

            unfold tnum_rshift, tnum.m, tnum.v.
            unfold tnum_trunc. f_equal.
            ****
              apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
              cbn -[Z.pow].
              rewrite avtrunc.
              rewrite hm. reflexivity.
            ****
              apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
              cbn -[Z.pow].
              rewrite amtrunc.
              rewrite hm. reflexivity.
            (* ------------------------------------------------------------------- *)

            **** lia.
            ****
              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
        **
          (* lsb (a.m) = 0 *)

          (* H9 : Int64.and (Int64.repr (uint2Z 64 am)) (Int64.repr 1) = Int64.zero *)
          apply hlsbavz in H9.

          assert (hlsbam : uint_lsb (tnum.m (trunctnum (S mp) av am)) = false).
          unfold uint_lsb in H9.
          unfold uint_lsb, tnum.m, trunctnum, uint_ith.
          unfold uint_ith in H9.
          autorewrite with convuint_db using auto.
          rewrite <- hm.
          rewrite <- amtrunc.
          auto.

          (* tnum_rshift *)
          forward_call (&v_ap, Tsh, Z2uint 8 1, &v_apsh__2, Tsh, av, am).
          Intros vret_rsh.

          (* tnum_lshift *)
          forward_call (&v_bp, Tsh, Z2uint 8 1, &v_bpsh__2, Tsh, bv, bm).
          Intros vret_lsh.

          (* tnum_mul_loop *)
          forward_call ((Z2uint 64 (m - 1) : u64), &v_apsh__2, Tsh, &v_bpsh__2, Tsh, r, shr,
                         (tnum.v (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                         (tnum.m (tnum_rshift (tnum.cons _ av am) 1%nat) : u64),
                         (tnum.v (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                         (tnum.m (tnum_lshift (tnum.cons _ bv bm) 1%nat) : u64),
                         rv, rm).
          entailer!.
          cbn.
          rewrite Z.mod_small. reflexivity.
          lia.

          entailer!.

          assert (hrshift' :
                   forall av (avtrunc : uint2Z 64 av = u64_to_Z av mod modulus (Z.to_nat (u64_to_Z m))),
                     uint2Z 64 (uint_rshift av 1%nat) =
                       uint2Z 64 (uint_rshift av 1%nat) mod modulus (Z.to_nat (u64_to_Z m - 1))).
          apply hrshift; lia.

          repeat split.
          *** autorewrite with convuint_db using auto. lia. auto.
              unfold modulus. nia.
          *** autorewrite with convuint_db using auto.
              unfold tnum_rshift. cbn -[uint_rshift].
              apply (hrshift' _ avtrunc).

              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
          *** autorewrite with convuint_db using auto.
              unfold tnum_rshift. cbn -[uint_rshift].
              apply (hrshift' _ amtrunc).

              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
          ***
            Exists (tnum_mul_loop (Z.to_nat (u64_to_Z m)) (trunctnum (Z.to_nat (u64_to_Z m)) av am)
                      63 (tnum.cons 64 bv bm) (tnum.cons 64 rv rm)).
            Intros vret_mul.
            entailer!.

            (* rewrite only in the RHS *)
            rewrite !tnum_mul_loop_less_branchify with (m := (Z.to_nat (u64_to_Z m))).

            rewrite !hm.

            (* TODO simplify based on havm *)
            unfold tnum_mul_loop_less_branch.
            rewrite hlsbav, hlsbam.
            fold tnum_mul_loop_less_branch.

            (* To simplify the match inside the unfolded function *)
            destruct (Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                        (uint_denote (tnum.m (trunctnum (S mp) av am)))); try easy.

            assert (cancel_tnum_cons : forall n P, tnum.cons n (tnum.v P) (tnum.m P) = P).
            intros. destruct P. auto.

            rewrite !cancel_tnum_cons.
            rewrite <- tnum_mul_loop_less_branchify.
            autorewrite with convuint_db using auto.
            replace (Z.to_nat (u64_to_Z m - 1)) with mp.

            replace (trunctnum mp
                       (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
                       (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat)))
              with (tnum_rshift1_shrink (trunctnum (S mp) av am)).

            unfold tnum_rshift1_shrink.
            entailer!.

            (* TODO move out *)
            (* tnum_rshift1_shrink (trunctnum (S mp) av am) =
               trunctnum mp (tnum.v (tnum_rshift (tnum.cons 64 av am) 1%nat))
               (tnum.m (tnum_rshift (tnum.cons 64 av am) 1%nat))
             *)
            unfold tnum_rshift1_shrink.
            unfold trunctnum.

            unfold tnum_rshift, tnum.m, tnum.v.
            unfold tnum_trunc. f_equal.
            ****
              apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
              cbn -[Z.pow].
              rewrite avtrunc.
              rewrite hm. reflexivity.
            ****
              apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
              cbn -[Z.pow].
              rewrite amtrunc.
              rewrite hm. reflexivity.
          (* ------------------------------------------------------------------- *)

            **** lia.
            ****
              (* 0 <= u64_to_Z m - 1 < modulus 64; TODO refactor COMMON_THM_1 *)
              split; try lia.
              assert (u64_to_Z m < modulus 64).
              destruct m as [m hm']; cbn. cbn in hm'. lia.
              lia.
    +
      (* (a.value | a.mask) = 0 *)

      (* TODO use *)
      (* Give a fixed name *)
      assert (havmcc :
               Int64.or (Int64.repr (uint2Z 64 av)) (Int64.repr (uint2Z 64 am)) = Int64.zero) by auto.

      assert (havm : Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                       (uint_denote (tnum.m (trunctnum (S mp) av am))) = 0).
      rewrite or64_repr in havmcc.
      Search ((Z.lor _  _) mod _).
      unfold trunctnum, tnum.v, tnum.m.
      unfold uint_denote.
      autorewrite with convuint_db.
      apply repr_inj_unsigned64 in havmcc.
      replace (S mp) with (Z.to_nat (u64_to_Z m)).
      rewrite <- avtrunc. rewrite <- amtrunc. auto.

      assert (lorbound := Z_lor_bounded 64 av am).
      assert (h1 : 0 <= Z.lor (u64_to_Z av) (u64_to_Z am) < modulus 64).
      apply lorbound.
      destruct av as [av avh]; cbn; unfold modulus in *; lia.
      destruct am as [am amh]; cbn; unfold modulus in *; lia.

      change (modulus 64) with (2 ^ 64) in h1.
      unfold Int64.max_unsigned. change Int64.modulus with (2 ^ 64). unfold u64_to_Z in h1. lia.
      unfold Int64.max_unsigned. change Int64.modulus with (2 ^ 64). lia.

      forward.
      Exists (tnum_mul_loop (Z.to_nat (u64_to_Z m)) (trunctnum (Z.to_nat (u64_to_Z m)) av am) 63
                (tnum.cons 64 bv bm) (tnum.cons 64 rv rm)).
      entailer!.

      (* rewrite only in the RHS *)
      rewrite !tnum_mul_loop_less_branchify with (m := (Z.to_nat (u64_to_Z m))).

      rewrite !hm.

      (* TODO simplify based on havm *)
      unfold tnum_mul_loop_less_branch.
      fold tnum_mul_loop_less_branch.
      destruct (Z.lor (uint_denote (tnum.v (trunctnum (S mp) av am)))
                  (uint_denote (tnum.m (trunctnum (S mp) av am)))); try easy.
  -
      (* m = 0 *)
      forward.
      Exists (tnum_mul_loop (Z.to_nat (u64_to_Z m)) (trunctnum (Z.to_nat (u64_to_Z m)) av am) 63
                (tnum.cons 64 bv bm) (tnum.cons 64 rv rm)).
      entailer!.
      replace (Z.to_nat (u64_to_Z m)) with 0%nat.
      unfold tnum_mul_loop.
      cbn. auto.

      (* m = 0 *)
      assert (hm0cc : Int64.repr (u64_to_Z m) = Int64.zero) by auto.
      apply repr_inj_unsigned64 in hm0cc;
        try lia; destruct m as [m' hm']; cbn;
        unfold modulus in hm'; lia.
Qed.
