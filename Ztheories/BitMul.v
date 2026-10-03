From Stdlib Require Import
  Lia
  ZArith.

From trirocq.Z Require Import
  Bit
  BitVector.

Local Open Scope Z_scope.

(* A custom definition of bvec_mul was necessary back when
 * I was using list+length-based bit vectors, that too
 * denoted as nat, because Rocq's definition of nat mul
 * doesn't follow the long-multiplication structure
 * used in tnum_mul. When using Z-based bvec, this gap
 * is reduced, but the abstraction is still useful.
 *)
Section bvec_mul.
  (* A version in which a is unpadded after rshift.
   * This makes defining it easier in Rocq, because at least one
   * parameter (the size of the vector a) is decreasing.
   *)
  Fixpoint bvec_mul_loop m (a : bvec m) {struct m} :=
    match m return bvec m -> forall n, bvec (S n) -> bvec (S n) -> bvec (S n) with
    | O => fun (a : bvec 0) n (b acc : bvec (S n)) => acc
    | S mp => fun (a : bvec (S mp)) n (b acc : bvec (S n)) =>
                match (bvec_denote a) return (bvec (S n)) with
                | Z0 => acc
                | Zpos _ =>
                    let nxta := bvec_rshift1_shrink a in
                    let nxtb := bvec_lshift b 1%nat in
                    match (bvec_lsb a) with
                    | false => bvec_mul_loop _ nxta _ nxtb acc
                    | true => bvec_mul_loop _ nxta _ nxtb (bvec_add acc b)
                    end
                | Zneg _ => acc (* Absurd case; handled in the proof *)
                end
    end a.

  Lemma divmul2_odd_pos x (hx : Z.Odd (Z.pos x)) : Z.pos x / 2 * 2 = Z.pos x - 1.
  Proof.
    unfold Z.Odd in hx.
    destruct hx as [f hf].
    rewrite hf.
    rewrite (Z.mul_comm 2).
    rewrite Z.div_add_l by lia.
    change (1 / 2) with 0. nia.
  Qed.

  Lemma divmul2_even_pos x (hx : Z.Even (Z.pos x)) : Z.pos x / 2 * 2 = Z.pos x.
  Proof.
    unfold Z.Even in hx.
    destruct hx as [f hf].
    rewrite hf.
    rewrite (Z.mul_comm 2).
    replace (f * 2 / 2) with f. lia.
    rewrite Z_div_mult_full; lia.
  Qed.

  Lemma bvec_mul_loop_correct : forall m (a : bvec m) n (b acc : bvec (S n)),
      bvec_denote (bvec_mul_loop m a n b acc) =
        (bvec_denote acc + bvec_denote a * bvec_denote b) mod (2 ^ Z.of_nat (S n)).
  Proof.
    induction m.
    -
      destruct a as [a ha]. destruct b as [b hb].
      destruct acc as [acc hacc].

      unfold bvec_mul_loop. cbn.
      assert (a = 0). change (modulus 0) with 1 in ha.
      lia.
      subst. cbn.

      replace (acc + 0) with acc by lia.
      rewrite Z.mod_small. reflexivity.
      replace (Z.pow_pos 2 (PosDef.Pos.of_succ_nat n)) with (modulus (S n))
        by (unfold modulus; lia).
      assumption.
    -
      unfold bvec_mul_loop. fold bvec_mul_loop.
      intros.

      destruct a as [a ha]. destruct b as [b hb].
      destruct acc as [acc hacc].

      simpl bvec_denote at 2.
      destruct a as [ | ap | an ] eqn : ades.
      + (* a = 0 *)
        simpl.
        replace (acc + 0) with acc by lia.
        rewrite Z.mod_small. reflexivity.
        replace (Z.pow_pos 2 (PosDef.Pos.of_succ_nat n)) with (modulus (S n))
          by (unfold modulus; lia).
        assumption.
      + (* a is +ve *)
        assert (heo := Z.Even_or_Odd (Z.pos ap)).

        destruct (bvec_lsb _) eqn : hlsba;
          rewrite IHm;
          unfold bvec_denote, bvec_lshift, bvec_rshift1_shrink;
          simpl;
          replace (Z.pow_pos 2 (PosDef.Pos.of_succ_nat n)) with (modulus (S n))
          by (unfold modulus; lia).

        * (* LSB(a) = 1 *)
          assert (H : Z.Odd (Z.pos ap)).
          cbn -[Z.odd] in hlsba.
          apply Z.odd_spec; auto.

          destruct b as [ | bp | bn ].
          ** rewrite !Z.mod_0_l. rewrite Z.mul_0_r.
             rewrite Z.add_0_r. rewrite Z.mod_mod.
             reflexivity. lia. lia.
          **
            replace (Z.pos bp~0) with (Z.pos bp * 2) by lia.
            rewrite Z.shiftr_div_pow2 by lia.
            change (2 ^ 1) with 2.

            replace ((Z.pos ap / 2) mod modulus m) with (Z.pos ap / 2).

            (* Going to apply Z.mul_mod_distr_l; a being 1 will break
             * a precondition.
             *)
            assert (ha1 : Z.pos ap = 1 \/ Z.pos ap > 1) by lia.
            destruct ha1 as [ha1 | han1].
            *** (* a is 1 *)
              rewrite Pos2Z.inj_mul.
              rewrite ha1. cbn. rewrite Z.add_0_r.
              rewrite Z.mod_mod. reflexivity.
              lia.
            *** (* a > 1 *)
              rewrite <- Z.mul_mod_distr_l; try lia.

              rewrite Z.mul_shuffle3.
              rewrite divmul2_odd_pos by auto.
              rewrite Z.add_mod by lia.
              rewrite Z.mod_mod by lia.
              rewrite <- Znumtheory.Zmod_div_mod.
              rewrite <- Z.add_mod by lia.

              replace (acc + Z.pos bp + Z.pos bp * (Z.pos ap - 1))
                with (acc + Z.pos (ap * bp)) by lia.
              reflexivity.
              lia.

              unfold modulus.

              assert (0 < Z.pos ap / 2).
              apply Z.div_str_pos; lia. nia.

              apply Z.divide_factor_r.
              assert (0 < Z.pos ap / 2).
              apply Z.div_str_pos; lia.
              lia.

            ***
              rewrite Z.mod_small. reflexivity.
              split.
              apply Z.div_pos; try lia.
              unfold modulus.
              apply Zmult_lt_reg_r with (p := 2). lia.
              rewrite divmul2_odd_pos by auto.
              unfold modulus in ha.
              replace (2 ^ Z.of_nat m * 2) with (2 ^ Z.of_nat (S m)).
              lia.
              replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
              rewrite Z.pow_add_r by lia. lia.
          ** (* Absurd case: b is -ve *)
            lia.

        * (* LSB(a) = 0 *)
          assert (H : Z.Even (Z.pos ap)).
          cbn -[Z.odd] in hlsba.
          apply Z.even_spec; auto.
          rewrite <- Z.negb_even in hlsba.
          apply Bool.negb_false_iff. auto.

          destruct b as [ | bp | bn ].
          ** rewrite !Z.mod_0_l by lia.
             rewrite Z.mul_0_r by lia.
             reflexivity.
          **
            replace (Z.pos bp~0) with (Z.pos bp * 2) by lia.
            rewrite Z.shiftr_div_pow2 by lia.
            change (2 ^ 1) with 2.

            replace ((Z.pos ap / 2) mod modulus m) with (Z.pos ap / 2).

            (* Going to apply Z.mul_mod_distr_l; a being 1 will break
             * a precondition.
             *)
            assert (ha1 : Z.pos ap = 1 \/ Z.pos ap > 1) by lia.
            destruct ha1 as [ha1 | han1].
            *** (* a is 1 -- absurd since a is even. *)
              rewrite Pos2Z.inj_mul.
              rewrite ha1. cbn.
              destruct H. lia.
            *** (* a > 1 *)
              destruct H as [x hx].
              rewrite <- Z.mul_mod_distr_l; try lia.

              rewrite Pos2Z.inj_mul.
              rewrite hx.

              rewrite Z.mul_shuffle3.
              replace (2 * x / 2) with x.
              rewrite Z.add_mod by lia.

              rewrite <- Z.add_mod by lia.
              replace (Z.pos bp * (x * 2)) with (x * (2 * Z.pos bp)) by lia.
              rewrite Z.add_mod by lia.
              rewrite Z.mul_mod_distr_l by lia.
              rewrite Z.mul_mod_idemp_r.
              rewrite <- Z.add_mod by lia.
              f_equal. lia.
              lia.
              rewrite Z.mul_comm.
              rewrite Z_div_mult_full by lia. reflexivity.
              assert (0 < Z.pos ap / 2). apply Z.div_str_pos. lia.
              lia.
            ***
              rewrite Z.mod_small. reflexivity.
              split.
              apply Z.div_pos; try lia.
              unfold modulus.
              apply Zmult_lt_reg_r with (p := 2). lia.
              rewrite divmul2_even_pos by auto.
              unfold modulus in ha.
              replace (2 ^ Z.of_nat m * 2) with (2 ^ Z.of_nat (S m)).
              lia.
              replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
              rewrite Z.pow_add_r by lia. lia.

          ** (* Absurd case: b is -ve *)
            lia.
      + (* Absurd case: a is -ve *)
        lia.
  Qed.

  Definition bvec_mul {n} (a b : bvec (S n)) :=
    bvec_mul_loop _ a _ b (zerovec (S n)).

  Lemma bvec_mul_correct : forall n (a b : bvec (S n)),
      bvec_denote (bvec_mul a b) =
        (bvec_denote a * bvec_denote b) mod modulus (S n).
  Proof.
    intros. unfold bvec_mul.
    rewrite bvec_mul_loop_correct.
    cbn.
    reflexivity.
  Qed.
End bvec_mul.
