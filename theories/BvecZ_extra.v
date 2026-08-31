(* Named BvecZ_extra.v because the branch itree contains
 * BvecZ.v that could be merged in future.
 *)

From Stdlib Require Import Lia List ZArith.

From trirocq Require Import Bit.
From trirocq Require Import BitVector.

Import ListNotations.
Local Open Scope Z_scope.

Section Z_to_bvec.
  Variable SIZE : nat.
  Definition modulus := 2 ^ (Z.of_nat SIZE).

  Definition z2bl (n : Z) : list bit.
    exact (List.map bool2bit
              (List.map (fun i => Z.testbit n (Z.of_nat i))
                 (List.seq 0 SIZE))).
  Defined.

  Definition z2bv (x : Z) : bvec SIZE.
    exists (z2bl x).
    unfold z2bl.
    rewrite !List.length_map.
    apply List.length_seq.
  Defined.

  Coercion z2bv : Z >-> bvec.

  Definition bv2z (x : bvec SIZE) : Z :=
    Z.of_nat (bvec_denote x).

  Coercion bv2z : bvec >-> Z.

  (* TODO move *)
  Lemma bitlist_denote_bounded xs : (bitlist_denote xs < 2 ^ length xs)%nat.
  Proof.
    induction xs.
    - auto.
    - rewrite List.length_cons.
      unfold bitlist_denote. fold bitlist_denote.
      rewrite Nat.pow_succ_r'.
      destruct a; simpl; lia.
  Qed.

  Lemma split_xleyltz x y z : x <=y -> y < z -> x <= y < z.
    lia.
  Qed.

  Lemma bv2z_bounded x : 0 <= bv2z x < modulus.
  Proof.
    unfold bv2z, bvec_denote, modulus.
    destruct x as [xs hlenx]. simpl.
    replace (2 ^ (Z.of_nat SIZE)) with (Z.of_nat (2 ^ SIZE)).
    apply split_xleyltz; try lia.
    apply inj_lt. rewrite <- hlenx.
    apply bitlist_denote_bounded.
    rewrite Nat2Z.inj_pow. auto.
  Qed.
End Z_to_bvec.

(* Tests *)
Goal (z2bl 4 2) = [ zero ; one ; zero ; zero ]. auto. Qed.
