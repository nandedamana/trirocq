Require Import trirocq.Bit.
Require Import trirocq.BitVector.
From Stdlib Require Import Lia.

Section bitlist_mul_rec.
  Fixpoint bitlist_mul (a b acc : list bit) :=
    match a with
    | List.nil => acc
    | List.cons h t =>
        match (bitlist_denote a) with
        | 0 => acc
        | _ => match h with
               | zero => bitlist_mul t (List.cons zero b) acc
               | one => bitlist_mul t (List.cons zero b) (bitlist_sum acc b)
               end
        end
    end.

  (* TODO move out *)
  Lemma bitlist_denote_nonempty h t :
    bitlist_denote (List.cons h t) = bit2nat h + Nat.double (bitlist_denote t).
  Proof.
    auto.
  Qed.

  Lemma bitlist_mul_correct : forall a b acc,
      bitlist_denote (bitlist_mul a b acc) =
        bitlist_denote acc + bitlist_denote a * bitlist_denote b.
  Proof.
    induction a as [|ha ta IHa].
    - auto.
    -
      intros.
      unfold bitlist_mul. fold bitlist_mul.
      rewrite bitlist_denote_nonempty.

      rewrite PeanoNat.Nat.mul_add_distr_r.
      rewrite PeanoNat.Nat.add_shuffle3.

      assert (H : forall x y,
                 Nat.double (bitlist_denote x) * bitlist_denote y =
                   bitlist_denote x * bitlist_denote (List.cons zero y)).
      simpl. lia.

      rewrite H.

      destruct ha.
      + simpl.
        destruct (bitlist_denote ta).
        * simpl. auto.
        * simpl. rewrite IHa. simpl. reflexivity.
      + simpl.
        repeat rewrite IHa.
        rewrite bitlist_sum_correct. simpl. lia.
  Qed.
End bitlist_mul_rec.

Section bitlist_mul_trunc.
  Fixpoint bitlist_mul_trunc (a b acc : list bit) n :=
    let truncacc := List.firstn n acc in
    match a with
    | List.nil => truncacc
    | List.cons h t =>
        match (bitlist_denote a) with
        | 0 => truncacc
        | _ => let trunc2b := (List.firstn n (List.cons zero b)) in
               match h with
               | zero => bitlist_mul_trunc t trunc2b truncacc n
               | one => bitlist_mul_trunc t trunc2b (List.firstn n (bitlist_sum acc b)) n
               end
        end
    end.

  Ltac destruct_match_bit :=
    match goal with
    | [ |- context[match ?e with | zero => _ | one => _ end] ] => destruct e
    end.

  Ltac destruct_match_nat :=
    match goal with
    | [ |- context[match ?e with | O => _ | S _ => _ end] ] => destruct e
    end.

  Lemma bitlist_fulladd_binarify_l a cin :
    bitlist_fulladd_paired_unary a cin =
      bitlist_fulladd_paired a List.nil cin.
  Proof.
    destruct a, cin; auto.
  Qed.

  Lemma bitlist_fulladd_binarify_trunc_l a cin n :
    bitlist_fulladd_paired_unary (List.firstn n a) cin =
      bitlist_fulladd_paired (List.firstn n a) (List.firstn n List.nil) cin.
  Proof.
    rewrite List.firstn_nil.
    apply bitlist_fulladd_binarify_l.
  Qed.

  Lemma bitlist_sum_internal_trunc_intrunc_ok : forall n a b cin,
      List.firstn n (bitlist_sum_internal a b cin) =
        List.firstn n (bitlist_sum_internal (List.firstn n a) (List.firstn n b)cin).
  Proof.
    unfold bitlist_sum_internal.
    induction n.
    - auto.
    - destruct a as [|ha ta].
      + destruct b as [|hb tb]; try auto.
        intros.
        unfold bitlist_fulladd_paired, bitlist_fulladd_paired_unary.
        fold bitlist_fulladd_paired_unary.
        rewrite fst_split_cons. simpl.
        rewrite bitlist_fulladd_binarify_trunc_l.
        rewrite bitlist_fulladd_binarify_l.

        rewrite IHn.
        destruct (List.split (bitlist_fulladd_paired _ _ _)).
        auto.
      + destruct b as [|hb tb].
        * intros.
          unfold bitlist_fulladd_paired, bitlist_fulladd_paired_unary.
          fold bitlist_fulladd_paired_unary.
          rewrite fst_split_cons. simpl.
          rewrite bitlist_fulladd_binarify_trunc_l.
          rewrite bitlist_fulladd_binarify_l.

          rewrite IHn.
          destruct (List.split (bitlist_fulladd_paired _ _ _)).
          auto.
        * intros.
          unfold bitlist_fulladd_paired.
          fold bitlist_fulladd_paired.
          rewrite fst_split_cons. simpl.
          rewrite IHn.
          destruct (List.split (bitlist_fulladd_paired _ _ _)).
          auto.
  Qed.

  Lemma bitlist_sum_trunc_intrunc_ok : forall n a b,
      List.firstn n (bitlist_sum a b) =
        List.firstn n (bitlist_sum (List.firstn n a) (List.firstn n b)).
  Proof.
    intros. unfold bitlist_sum.
    rewrite bitlist_sum_internal_trunc_intrunc_ok.
    reflexivity.
  Qed.

  Lemma bitlist_mul_trunc_intrunc_ok : forall a b acc n,
      bitlist_mul_trunc a b acc n =
        bitlist_mul_trunc a (List.firstn n b) (List.firstn n acc) n.
  Proof.
    induction a.
    - intros. simpl.
      rewrite List.firstn_firstn. rewrite PeanoNat.Nat.min_id.
      reflexivity.
    - unfold bitlist_mul, bitlist_mul_trunc.
      fold bitlist_mul. fold bitlist_mul_trunc.
      destruct_match_bit; destruct_match_nat; intros;
      try rewrite List.firstn_firstn, PeanoNat.Nat.min_id; auto.

      rewrite <- List.firstn_cons.
      rewrite List.firstn_firstn.
      replace (Nat.min n0 (S n0)) with n0. reflexivity. lia.

      rewrite <- List.firstn_cons.
      rewrite List.firstn_firstn.
      rewrite bitlist_sum_trunc_intrunc_ok.
      replace (Nat.min n0 (S n0)) with n0. reflexivity. lia.
  Qed.

  Lemma bitlist_mul_trunc_correct : forall a b acc n,
      bitlist_denote (bitlist_mul_trunc a b acc n) =
        Nat.modulo (bitlist_denote (bitlist_mul a b acc)) (Nat.pow 2 n).
  Proof.
    induction a.
    - intros. rewrite <- bitlist_denote_firstn. auto.
    - unfold bitlist_mul, bitlist_mul_trunc.
      fold bitlist_mul. fold bitlist_mul_trunc.
      destruct_match_bit; destruct_match_nat; intros.
      + apply bitlist_denote_firstn.
      + rewrite <- IHa.
        rewrite <- bitlist_mul_trunc_intrunc_ok. reflexivity.
      + apply bitlist_denote_firstn.
      + rewrite <- IHa.
        rewrite <- bitlist_mul_trunc_intrunc_ok. reflexivity.
  Qed.
End bitlist_mul_trunc.
