Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.SigVector.
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

Section bvec_mul.
  (* A version in which a is unpadded after rshift.
   * This makes defining it easier in Rocq, because at least one
   * parameter (the size of the vector a) is decreasing.
   *)
  Fixpoint bvec_mul_shrinkinga m (a : bvec m) :=
    match m return bvec m -> forall n, bvec (S n) -> bvec (S n) -> bvec (S n) with
    | 0 => fun (a : bvec 0) n (b acc : bvec (S n)) => acc
    | S mp => fun (a : bvec (S mp)) n (b acc : bvec (S n)) =>
        match (bvec_denote a) return (bvec (S n)) with
        | 0 => acc
        | _ =>
            let nxta := Vector.tl a in
            let nxtb := bvec_lshift1 b in
            match (bvec_lsb a) with
            | zero => bvec_mul_shrinkinga _ nxta _ nxtb acc
            | one => bvec_mul_shrinkinga _ nxta _ nxtb (bvec_add acc b)
            end
        end
    end a.

  Lemma bvec_denote_to_bitlist_denote xs n (hlenx : length xs = n) :
    bvec_denote (exist (fun x : list bit => length x = n) xs hlenx) =
      bitlist_denote xs.
  Proof.
    unfold bvec_denote. auto.
  Qed.

  (* Proves bitlist_denote (b :: zs) = bitlist_denote (b :: ListDef.firstn n zs) if (length zs) is n *)
  Ltac crush_firstn_all :=
    match goal with
    | [ hlenx : length ?xs = ?n |- context[ListDef.firstn ?n ?xs] ] =>
        rewrite <- hlenx;
        rewrite List.firstn_all; try reflexivity
    | [ hlenx : length (List.cons _ ?xs) = S ?n |- context[ListDef.firstn ?n ?xs] ] =>
        let H := fresh "H" in
        assert (H : length xs = n); auto;
        rewrite <- H;
        rewrite List.firstn_all; try reflexivity
    end.

  Lemma bvec_mul_shrinkinga_correct : forall m (a : bvec m) n (b acc : bvec (S n)),
    bvec_denote (bvec_mul_shrinkinga m a n b acc) =
      Nat.modulo (bvec_denote acc + bvec_denote a * bvec_denote b) (Nat.pow 2 (S n)).
  Proof.
    induction m.
    -
      destruct a as [xs hlenx]. destruct b as [ys hleny].
      destruct acc as [zs hlenz].
      repeat rewrite bvec_denote_to_bitlist_denote.

      rewrite <- bitlist_mul_correct.
      rewrite <- bitlist_mul_trunc_correct.

      unfold bvec_mul_shrinkinga.
      unfold bitlist_mul_trunc.
      destruct xs; try easy.
      repeat rewrite bvec_denote_to_bitlist_denote.
      crush_firstn_all.
    -
      destruct a as [xs hlenx]. destruct b as [ys hleny].
      destruct acc as [zs hlenz].
      repeat rewrite bvec_denote_to_bitlist_denote.

      rewrite <- bitlist_mul_correct.
      rewrite <- bitlist_mul_trunc_correct.

      unfold bvec_mul_shrinkinga. fold bvec_mul_shrinkinga.
      unfold bitlist_mul_trunc.
      repeat rewrite bvec_denote_to_bitlist_denote.
      destruct xs as [|hx tx].
      + simpl.
        rewrite bvec_denote_to_bitlist_denote.
        destruct zs. reflexivity. crush_firstn_all.
      + destruct (bitlist_denote (List.cons hx _)).
        rewrite bvec_denote_to_bitlist_denote.
        destruct zs. reflexivity. crush_firstn_all.

        unfold bvec_lsb. unfold bvec_ith.
        unfold Vector.nth_order. simpl.
        destruct hx.
        *
          fold bitlist_mul_trunc.
          rewrite IHm.
          repeat rewrite bvec_denote_to_bitlist_denote.
          rewrite bitlist_mul_trunc_correct.
          rewrite bitlist_mul_correct.
          destruct zs. auto.
          assert (h1 : ListDef.firstn n zs = zs). crush_firstn_all.
          rewrite h1.

          unfold bvec_lshift1. unfold bvec_denote. simpl.
          reflexivity.
        * fold bitlist_mul_trunc.
          rewrite IHm.
          repeat rewrite bvec_denote_to_bitlist_denote.
          rewrite bitlist_mul_trunc_correct.
          rewrite bitlist_mul_correct.

          unfold bitlist_sum_nocarry.
          unfold bvec_lshift1. unfold bvec_denote. simpl.

          destruct (bitlist_sum _ _).
          rewrite List.firstn_nil. reflexivity.
          rewrite hlenz. rewrite List.firstn_cons. reflexivity.
  Qed.
End bvec_mul.
