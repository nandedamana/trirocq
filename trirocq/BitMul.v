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
