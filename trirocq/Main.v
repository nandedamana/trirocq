(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Import trirocq.AddSub.
Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.Tnum.

From Stdlib Require Import Lia.

Module tmir. (* tnum_mul_iter_result *)
  Inductive t {n} := cons (a b acc : tnum.t (S n)).

  Definition a {n} (r : @tmir.t n) :=
    match r with cons a _ _ => a end.

  Definition b {n} (r : @tmir.t n) :=
    match r with cons _ b _ => b end.

  Definition acc {n} (r : @tmir.t n) :=
    match r with cons _ _ acc => acc end.
End tmir.

Section linux_tnum_multiplication.
  (* To make another proof cleaner *)
  Lemma tnum_union_sound_l {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset P U.
  Proof.
    intros wfP wfQ.
    pose (H := tnum_union_sound P Q wfP wfQ).
    simpl in H. simpl. destruct H as (h1 & h2 & h3). auto.
  Qed.

  Lemma tnum_union_sound_r {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset Q U.
  Proof.
    intros wfP wfQ.
    pose (H := tnum_union_sound P Q wfP wfQ).
    simpl in H. simpl. destruct H as (h1 & h2 & h3). auto.
  Qed.

  (* Using a and b instead of P and Q to make comparison with the in-kernel code easier. *)
  Definition tnum_mul_iter {n} (input : @tmir.t n) :=
    let a := tmir.a input in let b := tmir.b input in let acc := tmir.acc input in
    let nxt_acc := match bvec_lsb (tnum.v a) with
                   | one => tnum_add acc b
                   | zero => match bvec_lsb (tnum.m a) with
                             | one => tnum_union acc (tnum_add acc b)
                             | zero => acc
                             end
                    end in
    let nxt_a := tnum_rshift1 a in
    let nxt_b := tnum_lshift1 b in
    tmir.cons nxt_a nxt_b nxt_acc.

  Lemma tnum_mul_iter_wellformed_nxt_acc {n} (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    let tout := tmir.acc (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfP wfQ wfA.

    unfold tnum_mul_iter.
    unfold tmir.acc. unfold tmir.a. unfold tmir.b.

    destruct (bvec_lsb (tnum.v P)).
    - destruct (bvec_lsb (tnum.m P)). auto.
      apply tnum_union_wellformed; auto. apply tnum_add_wellformed. auto.
    - apply tnum_add_wellformed. auto.
  Qed.

  Lemma tnum_mul_iter_wellformed_nxt_a {n} (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    let touta := tmir.a (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed touta.
  Proof.
    intros. apply tnum_rshift1_wellformed. auto.
  Qed.

  Lemma tnum_mul_iter_wellformed_nxt_b {n} (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    let toutb := tmir.b (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed toutb.
  Proof.
    intros. apply tnum_lshift1_wellformed. auto.
  Qed.

  Lemma tnum_mul_iter_sound_nxt_a {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.a (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.a (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed_nxt_a P Q A).
    intros wfP wfQ wfA igx igy iga.
    split. auto. (* Well-formedness *)

    (* Now soundness *)
    (* Several unfolds used while proving were removed as part of cleanup. *)

    apply tnum_rshift1_sound; auto.
  Qed.

  Lemma tnum_mul_iter_sound_nxt_b {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.b (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.b (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed_nxt_b P Q A).
    intros wfP wfQ wfA igx igy iga.
    split. auto. (* Well-formedness *)

    (* Now soundness *)
    apply tnum_lshift1_sound; auto.
  Qed.

  (* Stated informally, this lemma shows that tnum_mul_iter abstracts
   * bvec_mul_iter. It doesn't assume any relationship between the incoming
   * (P, Q) and A (i.e., A is a partial product of P and Q); but that's okay.
   *)
  Lemma tnum_mul_iter_sound_nxt_acc {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.acc (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.acc (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed_nxt_acc P Q A).
    revert hwf.

    unfold tnum.wellformed. unfold ingamma. unfold tnum.ith_m. unfold tnum.ith_v.
    intros hwf wfP wfQ wfA igx igy iga.

    split. auto. (* Well-formedness *)

    (* Now soundness *)

    unfold tnum_mul_iter.
    unfold tmir.acc. unfold tmir.a. unfold tmir.b.
    unfold bvec_mul_iter.
    unfold bmir.acc. unfold bmir.a. unfold bmir.b.
    unfold bvec_lsb.

    specialize (igx _ (PeanoNat.Nat.lt_0_succ n)).
    specialize (wfP _ (PeanoNat.Nat.lt_0_succ n)).

    destruct (bvec_ith (tnum.m P) (PeanoNat.Nat.lt_0_succ n)).
    + rewrite igx; auto.
      destruct (bvec_ith (tnum.v P) (PeanoNat.Nat.lt_0_succ n)). auto.
      apply tnum_add_sound; auto.
    + rewrite wfP; auto.
      destruct (bvec_ith x (PeanoNat.Nat.lt_0_succ n)); auto.
      (* Direct application of tnum_union_sound results in absurd goals,
       * solving which would result in unnecessary assert, pose, etc.
       *)
      apply tnum_union_sound_l; auto. apply tnum_add_wellformed; auto.
      apply tnum_union_sound_r; auto. apply tnum_add_wellformed; auto.
      apply tnum_add_sound; auto.
  Qed.

  Lemma tnum_mul_iter_sound_all {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let ra := bmir.a (bvec_mul_iter (bmir.cons x y a)) in
    let Ra := tmir.a (tnum_mul_iter (tmir.cons P Q A)) in
    let rb := bmir.b (bvec_mul_iter (bmir.cons x y a)) in
    let Rb := tmir.b (tnum_mul_iter (tmir.cons P Q A)) in
    let rc := bmir.acc (bvec_mul_iter (bmir.cons x y a)) in
    let Rc := tmir.acc (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed Ra /\ tnum.wellformed Rb /\ tnum.wellformed Rc /\
    ingamma ra Ra /\ ingamma rb Rb /\ ingamma rc Rc.
  Proof.
    intros wfP wfQ wfA igx igy iga.
    pose (h1 := tnum_mul_iter_sound_nxt_a x y a P Q A).
    pose (h2 := tnum_mul_iter_sound_nxt_b x y a P Q A).
    pose (h3 := tnum_mul_iter_sound_nxt_acc x y a P Q A).
    split. apply h1; auto.
    split. apply h2; auto.
    split. apply h3; auto.
    split. apply h1; auto.
    split. apply h2; auto.
    apply h3; auto.
  Qed.

  Definition tnum_mul {n} (a b : tnum.t (S n)) :=
    tmir.acc (Nat.iter (S n) tnum_mul_iter (tmir.cons a b (zerotnum (S n)))).

  Lemma tnum_mul_loop_wellformed_all {n} (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall c,
      let R := Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n))) in
      tnum.wellformed (tmir.a R) /\ tnum.wellformed (tmir.b R) /\
        tnum.wellformed (tmir.acc R).
  Proof.
    intros wfP wfQ.

    induction c.
    - split; [|split]; simpl; auto.
      apply zerotnum_wellformed.
    - unfold Nat.iter. unfold nat_rect.
      split. apply tnum_mul_iter_wellformed_nxt_a; apply IHc.
      split. apply tnum_mul_iter_wellformed_nxt_b; apply IHc.
      apply tnum_mul_iter_wellformed_nxt_acc; apply IHc.
  Qed.

  (* This intermediate lemma is needed because in tnum_mul_sound, both
   * the width and the iter count are (S n). I want to induct on the iter
   * count, but that would cause an induction on the width as well. But
   * the width isn't meant to change between iterations. This is a general
   * lemma that disconnects the width and the iter count.
   *)
  Lemma tnum_mul_loop_sound_all {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    forall c,
      let ra := bmir.a (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let Ra := tmir.a (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      let rb := bmir.b (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let Rb := tmir.b (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      let rc := bmir.acc (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let Rc := tmir.acc (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      (* tnum.wellformed R /\ (* TODO *) *)
      ingamma ra Ra /\ ingamma rb Rb /\ ingamma rc Rc.
  Proof.
    unfold tnum.wellformed. unfold ingamma. unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfP wfQ igx igy.

    induction c.
    - simpl. auto.
    -
      pose(wfall := tnum_mul_loop_wellformed_all P Q).
      unfold Nat.iter. unfold nat_rect.
      unfold Nat.iter in wfall. unfold nat_rect in wfall.

      apply tnum_mul_iter_sound_all.
      apply wfall; auto. apply wfall; auto. apply wfall; auto.

      revert IHc. unfold Nat.iter. unfold nat_rect. intro IHc.
      + unfold ingamma. apply IHc.
      + unfold ingamma. apply IHc.
      + unfold ingamma. apply IHc.
  Qed.

  Lemma tnum_mul_sound {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    let R := tnum_mul P Q in let r := bvec_mul x y in
    tnum.wellformed R /\ ingamma r R.
  Proof.
    split.
    - unfold tnum_mul. intros. apply tnum_mul_loop_wellformed_all; auto.
    - apply tnum_mul_loop_sound_all; auto. (* Soundness *)
  Qed.
End linux_tnum_multiplication.
