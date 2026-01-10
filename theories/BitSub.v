Require Import trirocq.Bit.
Require Import trirocq.BitVector.
Require Import trirocq.SigVector.
From Stdlib Require Import Lia.

Section bvec_subtraction.
  Definition fullsub a b bin :=
    let diff := bit_xor bin (bit_xor a b) in
    let borrow := bit_or (bit_or (bit_and (bit_not a) b) (bit_and (bit_not a) bin)) (bit_and b bin) in
    pair diff borrow.

  Fixpoint bitlist_fullsub_paired_unary (xs : list bit) (cin : bit) :=
    match xs with
      | List.cons hx tx =>
          let lsbsumcarry := fullsub hx zero cin in
          let lsbsum := fst lsbsumcarry in
          let lsbcarry := snd lsbsumcarry in
          List.cons (pair lsbsum cin) (bitlist_fullsub_paired_unary tx lsbcarry)
    | List.nil => List.cons (fullsub zero zero cin) nil
    end.

  (* Element i is (sum[i], incarry[i]) *)
  Fixpoint bitlist_fullsub_paired (xs ys : list bit) (cin : bit) :=
    match xs, ys with
    | List.cons hx tx, List.cons hy ty =>
        let lsbsumcarry := fullsub hx hy cin in
        let lsbsum := fst lsbsumcarry in
        let lsbcarry := snd lsbsumcarry in
        List.cons (pair lsbsum cin) (bitlist_fullsub_paired tx ty lsbcarry)
    | List.cons _ _, List.nil =>
        bitlist_fullsub_paired_unary xs cin
    | List.nil, List.cons _ _ =>
        bitlist_fullsub_paired_unary ys cin
    | _, _ =>
        bitlist_fullsub_paired_unary List.nil cin
    end.

  Definition bitlist_sub_internal (xs ys : list bit) cin : list bit :=
    match xs, ys with
    | _, _ => fst (List.split (bitlist_fullsub_paired xs ys cin))
    end.

  Definition bitlist_sub (xs ys : list bit) : list bit :=
    bitlist_sub_internal xs ys zero.

  Definition bitlist_inborrow (xs ys : list bit) cin : list bit :=
    snd (List.split (bitlist_fullsub_paired xs ys cin)).

  Definition bitlist_sub_noborrow (xs ys : list bit) : list bit :=
    List.firstn (Nat.max (length xs) (length ys)) (bitlist_sub xs ys).

  Lemma length_bitlist_fullsub_paired n : forall (xs ys : list bit) cin,
      length xs = n -> length ys = n ->
      length (bitlist_fullsub_paired xs ys cin) = S n.
  Proof.
    induction n.
    - destruct xs; destruct ys; try easy.
    - simpl.
      destruct xs; destruct ys; try easy.
      simpl. intro cin.
      intros hlen1 hlen2. rewrite IHn.
      reflexivity. lia. lia.
  Qed.

  Lemma length_bitlist_sub_noborrow n : forall (xs ys : list bit),
      length xs = n -> length ys = n ->
      length (bitlist_sub_noborrow xs ys) = n.
  Proof.
    intros.
    unfold bitlist_sub_noborrow. rewrite List.length_firstn.
    unfold bitlist_sub. unfold bitlist_sub_internal.
    rewrite List.length_fst_split.
    rewrite length_bitlist_fullsub_paired with (n := n); lia.
  Qed.

  Definition bvec_sub {n} (x y : bvec n) : bvec n.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    refine (exist _ (bitlist_sub_noborrow xs ys) _).
    apply length_bitlist_sub_noborrow; auto.
  Defined.

  (* TODO FIXME duplication with another file *)
  Lemma convhi {A} {xs : list A} {n} (hlen : length xs = n) {i} (hi : i < n) :
    i < length xs.
  Proof. lia. Qed.

  Lemma length_bitlist_inborrow n : forall (xs ys : list bit) cin,
      length xs = n -> length ys = n -> length (bitlist_inborrow xs ys cin) = S n.
  Proof.
    unfold bitlist_inborrow. intros.
    rewrite List.length_snd_split.
    apply length_bitlist_fullsub_paired; auto.
  Qed.

  Definition bitlist_ith_inborrow {n} (xs ys : list bit) cin
    (hlenx : length xs = n) (hleny : length ys = n) {i} (hidx : i < n) :=
    safe_nth (bitlist_inborrow xs ys cin)
      (convhi (length_bitlist_inborrow n xs ys cin hlenx hleny) (ltsuc _ _ hidx)).

  (* TODO rename as bvec_ith_inborrow *)
  Definition bvec_inborrow {SIZE} (x y : bvec SIZE) {i} (hidx : i < SIZE) : bit.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    exact (bitlist_ith_inborrow xs ys zero hlenx hleny hidx).
  Defined.

  Lemma bvec_inborrow_0 {SIZE} (x y : bvec SIZE) (hidx : 0 < SIZE) :
    bvec_inborrow x y hidx = zero.
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_inborrow. unfold bitlist_ith_inborrow.
    rewrite_safe_nth_anywhere.
    revert hx1. unfold bitlist_inborrow.
    rewrite nth_error_snd_split.
    destruct xs; destruct ys; try easy; simpl; congruence.
  Qed.

  (* TODO FIXME duplication with another file *)
  Lemma length_cons_imp_predecessor {A} (xs : list A) x m :
    length (x :: xs) = m -> exists n, m = S n /\ length xs = n.
  Proof.
    simpl. destruct m. easy.
    exists m. apply eq_add_S in H.
    split; auto.
  Qed.

  Lemma bitlist_fullsub_Si :
    forall {i} (xs ys : list bit) {SIZE}
           (hlenx : length xs = SIZE) (hleny : length ys = SIZE)
           (hsi : S i < SIZE) ap bp prvpair a b cin0,
      let falist := (bitlist_fullsub_paired xs ys cin0) in
      List.nth_error xs i = Some ap ->
      List.nth_error ys i = Some bp ->
      List.nth_error falist i = Some prvpair ->
      List.nth_error xs (S i) = Some a ->
      List.nth_error ys (S i) = Some b ->
      let cinp := snd prvpair in
      let cin := bit_or (bit_or (bit_and (bit_not ap) bp) (bit_and (bit_not ap) cinp)) (bit_and bp cinp) in
      let sum := fst (fullsub a b cin) in
      List.nth_error falist (S i) = Some (pair sum cin).
  Proof.
    induction i.
    - destruct xs; destruct ys; try easy. simpl.
      destruct xs; destruct ys; try easy. simpl.
      intros until cin0.
      intros h1 h2 h3 h4 h5.
      apply eqxy2Some in h1, h2, h3, h4, h5.
      subst. auto.
    - destruct xs; destruct ys; try easy.
      unfold bitlist_fullsub_paired.
      fold bitlist_fullsub_paired.

      intros SIZE hlenx hleny hsi ap bp prvpair hx hy.

      intros h1 h2 h3 h4 h5. revert h3.
      rewrite List.nth_error_cons. intro h3.
      rewrite List.nth_error_cons.
      pose (h7 := length_cons_imp_predecessor xs b SIZE hlenx). destruct h7 as (pzx & hpzx).
      apply IHi with (SIZE := pzx); try lia; try auto.
      pose (h8 := length_cons_imp_predecessor ys b0 SIZE hleny). destruct h8 as (pzy & hpzy).
      lia.
  Qed.

  (* TODO just move out fulladd_has_elems and reuse it; there is nothing sub-specific here. *)
  Lemma fullsub_has_elems {SIZE} {xs ys : list bit} {i} :
    length xs = SIZE -> length ys = SIZE -> i < SIZE ->
    (exists x, List.nth_error xs i = Some x) /\
      (exists y, List.nth_error ys i = Some y).
  Proof.
    intros hlenx hleny hi.
    split.

    assert (hx : List.nth_error xs i <> None).
    apply List.nth_error_Some; lia.
    destruct (List.nth_error xs i); try easy. eauto.

    assert (hy : List.nth_error ys i <> None).
    apply List.nth_error_Some; lia.
    destruct (List.nth_error ys i); try easy. eauto.
  Qed.

  Lemma bitlist_snd_fullsub_Si SIZE (xs ys : list bit) i x0 x2 x3 :
    length xs = SIZE -> length ys = SIZE -> S i < SIZE ->
    List.nth_error xs i = Some x0 ->
    List.nth_error ys i = Some x2 ->
    List.nth_error (snd (List.split (bitlist_fullsub_paired xs ys zero))) i = Some x3 ->
    List.nth_error (snd (List.split (bitlist_fullsub_paired xs ys zero))) (S i) = Some (bit_or (bit_or (bit_and (bit_not x0) x2) (bit_and (bit_not x0) x3)) (bit_and x2 x3)).
  Proof.
    intros hlenx hleny hsi hx0 hx2 hx3.
    rewrite nth_error_snd_split.

    assert (heprv : exists prvpair,
               List.nth_error ((bitlist_fullsub_paired xs ys zero)) i =
                 Some prvpair).
    rewrite nth_error_snd_split in hx3.
    destruct (List.nth_error (bitlist_fullsub_paired _ _ _) _);
      try easy; try eauto.
    destruct heprv as (prv & hprv).

    assert (helems := fulladd_has_elems hlenx hleny hsi).
    destruct helems as ((a & ha) & (b & hb)).

    rewrite (bitlist_fullsub_Si xs ys hlenx hleny hsi x0 x2 prv a b);
      auto.

    simpl.
    enough (x3 = snd prv). subst. auto.
    rewrite nth_error_snd_split in hx3.
    rewrite hprv in hx3. congruence.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma bvec_inborrow_Si {SIZE} (x y : bvec SIZE) {i} (hidx : S i < SIZE) :
    bvec_inborrow x y hidx = let a := bvec_ith x (ltprv hidx) in
                             let b := bvec_ith y (ltprv hidx) in
                             let cin := bvec_inborrow x y (ltprv hidx) in
                             bit_or (bit_or (bit_and (bit_not a) b) (bit_and (bit_not a) cin)) (bit_and b cin).
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_inborrow. unfold bitlist_ith_inborrow.
    unfold bvec_ith. unfold Vector.nth_order.
    simpl. repeat rewrite_safe_nth_anywhere.

    apply eqxy2Some. rewrite <- hx1.
    unfold bitlist_inborrow. apply (bitlist_snd_fullsub_Si SIZE); auto.
  Qed.

  (* TODO FIXME duplication with another file *)
  Lemma split_cons_pair A B (xs : list (prod A B)) x :
    List.split (List.cons x xs) =
      pair (List.cons (fst x) (fst (List.split xs)))
        (List.cons (snd x) (snd (List.split xs))).
  Proof.
    simpl. destruct (List.split xs). intuition.
  Qed.

  (* TODO cin and x3 redundant? *)
  Lemma bitlist_fst_fullsub_Si i : forall (xs ys : list bit) x0 x2 x3 cin SIZE,
      length xs = SIZE -> length ys = SIZE -> i < SIZE ->
      List.nth_error xs i = Some x0 ->
      List.nth_error ys i = Some x2 ->
      List.nth_error (snd (List.split (bitlist_fullsub_paired xs ys cin))) i = Some x3 ->
      List.nth_error (fst (List.split (bitlist_fullsub_paired xs ys cin))) i =
        Some (bit_xor x3 (bit_xor x0 x2)).
  Proof.
    induction i.
    - intros xs ys x0 x2 x3 cin SIZE hlenx hleny hi hx hy.
      simpl.
      destruct xs, ys; try easy.
      unfold bitlist_fullsub_paired. fold bitlist_fullsub_paired.
      rewrite split_cons_pair. simpl in hx, hy. simpl. congruence.
    - intros xs ys x0 x2 x3 cin SIZE hlenx hleny hi hx hy.
      simpl.
      destruct xs, ys; try easy.
      unfold bitlist_fullsub_paired. fold bitlist_fullsub_paired.
      rewrite split_cons_pair. simpl in hx, hy. simpl.

      pose (h7 := length_cons_imp_predecessor xs b SIZE hlenx).
      destruct h7 as (pzx & (hpzx0 & hpzx1)).
      pose (h8 := length_cons_imp_predecessor ys b0 SIZE hleny).
      destruct h8 as (pzy & (hpzy0 & hpzy1)).
      apply IHi with (SIZE := pzx); try auto; lia.
  Qed.

  (* TODO FIXME duplication with another file *)
  Lemma nth_error_firstn {A} i : forall (xs : list A) n,
      n > 0 -> i < length xs -> i < n ->
      List.nth_error (ListDef.firstn n xs) i = List.nth_error xs i.
  Proof.
    induction i.
    - destruct n; try easy.
      unfold List.nth_error. fold List.nth_error.
      destruct xs.
      unfold ListDef.firstn. fold ListDef.firstn.
      auto. simpl. auto.
    - destruct xs; try easy.
      destruct n; try easy.
      rewrite List.firstn_cons. simpl.
      intros h1 h2 h3.
      apply PeanoNat.lt_S_n in h2, h3.
      apply IHi; auto. lia.
  Qed.

  Lemma bvec_fullsub_result : forall {SIZE} x y [i] (hidx : i < SIZE),
      bvec_ith (bvec_sub x y) hidx =
        bit_xor (bvec_inborrow x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
  Proof.
    destruct i.
    - intros. rewrite bvec_inborrow_0.
      destruct x as [xs hlenx]. destruct y as [ys hleny].
      unfold bvec_ith. unfold Vector.nth_order. simpl.
      unfold bitlist_sub_noborrow.
      unfold bitlist_sub. unfold bitlist_sub_internal.
      repeat rewrite_safe_nth_anywhere.
      apply eqxy2Some.
      rewrite <- hx1.

      destruct xs, ys; try easy.
      rewrite nth_error_firstn.

      rewrite nth_error_fst_split. unfold bitlist_fullsub_paired.
      destruct xs; destruct ys; try easy. simpl.
      simpl in hx0. apply eqxy2Some in hx0.
      simpl in hx2. apply eqxy2Some in hx2.
      congruence.
      subst. simpl. auto.
      subst. simpl. auto.
      subst. simpl. auto.
      lia.
      rewrite List.length_fst_split.
      rewrite (length_bitlist_fullsub_paired SIZE); lia.
      lia.
    - intros.
      destruct x as [xs hlenx]. destruct y as [ys hleny].
      unfold bvec_inborrow. unfold bitlist_ith_inborrow.
      unfold bitlist_inborrow.
      unfold bvec_ith. unfold Vector.nth_order. simpl.
      unfold bitlist_sub_noborrow.
      unfold bitlist_sub. unfold bitlist_sub_internal.
      repeat rewrite_safe_nth_anywhere.
      apply eqxy2Some.
      rewrite <- hx1.

      destruct xs, ys; try easy.
      rewrite nth_error_firstn.
      apply (bitlist_fst_fullsub_Si (S i) _ _ _ _ _ zero SIZE); auto.
      rewrite hlenx. lia.
      rewrite List.length_fst_split.
      rewrite (length_bitlist_fullsub_paired SIZE); lia; auto.
      lia.
  Qed.
End bvec_subtraction.
