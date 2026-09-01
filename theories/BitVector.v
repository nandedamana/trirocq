Require Import trirocq.Bit.
Require Import trirocq.SigVector.

From Stdlib Require Import Lia ZArith.

Definition bvec SIZE := Vector.t bit SIZE.

Definition bvec_ith {n} (v : bvec n) {i} (hi : i < n) := Vector.nth_order v hi.
Definition bvec_ith_error {n} (v : bvec n) {i} := Vector.nth_error v i.

Section bvec_bitwise.
  Definition bvec_and {SIZE} (x y : bvec SIZE) := Vector.map2 bit_and x y.
  Definition bvec_or  {SIZE} (x y : bvec SIZE) := Vector.map2 bit_or x y.
  Definition bvec_xor {SIZE} (x y : bvec SIZE) := Vector.map2 bit_xor x y.
  Definition bvec_neg {SIZE} (x   : bvec SIZE) := Vector.map bit_not x.

  Lemma bvec_and_rel : forall {SIZE} v1 v2 {i} (hidx : i < SIZE),
      bvec_ith (bvec_and v1 v2) hidx = bit_and (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof. intros. apply Vector.nth_map2; auto. Qed.

  Lemma bvec_neg_rel : forall {SIZE} v1 {i} (hidx : i < SIZE),
      bvec_ith (bvec_neg v1) hidx = bit_not (bvec_ith v1 hidx).
  Proof. intros. apply Vector.nth_map; auto. Qed.

  Lemma bvec_or_rel : forall {SIZE} v1 v2 {i} (hidx : i < SIZE),
      bvec_ith (bvec_or v1 v2) hidx = bit_or (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof. intros. apply Vector.nth_map2; auto. Qed.

  Lemma bvec_xor_rel : forall {SIZE} v1 v2 {i} (hidx : i < SIZE),
      bvec_ith (bvec_xor v1 v2) hidx = bit_xor (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof. intros. apply Vector.nth_map2; auto. Qed.
End bvec_bitwise.

Lemma bvec_eq_by_ith : forall {SIZE} (x y : bvec SIZE),
    (forall i (hidx : i < SIZE), (bvec_ith x hidx) = (bvec_ith y hidx)) -> x = y.
Proof.
  destruct x as [x lx].
  destruct y as [y ly].
  intro heqi.
  apply SigVector.Vector.eqlist_imp_eqvec.

  simpl.
  apply list_eq_by_ith. subst. auto.

  intros i hix hiy.
  subst. specialize (heqi i hix).

  revert heqi.
  unfold bvec_ith. unfold SigVector.Vector.nth_order.
  simpl.

  match goal with
    [ |- ?x = ?y -> ?x' = ?y' ] => assert (hx : x = x')
  end.
  match goal with
    [ |- SigVector.safe_nth ?x ?hi = SigVector.safe_nth ?x ?hi' ] =>
      rewrite (SigVector.safe_nth_eq x hi hi')
  end.
  reflexivity.

  match goal with
    [ |- ?x = ?y -> ?x' = ?y' ] => assert (hy : y = y')
  end.
  match goal with
    [ |- SigVector.safe_nth ?x ?hi = SigVector.safe_nth ?x ?hi' ] =>
      rewrite (SigVector.safe_nth_eq x hi hi')
  end.
  reflexivity.

  rewrite hx, hy. auto.
Qed.

Section bvec_addition.
  Definition fulladd a b cin :=
    let sum := bit_xor cin (bit_xor a b) in
    let carry := bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin) in
    pair sum carry.

  Fixpoint bitlist_fulladd_paired_unary (xs : list bit) (cin : bit) :=
    match xs with
      | List.cons hx tx =>
          let lsbsumcarry := fulladd hx zero cin in
          let lsbsum := fst lsbsumcarry in
          let lsbcarry := snd lsbsumcarry in
          List.cons (pair lsbsum cin) (bitlist_fulladd_paired_unary tx lsbcarry)
    | List.nil => List.cons (fulladd zero zero cin) nil
    end.

  (* Element i is (sum[i], incarry[i]) *)
  Fixpoint bitlist_fulladd_paired (xs ys : list bit) (cin : bit) :=
    match xs, ys with
    | List.cons hx tx, List.cons hy ty =>
        let lsbsumcarry := fulladd hx hy cin in
        let lsbsum := fst lsbsumcarry in
        let lsbcarry := snd lsbsumcarry in
        List.cons (pair lsbsum cin) (bitlist_fulladd_paired tx ty lsbcarry)
    | List.cons _ _, List.nil =>
        bitlist_fulladd_paired_unary xs cin
    | List.nil, List.cons _ _ =>
        bitlist_fulladd_paired_unary ys cin
    | _, _ =>
        bitlist_fulladd_paired_unary List.nil cin
    end.

  Definition bitlist_sum_internal (xs ys : list bit) cin : list bit :=
    match xs, ys with
    | _, _ => fst (List.split (bitlist_fulladd_paired xs ys cin))
    end.

  Definition bitlist_sum (xs ys : list bit) : list bit :=
    bitlist_sum_internal xs ys zero.

  Definition bitlist_incarry (xs ys : list bit) cin : list bit :=
    snd (List.split (bitlist_fulladd_paired xs ys cin)).

  Definition bitlist_sum_nocarry (xs ys : list bit) : list bit :=
    List.firstn (Nat.max (length xs) (length ys)) (bitlist_sum xs ys).

  Lemma length_bitlist_fulladd_paired n : forall (xs ys : list bit) cin,
      length xs = n -> length ys = n ->
      length (bitlist_fulladd_paired xs ys cin) = S n.
  Proof.
    induction n.
    - destruct xs; destruct ys; try easy.
    - simpl.
      destruct xs; destruct ys; try easy.
      simpl. intro cin.
      intros hlen1 hlen2. rewrite IHn.
      reflexivity. lia. lia.
  Qed.

  Lemma length_bitlist_sum (x y : list bit) :
    length x = length y ->
    length (bitlist_sum x y) = S (Nat.max (length x) (length y)).
  Proof.
    unfold bitlist_sum. unfold bitlist_sum_internal.
    rewrite List.length_fst_split.
    intro hlen. rewrite hlen.
    apply length_bitlist_fulladd_paired; lia.
  Qed.

  Lemma length_bitlist_sum_nocarry n : forall (xs ys : list bit),
      length xs = n -> length ys = n ->
      length (bitlist_sum_nocarry xs ys) = n.
  Proof.
    intros.
    unfold bitlist_sum_nocarry. rewrite List.length_firstn.
    rewrite length_bitlist_sum; lia.
  Qed.

  Lemma bitlist_fulladd_paired_commutative (xs ys : list bit) :
    forall cin, bitlist_fulladd_paired xs ys cin = bitlist_fulladd_paired ys xs cin.
  Proof.
    induction xs in ys |- *.
    - destruct ys. auto.
      intuition.
    - destruct ys. auto.
      simpl. intro cin. rewrite IHxs.
      destruct a, b, cin; auto.
  Qed.

  Lemma bitlist_sum_commutative (xs ys : list bit) :
    bitlist_sum xs ys = bitlist_sum ys xs.
  Proof.
    unfold bitlist_sum. unfold bitlist_sum_internal.
    rewrite bitlist_fulladd_paired_commutative.
    reflexivity.
  Qed.

  Definition bvec_add {n} (x y : bvec n) : bvec n.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    refine (exist _ (bitlist_sum_nocarry xs ys) _).
    apply length_bitlist_sum_nocarry; auto.
  Defined.

  Lemma bvec_add_commutative {SIZE} (x y : bvec SIZE) :
    bvec_add x y = bvec_add y x.
  Proof.
    destruct x as [xs xlen], y as [ys ylen].
    apply SigVector.Vector.eqlist_imp_eqvec.
    simpl. unfold bitlist_sum_nocarry.
    rewrite xlen, ylen.
    assert (heq : bitlist_sum xs ys = bitlist_sum ys xs).
    apply bitlist_sum_commutative.
    rewrite heq. reflexivity.
  Qed.

  Lemma convhi {A} {xs : list A} {n} (hlen : length xs = n) {i} (hi : i < n) :
    i < length xs.
  Proof. lia. Qed.

  Lemma length_bitlist_incarry n : forall (xs ys : list bit) cin,
      length xs = n -> length ys = n -> length (bitlist_incarry xs ys cin) = S n.
  Proof.
    unfold bitlist_incarry. intros.
    rewrite List.length_snd_split.
    apply length_bitlist_fulladd_paired; auto.
  Qed.

  Definition bitlist_ith_incarry {n} (xs ys : list bit) cin
    (hlenx : length xs = n) (hleny : length ys = n) {i} (hidx : i < n) :=
    safe_nth (bitlist_incarry xs ys cin)
      (convhi (length_bitlist_incarry n xs ys cin hlenx hleny) (ltsuc _ _ hidx)).

  (* TODO rename as bvec_ith_incarry *)
  Definition bvec_incarry {SIZE} (x y : bvec SIZE) {i} (hidx : i < SIZE) : bit.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    exact (bitlist_ith_incarry xs ys zero hlenx hleny hidx).
  Defined.

  Lemma bvec_incarry_0 {SIZE} (x y : bvec SIZE) (hidx : 0 < SIZE) :
    bvec_incarry x y hidx = zero.
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_incarry. unfold bitlist_ith_incarry.
    rewrite_safe_nth_anywhere.
    revert hx1. unfold bitlist_incarry.
    rewrite nth_error_snd_split.
    destruct xs; destruct ys; try easy; simpl; congruence.
  Qed.

  Lemma length_cons_imp_predecessor {A} (xs : list A) x m :
    length (x :: xs) = m -> exists n, m = S n /\ length xs = n.
  Proof.
    simpl. destruct m. easy.
    exists m. apply eq_add_S in H.
    split; auto.
  Qed.

  Lemma bitlist_fulladd_Si :
    forall {i} (xs ys : list bit) {SIZE}
           (hlenx : length xs = SIZE) (hleny : length ys = SIZE)
           (hsi : S i < SIZE) ap bp prvpair a b cin0,
      let falist := (bitlist_fulladd_paired xs ys cin0) in
      List.nth_error xs i = Some ap ->
      List.nth_error ys i = Some bp ->
      List.nth_error falist i = Some prvpair ->
      List.nth_error xs (S i) = Some a ->
      List.nth_error ys (S i) = Some b ->
      let cinp := snd prvpair in
      let cin := bit_or (bit_or (bit_and ap bp) (bit_and ap cinp)) (bit_and bp cinp) in
      let sum := fst (fulladd a b cin) in
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
      unfold bitlist_fulladd_paired.
      fold bitlist_fulladd_paired.

      intros SIZE hlenx hleny hsi ap bp prvpair hx hy.

      intros h1 h2 h3 h4 h5. revert h3.
      rewrite List.nth_error_cons. intro h3.
      rewrite List.nth_error_cons.
      pose (h7 := length_cons_imp_predecessor xs b SIZE hlenx). destruct h7 as (pzx & hpzx).
      apply IHi with (SIZE := pzx); try lia; try auto.
      pose (h8 := length_cons_imp_predecessor ys b0 SIZE hleny). destruct h8 as (pzy & hpzy).
      lia.
  Qed.

  Lemma fulladd_has_elems {SIZE} {xs ys : list bit} {i} :
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

  Lemma bitlist_snd_fulladd_Si SIZE (xs ys : list bit) i x0 x2 x3 :
    length xs = SIZE -> length ys = SIZE -> S i < SIZE ->
    List.nth_error xs i = Some x0 ->
    List.nth_error ys i = Some x2 ->
    List.nth_error (snd (List.split (bitlist_fulladd_paired xs ys zero))) i = Some x3 ->
    List.nth_error (snd (List.split (bitlist_fulladd_paired xs ys zero))) (S i) = Some (bit_or (bit_or (bit_and x0 x2) (bit_and x0 x3)) (bit_and x2 x3)).
  Proof.
    intros hlenx hleny hsi hx0 hx2 hx3.
    rewrite nth_error_snd_split.

    assert (heprv : exists prvpair,
               List.nth_error ((bitlist_fulladd_paired xs ys zero)) i =
                 Some prvpair).
    rewrite nth_error_snd_split in hx3.
    destruct (List.nth_error (bitlist_fulladd_paired _ _ _) _);
      try easy; try eauto.
    destruct heprv as (prv & hprv).

    assert (helems := fulladd_has_elems hlenx hleny hsi).
    destruct helems as ((a & ha) & (b & hb)).

    rewrite (bitlist_fulladd_Si xs ys hlenx hleny hsi x0 x2 prv a b);
      auto.

    simpl.
    enough (x3 = snd prv). subst. auto.
    rewrite nth_error_snd_split in hx3.
    rewrite hprv in hx3. congruence.
  Qed.

  (* Originally specialized to take away the convoy pattern, back when
   * I was using Vector.t from Stdlib.
   *)
  Lemma bvec_incarry_Si {SIZE} (x y : bvec SIZE) {i} (hidx : S i < SIZE) :
    bvec_incarry x y hidx = let a := bvec_ith x (ltprv hidx) in
                            let b := bvec_ith y (ltprv hidx) in
                            let cin := bvec_incarry x y (ltprv hidx) in
                            bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin).
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_incarry. unfold bitlist_ith_incarry.
    unfold bvec_ith. unfold Vector.nth_order.
    simpl. repeat rewrite_safe_nth_anywhere.

    apply eqxy2Some. rewrite <- hx1.
    unfold bitlist_incarry. apply (bitlist_snd_fulladd_Si SIZE); auto.
  Qed.

  Lemma split_cons_pair A B (xs : list (prod A B)) x :
    List.split (List.cons x xs) =
      pair (List.cons (fst x) (fst (List.split xs)))
        (List.cons (snd x) (snd (List.split xs))).
  Proof.
    simpl. destruct (List.split xs). intuition.
  Qed.

  (* TODO cin and x3 redundant? *)
  Lemma bitlist_fst_fulladd_Si i : forall (xs ys : list bit) x0 x2 x3 cin SIZE,
      length xs = SIZE -> length ys = SIZE -> i < SIZE ->
      List.nth_error xs i = Some x0 ->
      List.nth_error ys i = Some x2 ->
      List.nth_error (snd (List.split (bitlist_fulladd_paired xs ys cin))) i = Some x3 ->
      List.nth_error (fst (List.split (bitlist_fulladd_paired xs ys cin))) i =
        Some (bit_xor x3 (bit_xor x0 x2)).
  Proof.
    induction i.
    - intros xs ys x0 x2 x3 cin SIZE hlenx hleny hi hx hy.
      simpl.
      destruct xs, ys; try easy.
      unfold bitlist_fulladd_paired. fold bitlist_fulladd_paired.
      rewrite split_cons_pair. simpl in hx, hy. simpl. congruence.
    - intros xs ys x0 x2 x3 cin SIZE hlenx hleny hi hx hy.
      simpl.
      destruct xs, ys; try easy.
      unfold bitlist_fulladd_paired. fold bitlist_fulladd_paired.
      rewrite split_cons_pair. simpl in hx, hy. simpl.

      pose (h7 := length_cons_imp_predecessor xs b SIZE hlenx).
      destruct h7 as (pzx & (hpzx0 & hpzx1)).
      pose (h8 := length_cons_imp_predecessor ys b0 SIZE hleny).
      destruct h8 as (pzy & (hpzy0 & hpzy1)).
      apply IHi with (SIZE := pzx); try auto; lia.
  Qed.

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

  Lemma bvec_fulladd_result : forall {SIZE} x y [i] (hidx : i < SIZE),
      bvec_ith (bvec_add x y) hidx =
        bit_xor (bvec_incarry x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
  Proof.
    destruct i.
    - intros. rewrite bvec_incarry_0.
      destruct x as [xs hlenx]. destruct y as [ys hleny].
      unfold bvec_ith. unfold Vector.nth_order. simpl.
      unfold bitlist_sum_nocarry.
      unfold bitlist_sum. unfold bitlist_sum_internal.
      repeat rewrite_safe_nth_anywhere.
      apply eqxy2Some.
      rewrite <- hx1.

      destruct xs, ys; try easy.
      rewrite nth_error_firstn.

      rewrite nth_error_fst_split. unfold bitlist_fulladd_paired.
      destruct xs; destruct ys; try easy. simpl.
      simpl in hx0. apply eqxy2Some in hx0.
      simpl in hx2. apply eqxy2Some in hx2.
      congruence.
      subst. simpl. auto.
      subst. simpl. auto.
      subst. simpl. auto.
      lia.
      rewrite List.length_fst_split.
      rewrite (length_bitlist_fulladd_paired SIZE); lia.
      lia.
    - intros.
      destruct x as [xs hlenx]. destruct y as [ys hleny].
      unfold bvec_incarry. unfold bitlist_ith_incarry.
      unfold bitlist_incarry.
      unfold bvec_ith. unfold Vector.nth_order. simpl.
      unfold bitlist_sum_nocarry.
      unfold bitlist_sum. unfold bitlist_sum_internal.
      repeat rewrite_safe_nth_anywhere.
      apply eqxy2Some.
      rewrite <- hx1.

      destruct xs, ys; try easy.
      rewrite nth_error_firstn.
      apply (bitlist_fst_fulladd_Si (S i) _ _ x2 x3 x0 zero SIZE); auto.
      rewrite hlenx. lia.
      rewrite List.length_fst_split.
      rewrite (length_bitlist_fulladd_paired SIZE); lia; auto.
      lia.
  Qed.
End bvec_addition.

(* ------------------------------------------------------------------------ *)

(* TODO doc somewhere above: I've checked this and found not of much use:
     https://docs.rocq-prover.org/v8.16/stdlib/Coq.Bool.Bvector.html
 *)

Section bvec_shift.
  (* Remember: head (i = 0) has the LSB *)
  Definition bvec_lshift1 {n} (v : bvec (S n)) : bvec (S n) :=
    Vector.cons _ zero _ (Vector.shiftout v).

  Lemma bvec_lshift1_ith_0 {n} (v : bvec (S n)) (hi : 0 < S n) :
    bvec_ith (bvec_lshift1 v) hi = zero.
  Proof.
    destruct v as [xs hlen].
    destruct n; try easy.
  Qed.

  Lemma bvec_lshift1_ith_S {n} (v : bvec (S n)) {i} (hi : S i < S n) :
    bvec_ith (bvec_lshift1 v) hi = bvec_ith v (ltprv hi).
  Proof.
    destruct v as [xs hlen].
    unfold bvec_lshift1. unfold bvec_ith.
    rewrite Vector.nth_cons.
    rewrite Vector.nth_shiftout.
    apply Vector.nth_order_eq.
  Qed.

  (* Using logical shift since the type used in Linux is u64 *)
  Definition bvec_rshift1 {n} (v : bvec (S n)) : bvec (S n) :=
    Vector.shiftin zero (Vector.tl v).

  Lemma suclt {i} {n} : i < S n -> i <> n -> S i < S n. lia. Qed.

  Lemma bvec_rshift1_ith_ltn {n} (v : bvec (S n)) {i} (hi : i < S n) (hi2 : i <> n) :
    bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).
  Proof.
    destruct v as [xs hlen].
    unfold bvec_rshift1. unfold bvec_ith.
    unfold Vector.nth_order.
    destruct xs.
    - destruct i; easy.
    - rewrite_safe_nth_auto.
      rewrite_eqxy2Some.
      simpl. rewrite List.nth_error_app1. reflexivity.
      assert (hlen2 := List.length_cons xs b). rewrite hlen in hlen2.
      assert (hlen3 : n = length xs). lia.
      assert (hlen4 : i < n). lia. rewrite hlen3 in hlen4. assumption.
  Qed.

  Lemma nth_shiftin_last {A} (a : A) {n} (v : Vector.t A n) (hi : n < S n):
    Vector.nth_order (Vector.shiftin a v) hi = a.
  Proof.
    destruct v as [xs hlen].
    unfold Vector.nth_order. rewrite_safe_nth_anywhere.
    revert hx1. simpl. rewrite List.nth_error_app2.
    rewrite hlen. rewrite PeanoNat.Nat.sub_diag. simpl.
    congruence. lia.
  Qed.

  Lemma bvec_rshift1_ith_n {n} (v : bvec (S n)) (hi : n < S n) :
    bvec_ith (bvec_rshift1 v) hi = zero.
  Proof.
    apply nth_shiftin_last.
  Qed.
End bvec_shift.

Section bvec_multiplication_helpers.
  Definition zerovec SIZE : bvec SIZE := Vector.const zero SIZE.

  Lemma zerovec_ith {n} {i} (hidx : i < n) : bvec_ith (zerovec n) hidx = zero.
    apply Vector.const_nth.
  Qed.

  Section Testing.
    Definition onevec SIZE : bvec SIZE := Vector.const one SIZE.

    Lemma lt_0_8 : 0 < 8. lia. Qed.
    Lemma lt_1_8 : 1 < 8. lia. Qed.
    Lemma lt_6_8 : 6 < 8. lia. Qed.
    Lemma lt_7_8 : 7 < 8. lia. Qed.

    Example vlsh := (bvec_lshift1 (onevec 8)).
    Lemma lshift_probably_correct :
      (bvec_ith vlsh lt_0_8) = zero /\
        (bvec_ith vlsh lt_1_8) = one /\
        (bvec_ith vlsh lt_6_8) = one /\
        (bvec_ith vlsh lt_7_8) = one.
    Proof.
      split. apply bvec_lshift1_ith_0.
      split. apply bvec_lshift1_ith_S.
      split. unfold vlsh. rewrite bvec_lshift1_ith_S. auto.
      unfold vlsh. rewrite bvec_lshift1_ith_S. auto.
    Qed.

    Example vrsh := (bvec_rshift1 (onevec 8)).
    Lemma rshift_probably_correct :
      (bvec_ith vrsh lt_0_8) = one /\
        (bvec_ith vrsh lt_1_8) = one /\
        (bvec_ith vrsh lt_6_8) = one /\
        (bvec_ith vrsh lt_7_8) = zero.
    Proof.
      split. unfold vrsh. assert (hi2 : 0 <> 7). lia.
      rewrite bvec_rshift1_ith_ltn with (hi2 := hi2). auto.

      split. unfold vrsh. assert (hi2 : 1 <> 7). lia.
      rewrite bvec_rshift1_ith_ltn with (hi2 := hi2). auto.

      split. unfold vrsh. assert (hi2 : 6 <> 7). lia.
      rewrite bvec_rshift1_ith_ltn with (hi2 := hi2). auto.

      unfold vrsh. rewrite bvec_rshift1_ith_n. reflexivity.
    Qed.
  End Testing.

  Definition bvec_lsb {n} (x : bvec (S n)) := bvec_ith x (PeanoNat.Nat.lt_0_succ n).
End bvec_multiplication_helpers.

Ltac unwrap_bvec_ops := match goal with
                          _ => repeat rewrite bvec_and_rel;
                               repeat rewrite bvec_neg_rel;
                               repeat rewrite bvec_or_rel;
                               repeat rewrite bvec_xor_rel
                        end.

Section bvec_denote.
  Definition bit2nat b := match b with
                          | zero => 0
                          | one => 1
                          end.

  Fixpoint bitlist_denote (xs : list bit) : nat :=
    match xs with
    | List.nil => 0
    | List.cons h t => bit2nat h + Nat.double (bitlist_denote t)
    end.

  Definition bvec_denote {n} (v : bvec n) :=
    bitlist_denote (Vector.projlist v).

  Example v10 : bvec 4 := Vector.cons _ zero _
                            (Vector.cons _ one _
                               (Vector.cons _ zero _
                                  (Vector.cons _ one _
                                     (Vector.nil _)))).
  Example bvec_test_10 : bvec_denote v10 = 10. auto. Qed.

  Lemma bitlist_denote_bounded xs : bitlist_denote xs < 2 ^ length xs.
  Proof.
    induction xs.
    - auto.
    - rewrite List.length_cons.
      unfold bitlist_denote. fold bitlist_denote.
      rewrite Nat.pow_succ_r'.
      destruct a; simpl; lia.
  Qed.

  Lemma bvec_denote_bounded {SIZE} (x : bvec SIZE) : bvec_denote x < 2 ^ SIZE.
  Proof.
    destruct x as [xs lenxs].
    unfold bvec_denote. simpl.
    subst. apply bitlist_denote_bounded.
  Qed.
End bvec_denote.

Section bvec_lshift1_correct.
  Definition bvec_lshift1_notrunc {n} (v : bvec n) : bvec (S n) :=
    Vector.cons _ zero _ v.

  (* denoted(shifted v) = shifted(denoted v) mod 2^SIZE *)
  Lemma bitlist_lshift1_notrunc_correct xs :
    bitlist_denote (List.cons zero xs) =
      Nat.shiftl (bitlist_denote xs) 1.
  Proof.
    auto.
  Qed.

  (* denoted(shifted v) = shifted(denoted v) mod 2^SIZE *)
  Lemma bvec_lshift1_notrunc_correct {n} : forall (v : bvec (S n)),
      bvec_denote (bvec_lshift1_notrunc v) = Nat.shiftl (bvec_denote v) 1.
  Proof.
    destruct v as [xs hlen].
    apply bitlist_lshift1_notrunc_correct.
  Qed.

  (* TODO instead, consider redefining lshift1 (first cons and then tl),
   * which would make this rewriting unnecessary.
   *)
  Lemma bvec_lshift1_reorder {n} (v : bvec (S n)) :
    Vector.cons bit zero n (Vector.shiftout v) =
      Vector.shiftout (Vector.cons bit zero (S n) v).
  Proof.
    destruct v as [xs hlen].
    apply Vector.eqlist_imp_eqvec. simpl. reflexivity.
  Qed.

  Lemma bitlist_double_denote (xs : list bit) :
    Nat.double (bitlist_denote xs) =
      bitlist_denote (List.cons zero xs).
  Proof. simpl. reflexivity. Qed.

  Lemma Nat_ones_to_bitlist {n} :
    PeanoNat.Nat.ones n = bitlist_denote (List.repeat one n).
  Proof.
    induction n.
    - auto.
    - simpl. rewrite <- IHn.
      rewrite PeanoNat.Nat.ones_succ. lia.
  Qed.

  Lemma x_plus_x_eq_twice_x x : x + x = 2 * x. lia. Qed.
  Lemma x_plus_1_eq_Sx x : x + 1 = S x. lia. Qed.

  Lemma Nat_land_cons_cons a xs b ys :
    Nat.land (bitlist_denote (a :: xs)) (bitlist_denote (b :: ys)) =
      bit2nat (bit_and a b) + Nat.double (Nat.land (bitlist_denote xs) (bitlist_denote ys)).
  Proof.
    simpl.
    repeat rewrite PeanoNat.Nat.double_twice.
    destruct a; simpl; destruct b; simpl; repeat rewrite PeanoNat.Nat.add_0_r; repeat rewrite x_plus_x_eq_twice_x.
    - rewrite PeanoNat.Nat.land_even_even. reflexivity.
    - replace (S (2 * bitlist_denote ys)) with ((2 * bitlist_denote ys) + 1).
      rewrite PeanoNat.Nat.land_even_odd. reflexivity.
      apply x_plus_1_eq_Sx.
    - replace (S (2 * bitlist_denote xs)) with ((2 * bitlist_denote xs) + 1).
      rewrite PeanoNat.Nat.land_odd_even. reflexivity.
      apply x_plus_1_eq_Sx.
    - replace (S (2 * bitlist_denote xs)) with ((2 * bitlist_denote xs) + 1).
      replace (S (2 * bitlist_denote ys)) with ((2 * bitlist_denote ys) + 1).
      rewrite PeanoNat.Nat.land_odd_odd. simpl. rewrite x_plus_1_eq_Sx. auto.
      apply x_plus_1_eq_Sx. apply x_plus_1_eq_Sx.
  Qed.

  Lemma Nat_land_xs_ys xs : forall ys,
      Nat.land (bitlist_denote xs) (bitlist_denote ys) =
        bitlist_denote (map2_list bit_and xs ys).
  Proof.
    induction xs.
    - destruct ys; auto.
    - destruct ys. apply PeanoNat.Nat.land_0_r.
      rewrite Nat_land_cons_cons. rewrite IHxs. auto.
  Qed.

  Lemma and_ones_to_firstn xs :
    forall n, map2_list bit_and xs (List.repeat one n) = List.firstn n xs.
  Proof.
    induction xs.
    - destruct n; easy.
    - destruct n.
      + simpl. auto.
      + simpl. rewrite IHxs.
        destruct a; reflexivity.
  Qed.

  Lemma Nat_land_ones_to_firstn {n} (xs : list bit) :
    Nat.land (bitlist_denote xs) (PeanoNat.Nat.ones n) =
      bitlist_denote (List.firstn n xs).
  Proof.
    rewrite Nat_ones_to_bitlist. rewrite Nat_land_xs_ys.
    rewrite and_ones_to_firstn. reflexivity.
  Qed.

  Lemma Nat_land_double_xs_ones {n} (xs : list bit) :
    Nat.land (Nat.double (bitlist_denote xs)) (PeanoNat.Nat.ones (S n)) =
      Nat.double (bitlist_denote (List.firstn n xs)).
  Proof.
    repeat rewrite bitlist_double_denote.
    rewrite Nat_land_ones_to_firstn.
    rewrite List.firstn_cons. reflexivity.
  Qed.

  Lemma bvec_lshift1_correct_trunc2notrunc {n} : forall (v : bvec (S n)),
      bvec_denote (bvec_lshift1 v) =
        Nat.modulo (bvec_denote (bvec_lshift1_notrunc v)) (Nat.pow 2 (S n)).
  Proof.
    intro v.
    rewrite <- PeanoNat.Nat.land_ones.
    unfold bvec_lshift1. unfold bvec_lshift1_notrunc.
    rewrite bvec_lshift1_reorder.

    destruct v as [xs hlen].
    unfold bvec_denote. simpl.
    rewrite Nat_land_double_xs_ones.
    reflexivity.
  Qed.

  (* denoted(shifted v) = shifted(denoted v) mod 2^SIZE *)
  Lemma bvec_lshift1_correct {n} (v : bvec (S n)) :
    bvec_denote (bvec_lshift1 v) =
      Nat.modulo (Nat.shiftl (bvec_denote v) 1) (Nat.pow 2 (S n)).
  Proof.
    rewrite bvec_lshift1_correct_trunc2notrunc.
    simpl. rewrite bvec_lshift1_notrunc_correct. auto.
  Qed.
End bvec_lshift1_correct.

Section bvec_rshift1_correct.
  Lemma div2_double n : Nat.div2 (Nat.double n) = n.
    rewrite PeanoNat.Nat.double_twice.
    rewrite PeanoNat.Nat.div2_double.
    reflexivity.
  Qed.

  Lemma bitlist_denote_msb_zero xs :
    bitlist_denote (xs ++ zero :: nil) = bitlist_denote xs.
  Proof.
    induction xs.
    - auto.
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma bvec_rshift1_correct_listify xs a :
    bitlist_denote (xs ++ zero :: nil) =
      Nat.div2 (bit2nat a + Nat.double (bitlist_denote xs)).
  Proof.
    destruct a; simpl; rewrite bitlist_denote_msb_zero.
    - rewrite div2_double. reflexivity.
    - destruct (bitlist_denote xs). simpl. reflexivity.
      simpl. apply eq_S.
      replace (n + S n) with (2 * n + 1).
      rewrite PeanoNat.Nat.div2_odd'. reflexivity.
      lia.
  Qed.

  Lemma bvec_rshift1_correct {n} : forall (v : bvec (S n)),
      bvec_denote (bvec_rshift1 v) = Nat.shiftr (bvec_denote v) 1.
  Proof.
    intro v. destruct v as [xs hlen].
    unfold Nat.shiftr.
    induction xs.
    - easy.
    - apply bvec_rshift1_correct_listify.
  Qed.
End bvec_rshift1_correct.

Section bvec_add_correct.
  Lemma fst_split_cons : forall A B x (xs : list (prod A B)),
      fst (List.split (List.cons x xs)) =
        List.cons (fst x) (fst (List.split xs)).
  Proof.
    intros.
    destruct xs.
    - destruct x; simpl. auto.
    - destruct x; simpl.
      destruct (List.split _). destruct p.
      simpl. auto.
  Qed.

  Lemma bitlist_fulladd_paired_unary_correct : forall xs cin,
      bitlist_denote (fst (List.split (bitlist_fulladd_paired_unary xs cin))) =
        bitlist_denote xs + bit2nat cin.
  Proof.
    induction xs.
    - destruct cin; auto.
    - unfold bitlist_fulladd_paired_unary.
      fold bitlist_fulladd_paired_unary.
      intro. rewrite fst_split_cons.
      unfold bitlist_denote. fold bitlist_denote.
      rewrite IHxs.

      destruct a, cin; simpl; lia.
  Qed.

  Lemma bitlist_sum_internal_correct : forall (xs ys : list bit) cin,
      bitlist_denote (bitlist_sum_internal xs ys cin) =
        plus (plus (bitlist_denote xs) (bitlist_denote ys)) (bit2nat cin).
  Proof.
    induction xs.
    - destruct ys, cin; try easy; auto;
      try unfold bitlist_sum_internal, bitlist_fulladd_paired;
      try rewrite bitlist_fulladd_paired_unary_correct;
      auto.
    - destruct ys; try easy.

      + intro cin.
        unfold bitlist_sum_internal, bitlist_fulladd_paired.
        rewrite bitlist_fulladd_paired_unary_correct;
          auto.
      +
        revert IHxs. unfold bitlist_sum, bitlist_sum_internal. intro IHxs.
        unfold bitlist_fulladd_paired.
        intro cin. rewrite fst_split_cons.
        fold bitlist_fulladd_paired. (* Just for clarity *)
        unfold bitlist_denote. fold bitlist_denote.

        rewrite IHxs; auto.

        destruct a, b, cin;
          simplify_bit_ops; simpl; simplify_bit_ops; try lia.
  Qed.

  Lemma bitlist_sum_correct : forall (xs ys : list bit),
      bitlist_denote (bitlist_sum xs ys) =
        plus (bitlist_denote xs) (bitlist_denote ys).
  Proof.
    unfold bitlist_sum.
    intros.
    rewrite bitlist_sum_internal_correct; auto.
  Qed.

  Lemma half_m_plus_2n n m : m = 0 \/ m = 1 ->
                             Nat.div (m + Nat.double n) 2 = n.
  Proof.
    intros [h0 | h1].
    destruct m; try rewrite h0; try rewrite h1; try easy.
    destruct n.
    - auto.
    - rewrite plus_O_n.
      rewrite <- PeanoNat.Nat.div_mul with (b := 2); auto.
      unfold Nat.double. rewrite x_plus_x_eq_twice_x.
      rewrite PeanoNat.Nat.mul_comm. auto.
    - rewrite h1.
      unfold Nat.double. rewrite x_plus_x_eq_twice_x.
      rewrite PeanoNat.Nat.mul_comm.
      rewrite PeanoNat.Nat.div_add; auto.
  Qed.

  Lemma bitlist_denote_firstn xs n :
    bitlist_denote (List.firstn n xs) =
      Nat.modulo (bitlist_denote xs) (Nat.pow 2 n).
  Proof.
    rewrite <- PeanoNat.Nat.land_ones.
    rewrite Nat_land_ones_to_firstn. reflexivity.
  Qed.

  (* Alternative proof that does not use land:
  Lemma bitlist_denote_firstn xs : forall n,
      bitlist_denote (ListDef.firstn n xs) =
        Nat.modulo (bitlist_denote xs) (Nat.pow 2 n).
  Proof.
    induction xs.
    - destruct n; auto. simpl.
      rewrite PeanoNat.Nat.Div0.mod_0_l. auto.
    - destruct n; simpl; auto.
      rewrite IHxs.

      rewrite <- plus_n_O. rewrite x_plus_x_eq_twice_x.
      rewrite PeanoNat.Nat.Div0.mod_mul_r.
      replace (PeanoNat.Nat.modulo
                 (bit2nat a + Nat.double (bitlist_denote xs)) 2)
        with (bit2nat a).
      rewrite half_m_plus_2n. unfold Nat.double. rewrite x_plus_x_eq_twice_x. auto.
      destruct a; auto.

      unfold Nat.double. rewrite x_plus_x_eq_twice_x.
      rewrite PeanoNat.Nat.mul_comm.
      rewrite PeanoNat.Nat.Div0.mod_add.
      destruct a; auto.
  Qed.
   *)

  (* denote(sum x y) = (denote(x) + denote(y)) mod 2^SIZE *)
  Lemma bvec_add_correct {n} (x y : bvec n) :
    bvec_denote (bvec_add x y) =
      Nat.modulo ((bvec_denote x) + (bvec_denote y)) (Nat.pow 2 n).
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_denote. simpl.
    unfold bitlist_sum_nocarry. rewrite bitlist_denote_firstn.
    subst. rewrite hleny. rewrite PeanoNat.Nat.max_id.
    rewrite bitlist_sum_correct; auto.
  Qed.
End bvec_add_correct.

Lemma eqdenote_imp_eqlist : forall (x y : list bit),
    length x = length y ->
    bitlist_denote x = bitlist_denote y ->
    x = y.
Proof.
  intros x y.
  induction x as [|xh] in y |- *.
  - destruct y; easy.
  - destruct y as [|yh]; try easy.
    simpl.
    intro hlen. apply eq_add_S in hlen.
    specialize (IHx y hlen).

    assert (Hem : bitlist_denote x = bitlist_denote y \/ bitlist_denote x <> bitlist_denote y). lia.
    destruct Hem as [Heml | Hemr].
    + destruct xh, yh, (bitlist_denote x), (bitlist_denote y);
        try easy;
        simpl;
        rewrite IHx; try rewrite Heml; try lia; try auto.
    + destruct xh, yh, (bitlist_denote x), (bitlist_denote y);
        try easy; simpl; try lia.
Qed.

Lemma eqdenote_imp_eqvec : forall {SIZE} (x y : bvec SIZE),
    bvec_denote x = bvec_denote y -> x = y.
Proof.
  intros SIZE x y heq.
  apply SigVector.Vector.eqlist_imp_eqvec.
  revert heq.
  unfold bvec_denote. simpl.
  intro eqlist. apply eqdenote_imp_eqlist in eqlist.
  auto.

  destruct x as [x xlen], y as [y ylen]. subst. auto.
Qed.

Section poking.
  Fixpoint list_set_ith A (x : list A) i value :=
    match x, i with
    | nil, _ => nil
    | List.cons h t, 0 => List.cons value t
    | List.cons h t, S n => List.cons h (list_set_ith _ t n value)
    end.

  Lemma length_list_set_ith : forall {A} (x : list A) i value,
      length (list_set_ith _ x i value) = length x.
  Proof.
    induction x.
    - auto.
    - unfold list_set_ith. fold list_set_ith.
      destruct i. auto.
      intro value. simpl. auto.
  Qed.

  Lemma list_ith_set_is_set : forall {A} (x : list A) i value,
      i < length x ->
      List.nth_error (list_set_ith _ x i value) i = Some value.
  Proof.
    induction x.
    - easy.
    - intros i value hidx.
      unfold list_set_ith. fold list_set_ith.
      destruct i. auto.
      rewrite List.nth_error_cons.
      apply IHx.
      simpl in hidx. lia.
  Qed.

  Lemma list_ith_unset_is_id : forall {A} (x : list A) i value j,
      j <> i ->
      List.nth_error (list_set_ith _ x i value) j = List.nth_error x j.
  Proof.
    induction x.
    - easy.
    - intros i value j hj.
      unfold list_set_ith. fold list_set_ith.
      destruct i.
      + destruct j. easy.
        repeat rewrite List.nth_error_cons. auto.
      + destruct j. easy.
        repeat rewrite List.nth_error_cons. auto.
  Qed.

  Definition bitlist_set_ith (x : list bit) i := list_set_ith _ x i one.

  Definition bvec_set_ith {SIZE} (x : bvec SIZE) {i} (setpos : i < SIZE) : bvec SIZE.
    destruct x as [xs hlen].
    exists (bitlist_set_ith xs i).
    subst. apply length_list_set_ith.
  Defined.

  Lemma bvec_ith_set_is_one {SIZE} (x : bvec SIZE) {i} (setpos : i < SIZE) :
    bvec_ith (bvec_set_ith x setpos) setpos = one.
  Proof.
    destruct x as [xs hlen].
    unfold bvec_ith.
    unfold bvec_set_ith.
    unfold bitlist_set_ith.
    unfold SigVector.Vector.nth_order. simpl.
    SigVector.rewrite_safe_nth_anywhere.
    subst.
    pose (H := list_ith_set_is_set xs i one setpos).
    congruence.
  Qed.

  Lemma bvec_ith_unset_is_id {SIZE} (x : bvec SIZE) {i} (hi : i < SIZE) {j} (hj : j < SIZE) :
    j <> i ->
    bvec_ith (bvec_set_ith x hi) hj = bvec_ith x hj.
  Proof.
    destruct x as [xs hlen].
    unfold bvec_ith.
    unfold bvec_set_ith.
    unfold bitlist_set_ith.
    unfold SigVector.Vector.nth_order. simpl.
    repeat SigVector.rewrite_safe_nth_anywhere.
    subst.
    pose (H := list_ith_unset_is_id xs i one).
    intro hj'. specialize (H j hj').
    congruence.
  Qed.
End poking.
