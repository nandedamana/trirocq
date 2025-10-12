Require Import trirocq.Bit.
Require Import trirocq.SigVector.

From Stdlib Require Import Lia.

Lemma ltprv {i} {n} : S i < n -> i < n. lia. Qed.

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

Section bvec_addition.
  Definition fulladd a b cin :=
    let sum := bit_xor (bit_xor a b) cin in
    let carry := bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin) in
    pair sum carry.

  Fixpoint bitlist_fulladd_paired (xs ys : list bit) (cin : bit) :=
    match xs, ys with
    | List.cons hx tx, List.cons hy ty =>
        let lsbsumcarry := fulladd hx hy cin in
        let lsbcarry := snd lsbsumcarry in
        List.cons lsbsumcarry (bitlist_fulladd_paired tx ty lsbcarry)
    | _, _ => List.nil
    end.

  Definition bitlist_sum (xs ys : list bit) (cin : bit) : list bit :=
    fst (List.split (bitlist_fulladd_paired xs ys cin)).

  Definition bitlist_carry (xs ys : list bit) (cin : bit) : list bit :=
    snd (List.split (bitlist_fulladd_paired xs ys cin)).

  Definition bitlist_sum_with_carry (xs ys : list bit) (cin : bit) : list bit :=
    List.app
      (bitlist_sum xs ys cin)
      (List.cons (List.last (bitlist_carry xs ys cin) zero) List.nil).

  Lemma length_bitlist_fulladd_paired n : forall (xs ys : list bit) cin,
      length xs = n -> length ys = n ->
      length (bitlist_fulladd_paired xs ys cin) = n.
  Proof.
    induction n.
    - destruct xs; destruct ys; try easy.
    - simpl.
      destruct xs; destruct ys; try easy.
      simpl. intro cin.
      intros hlen1 hlen2. rewrite IHn.
      reflexivity. lia. lia.
  Qed.

  Lemma length_bitlist_sum n : forall (xs ys : list bit) cin,
    length xs = n -> length ys = n -> length (bitlist_sum xs ys cin) = n.
  Proof.
    unfold bitlist_sum. intros.
    rewrite List.length_fst_split.
    apply length_bitlist_fulladd_paired; auto.
  Qed.

  Definition bvec_add {n} (x y : bvec n) : bvec n.
    refine (exist _ (bitlist_sum (Vector.projlist x) (Vector.projlist y) zero) _).
    destruct x as [xs hlenx].
    destruct y as [ys hleny].
    simpl. apply length_bitlist_sum; assumption.
  Defined.

  Lemma convhi {A} {xs : list A} {n} (hlen : length xs = n) {i} (hi : i < n) :
    i < length xs.
  Proof. lia. Qed.

  Lemma length_bitlist_carry n : forall (xs ys : list bit) cin,
    length xs = n -> length ys = n -> length (bitlist_carry xs ys cin) = n.
  Proof.
    unfold bitlist_carry. intros.
    rewrite List.length_snd_split.
    apply length_bitlist_fulladd_paired; auto.
  Qed.

  Definition bitlist_incarry (xs ys : list bit) cin :=
      List.cons cin (bitlist_carry xs ys cin).

  Lemma length_bitlist_incarry n : forall (xs ys : list bit) cin,
    length xs = n -> length ys = n -> length (bitlist_incarry xs ys cin) = S n.
  Proof.
    unfold bitlist_incarry. intros. simpl.
    apply eq_S. apply length_bitlist_carry; auto.
  Qed.

  Definition bitlist_ith_incarry {n} (xs ys : list bit)
    (hlenx : length xs = n) (hleny : length ys = n) {i} (hidx : i < n) :=
    safe_nth (bitlist_incarry xs ys zero)
      (convhi (length_bitlist_incarry n xs ys zero hlenx hleny) (ltsuc _ _ hidx)).

  Lemma fulladd_Si : forall i prvpair (xs ys : list bit) a b cin,
    List.nth_error (bitlist_fulladd_paired xs ys cin) i = Some prvpair ->
    List.nth_error xs (S i) = Some a ->
    List.nth_error ys (S i) = Some b ->
    List.nth_error (bitlist_fulladd_paired xs ys cin) (S i) = Some (fulladd a b (snd prvpair)).
  Proof.
    induction i.
    - intros prvpair xs ys a b cin.
      destruct xs; destruct ys; try easy. simpl.
      unfold bitlist_fulladd_paired.
      destruct xs; destruct ys; simpl; try lia; try easy.
      intros hp ha hb.
      apply eqxy2Some in ha. apply eqxy2Some in hb. apply eqxy2Some in hp.
      subst. simpl. reflexivity.
    - intros prvpair xs ys a b cin.
      destruct xs; destruct ys; try easy.
      apply IHi; auto.
  Qed.

  (* TODO rename as bvec_ith_incarry *)
  Definition bvec_incarry {SIZE} (x y : bvec SIZE) {i} (hidx : i < SIZE) : bit.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    exact (bitlist_ith_incarry xs ys hlenx hleny hidx).
  Defined.

  Lemma bvec_incarry_0 {SIZE} (x y : bvec SIZE) (hidx : 0 < SIZE) :
    bvec_incarry x y hidx = zero.
  Proof.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_incarry. unfold bitlist_ith_incarry.
    rewrite_safe_nth_auto_left.
    destruct xs; destruct ys; try easy.
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
    unfold bvec_incarry. unfold bvec_ith. unfold Vector.nth_order.
    unfold bitlist_ith_incarry.
    repeat rewrite_safe_nth_anywhere.
    apply eqxy2Some.
    rewrite <- hx1.

    unfold bitlist_incarry. simpl.
    unfold bitlist_carry.
    rewrite nth_error_snd_split.

    destruct i.
    - destruct xs; destruct ys; try easy; simpl.
      simpl in hx3. apply eqxy2Some in hx3. rewrite <- hx3.
      destruct b; destruct x0; destruct b0; destruct x2; auto.
    - assert (heprv : exists prvpair,
                 List.nth_error (bitlist_fulladd_paired xs ys zero) i =
                   Some prvpair).
      revert hx3.
      unfold bitlist_incarry. simpl. unfold bitlist_carry.
      rewrite nth_error_snd_split.
      destruct (List.nth_error (bitlist_fulladd_paired xs ys zero) i).
      eauto.
      easy.
      destruct heprv as [prv hprv].

      rewrite (fulladd_Si i prv xs ys x0 x2); try lia; try assumption. simpl.

      revert hx3.
      unfold bitlist_incarry. unfold bitlist_carry. simpl.
      rewrite nth_error_snd_split.
      rewrite hprv. congruence.
  Qed.

  Lemma bvec_fulladd_result : forall {SIZE} x y [i] (hidx : i < SIZE),
      bvec_ith (bvec_add x y) hidx =
        bit_xor (bvec_incarry x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
  Proof.
    intros.
    destruct x as [xs hlenx]. destruct y as [ys hleny].
    unfold bvec_ith. unfold Vector.nth_order. simpl.
    repeat rewrite_safe_nth_anywhere.
    apply eqxy2Some.
    rewrite <- hx1.

    unfold bitlist_sum. unfold bitlist_ith_incarry.
    rewrite nth_error_fst_split.
    unfold bitlist_incarry. unfold bitlist_carry.

    rewrite_safe_nth_anywhere.
    destruct i.
    - simpl.
      destruct xs; destruct ys; simpl in hlenx; simpl in hleny;
        try lia; try easy.
      simpl in hx0. apply eqxy2Some in hx0.
      simpl in hx2. apply eqxy2Some in hx2.
      subst.
      unfold bitlist_fulladd_paired. simpl.
      destruct x0; destruct x2; auto.
    - assert (hprv : exists prvpair,
                 List.nth_error (bitlist_fulladd_paired xs ys zero) i = Some prvpair).
      simpl in hx3. rewrite nth_error_snd_split in hx3.
      destruct (List.nth_error (bitlist_fulladd_paired xs ys zero) i); try easy.
      eauto.

      destruct hprv as (prvpair & hprv).
      rewrite fulladd_Si with (a := x0) (b := x2) (prvpair := prvpair);
        try lia; try auto.
      simpl. rewrite bit_xor_commutative.
      simpl in hx3. rewrite nth_error_snd_split in hx3.
      rewrite hprv in hx3. congruence.
  Qed.
End bvec_addition.

Section bvec_subtraction.
  (* TODO verify these axioms related to subtraction *)

  Axiom bvec_sub : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.

  Fixpoint bvec_inborrow {SIZE} (x y : bvec SIZE) {i} (hidx : i < SIZE) : bit :=
    match i return i < SIZE -> bit with
    | 0 => fun _ => zero
    | S i' => fun hidx => let a := bvec_ith x (ltprv hidx) in
                          let b := bvec_ith y (ltprv hidx) in
                          let bin := bvec_inborrow x y (ltprv hidx) in
                          bit_or (bit_or (bit_and (bit_not a) b) (bit_and (bit_not a) bin)) (bit_and b bin)
    end hidx.

  (* Takes away the convoy pattern, making some upcoming proofs simpler *)
  Lemma bvec_inborrow_Si {SIZE} (x y : bvec SIZE) {i} (hidx : S i < SIZE) :
    bvec_inborrow x y hidx = let a := bvec_ith x (ltprv hidx) in
                             let b := bvec_ith y (ltprv hidx) in
                             let bin := bvec_inborrow x y (ltprv hidx) in
                             bit_or (bit_or (bit_and (bit_not a) b) (bit_and (bit_not a) bin)) (bit_and b bin).
  Proof.
    auto.
  Qed.

  Axiom bvec_fullsub_result : forall {SIZE} x y [i] (hidx : i < SIZE),
      bvec_ith (bvec_sub x y) hidx =
        bit_xor (bvec_inborrow x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
End bvec_subtraction.

(* ------------------------------------------------------------------------ *)

(* TODO doc somewhere above: I've checked this and found not of much use:
     https://docs.rocq-prover.org/v8.16/stdlib/Coq.Bool.Bvector.html
 *)

Module bmir. (* bvec_mul_iter_result *)
  Inductive t {n} := cons (a b acc : bvec (S n)).

  Definition a {n} (r : @bmir.t n) :=
    match r with cons a _ _ => a end.

  Definition b {n} (r : @bmir.t n) :=
    match r with cons _ b _ => b end.

  Definition acc {n} (r : @bmir.t n) :=
    match r with cons _ _ acc => acc end.
End bmir.

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

  (* TODO rem if not used (written in the hope that it'd simplify many other parts *)
  Lemma nth_tl_error {n} (v : bvec (S n)) {i} :
    Vector.nth_error (Vector.tl v) i = Vector.nth_error v (S i).
  Proof.
    destruct v as [xs hlen].
    destruct xs. easy. simpl.
    reflexivity.
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

  (* TODO update the user and remove this *)
  Lemma bvec_rshift1_ith_0 {n} (v : bvec (S n)) (hi : 0 < S n) (hi2 : 0 <> n) :
    bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).
  Proof.
    apply bvec_rshift1_ith_ltn.
  Qed.

  (* TODO rem the third arg after updating the users;
   * synth with (PeanoNat.Nat.lt_succ_diag_r n)
   *)
  Lemma nth_shiftin_last {A} (a : A) {n} (v : Vector.t A n) (hi : n < S n) :
    Vector.nth_order (Vector.shiftin a v) hi = a.
  Proof.
    destruct v as [xs hlen].
    unfold Vector.nth_order.
    assert (n < length (Vector.projlist
                          (Vector.shiftin a (exist (fun x : list A => length x = n) xs hlen)))). simpl. rewrite <- hlen. rewrite List.length_app. simpl. lia.

    rewrite_safe_nth_auto_left. simpl in hx1.
    rewrite List.nth_error_app2 in hx1. rewrite hlen in hx1.
    replace (n - n) with 0 in hx1. rewrite List.nth_error_cons_0 in hx1.
    congruence. lia. lia.
  Qed.

  (* TODO rem the third arg after updating the users *)
  Lemma bvec_rshift1_ith_n {n} (v : bvec (S n)) (hi : n < S n) :
    bvec_ith (bvec_rshift1 v) hi = zero.
  Proof.
    apply nth_shiftin_last.
  Qed.
End bvec_shift.

Section bvec_multiplication.
  Definition zerovec SIZE : bvec SIZE := Vector.const zero SIZE.

  Lemma zerovec_ith {n} {i} (hidx : i < n) : bvec_ith (zerovec n) hidx = zero.
    apply Vector.const_nth.
  Qed.

  Definition bvec_mul_single {SIZE} y (x : bvec SIZE)
    := match y with
       | zero => zerovec SIZE
       | one => x
       end.

  Section Testing.
    Fixpoint onevec SIZE := match SIZE with
                            | 0 => Vector.nil bit
                            | S p => Vector.cons bit one p (onevec p)
                            end.

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
      rewrite bvec_rshift1_ith_0 with (hi2 := hi2). auto.

      split. unfold vrsh. assert (hi2 : 1 <> 7). lia.
      rewrite bvec_rshift1_ith_ltn with (hi2 := hi2). auto.

      split. unfold vrsh. assert (hi2 : 6 <> 7). lia.
      rewrite bvec_rshift1_ith_ltn with (hi2 := hi2). auto.

      unfold vrsh. rewrite bvec_rshift1_ith_n. reflexivity.
    Qed.
  End Testing.

  Definition bvec_lsb {n} (x : bvec (S n)) := bvec_ith x (PeanoNat.Nat.lt_0_succ n).

  Definition bvec_mul_iter {n} (input : @bmir.t n) :=
    let a := bmir.a input in
    let b := bmir.b input in
    let acc := bmir.acc input in
    let nxt_acc := match bvec_lsb a with
                   | one => bvec_add acc b
                   | zero => acc
                   end in
    let nxt_a := bvec_rshift1 a in
    let nxt_b := bvec_lshift1 b in
    bmir.cons nxt_a nxt_b nxt_acc.

  Definition bvec_mul {n} (a b : bvec (S n)) :=
    bmir.acc (Nat.iter (S n) bvec_mul_iter (bmir.cons a b (zerovec (S n)))).
End bvec_multiplication.

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

  Fixpoint bitlist_denote_helper (xs : list bit) : nat :=
    match xs with
    | List.nil => 0
    | List.cons h t => bit2nat h + Nat.double (bitlist_denote_helper t)
    end.

  Definition bvec_denote {n} (v : bvec n) :=
    bitlist_denote_helper (Vector.projlist v).

  Example v10 : bvec 4 := Vector.cons _ zero _
                            (Vector.cons _ one _
                               (Vector.cons _ zero _
                                  (Vector.cons _ one _
                                     (Vector.nil _)))).
  Example bvec_test_10 : bvec_denote v10 = 10. auto. Qed.
End bvec_denote.

Section bvec_lshift1_correct.
  Definition bvec_lshift1_notrunc {n} (v : bvec n) : bvec (S n) :=
    Vector.cons _ zero _ v.

  (* denoted(shifted v) = shifted(denoted v) mod 2^SIZE *)
  Lemma bitlist_lshift1_notrunc_correct xs :
    bitlist_denote_helper (List.cons zero xs) =
      Nat.shiftl (bitlist_denote_helper xs) 1.
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
    Nat.double (bitlist_denote_helper xs) =
      bitlist_denote_helper (List.cons zero xs).
  Proof. simpl. reflexivity. Qed.

  Lemma Nat_ones_to_bitlist {n} :
    PeanoNat.Nat.ones n = bitlist_denote_helper (List.repeat one n).
  Proof.
    induction n.
    - auto.
    - simpl. rewrite <- IHn.
      rewrite PeanoNat.Nat.ones_succ. lia.
  Qed.

  Lemma x_plus_x_eq_twice_x x : x + x = 2 * x. lia. Qed.
  Lemma x_plus_1_eq_Sx x : x + 1 = S x. lia. Qed.

  Lemma Nat_land_cons_cons a xs b ys :
    Nat.land (bitlist_denote_helper (a :: xs)) (bitlist_denote_helper (b :: ys)) =
      bit2nat (bit_and a b) + Nat.double (Nat.land (bitlist_denote_helper xs) (bitlist_denote_helper ys)).
  Proof.
    simpl.
    repeat rewrite PeanoNat.Nat.double_twice.
    destruct a; simpl; destruct b; simpl; repeat rewrite PeanoNat.Nat.add_0_r; repeat rewrite x_plus_x_eq_twice_x.
    - rewrite PeanoNat.Nat.land_even_even. reflexivity.
    - replace (S (2 * bitlist_denote_helper ys)) with ((2 * bitlist_denote_helper ys) + 1).
      rewrite PeanoNat.Nat.land_even_odd. reflexivity.
      apply x_plus_1_eq_Sx.
    - replace (S (2 * bitlist_denote_helper xs)) with ((2 * bitlist_denote_helper xs) + 1).
      rewrite PeanoNat.Nat.land_odd_even. reflexivity.
      apply x_plus_1_eq_Sx.
    - replace (S (2 * bitlist_denote_helper xs)) with ((2 * bitlist_denote_helper xs) + 1).
      replace (S (2 * bitlist_denote_helper ys)) with ((2 * bitlist_denote_helper ys) + 1).
      rewrite PeanoNat.Nat.land_odd_odd. simpl. rewrite x_plus_1_eq_Sx. auto.
      apply x_plus_1_eq_Sx. apply x_plus_1_eq_Sx.
  Qed.

  Lemma Nat_land_xs_ys xs : forall ys,
      Nat.land (bitlist_denote_helper xs) (bitlist_denote_helper ys) =
        bitlist_denote_helper (map2_list bit_and xs ys).
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
    Nat.land (bitlist_denote_helper xs) (PeanoNat.Nat.ones n) =
      bitlist_denote_helper (List.firstn n xs).
  Proof.
    rewrite Nat_ones_to_bitlist. rewrite Nat_land_xs_ys.
    rewrite and_ones_to_firstn. reflexivity.
  Qed.

  Lemma Nat_land_double_xs_ones {n} (xs : list bit) :
    Nat.land (Nat.double (bitlist_denote_helper xs)) (PeanoNat.Nat.ones (S n)) =
      Nat.double (bitlist_denote_helper (List.firstn n xs)).
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
    bitlist_denote_helper (xs ++ zero :: nil) = bitlist_denote_helper xs.
  Proof.
    induction xs.
    - auto.
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma bvec_rshift1_correct_listify xs a :
    bitlist_denote_helper (xs ++ zero :: nil) =
      Nat.div2 (bit2nat a + Nat.double (bitlist_denote_helper xs)).
  Proof.
    destruct a; simpl; rewrite bitlist_denote_msb_zero.
    - rewrite div2_double. reflexivity.
    - destruct (bitlist_denote_helper xs). simpl. reflexivity.
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
