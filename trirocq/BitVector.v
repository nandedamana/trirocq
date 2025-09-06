Require Import trirocq.Bit.

From Stdlib Require Import Lia.

Lemma ltprv {i} {n} : S i < n -> i < n.
  lia.
Qed.

Definition bvec SIZE := Vector.t bit SIZE.
Definition bvec_ith {SIZE} (v : bvec SIZE) {i} (hidx : i < SIZE) :=
  Vector.nth_order v hidx.

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

(* ------------------------------------------------------------------------ *)

Section bvec_addition.
  Axiom bvec_add : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.

  (* Uses the "convoy pattern" to solve the issue noted above
   * - http://adam.chlipala.net/cpdt/html/MoreDep.html
   * - https://stackoverflow.com/questions/32060556/convoy-pattern-and-match-involving-inequality?rq=3
   *)
  (* Carry due to the addition of bits at position (i - 1); 0 for i = 0 *)
  Fixpoint bvec_incarry {SIZE} (x y : bvec SIZE) {i} (hidx : i < SIZE) : bit :=
    match i return i < SIZE -> bit with
    | 0 => fun _ => zero
    | S i' => fun hidx => let a := bvec_ith x (ltprv hidx) in
                          let b := bvec_ith y (ltprv hidx) in
                          let cin := bvec_incarry x y (ltprv hidx) in
                          bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin)
    end hidx.

  (* Takes away the convoy pattern, making some upcoming proofs simpler *)
  Lemma bvec_incarry_Si {SIZE} (x y : bvec SIZE) {i} (hidx : S i < SIZE) :
    bvec_incarry x y hidx = let a := bvec_ith x (ltprv hidx) in
                            let b := bvec_ith y (ltprv hidx) in
                            let cin := bvec_incarry x y (ltprv hidx) in
                            bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin).
  Proof.
    auto.
  Qed.

  Axiom bvec_fulladd_result : forall {SIZE} x y [i] (hidx : i < SIZE), bvec_ith (bvec_add x y) hidx = bit_xor (bvec_incarry x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
End bvec_addition.

(* ------------------------------------------------------------------------ *)

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

  Axiom bvec_fullsub_result : forall {SIZE} x y [i] (hidx : i < SIZE), bvec_ith (bvec_sub x y) hidx = bit_xor (bvec_inborrow x y hidx) (bit_xor (bvec_ith x hidx) (bvec_ith y hidx)).
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

  Lemma suclt {i} {n} : i < S n -> i <> n -> S i < S n. lia. Qed.

  (* Remember: head (i = 0) has the LSB *)
  Axiom bvec_lshift1 : forall {n}, bvec (S n) -> bvec (S n).

  Axiom bvec_lshift1_ith_0 : forall {n} (v : bvec (S n)) (hi : 0 < S n),
      bvec_ith (bvec_lshift1 v) hi = zero.

  Axiom bvec_lshift1_ith_S : forall {n} (v : bvec (S n)) {i} (hi : S i < S n),
      bvec_ith (bvec_lshift1 v) hi = bvec_ith v (ltprv hi).

  (* Using logical shift since the type used in Linux is u64 *)
  Axiom bvec_rshift1 : forall {n}, bvec (S n) -> bvec (S n).

  Axiom bvec_rshift1_ith_0 : forall {n} (v : bvec (S n)) (hi : 0 < S n) (hi2 : 0 <> n),
      bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).

  Axiom bvec_rshift1_ith_ltn : forall {n} (v : bvec (S n)) {i} (hi : i < S n) (hi2 : i <> n),
      bvec_ith (bvec_rshift1 v) hi = bvec_ith v (suclt hi hi2).

  Axiom bvec_rshift1_ith_n : forall {n} (v : bvec (S n)) (hi : n < S n),
      bvec_ith (bvec_rshift1 v) hi = zero.

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
    Lemma lshift_is_correct :
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
    Lemma rshift_is_correct :
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
