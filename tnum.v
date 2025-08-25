(* Nandakumar Edamana
 * Started 2025-04-09
 *)

Require Vector.

Variant bit := zero | one.

Definition bit_and (x y : bit) :=
  match x, y with
  | one, one => one
  | _, _ => zero
  end.

Definition bit_not (x : bit) :=
  match x with
  | zero => one
  | one => zero
  end.

Definition bit_or (x y : bit) :=
  match x, y with
  | zero, zero => zero
  | _, _ => one
  end.

Definition bit_xor (x y : bit) :=
  match x, y with
  | zero, zero => zero
  | zero, one => one
  | one, zero => one
  | one, one => zero
  end.

Section bitops_simplification.
  Lemma bit_and_left_zero x : bit_and zero x = zero.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_right_zero x : bit_and x zero = zero.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_left_one x : bit_and one x = x.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_right_one x : bit_and x one = x.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_left_zero x : bit_or zero x = x.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_right_zero x : bit_or x zero = x.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_left_one x : bit_or one x = one.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_right_one x : bit_or x one = one.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_left_zero x : bit_xor zero x = x.
    unfold bit_xor; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_right_zero x : bit_xor x zero = x.
    unfold bit_xor; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_x_y_zero x y : bit_xor x y = zero -> x = y.
    intros. destruct x; destruct y; auto.
  Qed.

  Lemma bit_xor_x_y_z_y x y z : bit_xor x (bit_xor y z) = y -> bit_xor x z = zero.
    intros. destruct x; destruct y; destruct z; easy.
  Qed.

  Lemma bit_or_zero_zero x y : bit_or x y = zero -> x = zero /\ y = zero.
    intros. destruct x; destruct y; auto.
  Qed.
End bitops_simplification.

(* Not accessible from other sections if put inside bitops_simplification. *)
Ltac simplify_bit_ops_ex_not :=
  try rewrite bit_and_left_zero;
  try rewrite bit_and_right_zero;
  try rewrite bit_and_left_one;
  try rewrite bit_and_right_one;
  try rewrite bit_or_left_zero;
  try rewrite bit_or_right_zero;
  try rewrite bit_or_left_one;
  try rewrite bit_or_right_one;
  try rewrite bit_xor_left_zero;
  try rewrite bit_xor_right_zero.

Ltac simplify_bit_ops :=
  unfold bit_not;
  simplify_bit_ops_ex_not.

Require Import Lia.
Lemma ltprv {i} {n} : S i < n -> i < n.
  lia.
Qed.

Definition p_from_pltq {p q} (pltq : p < q) := p.


Section bvec.
  Definition bvec SIZE := Vector.t bit SIZE.
  Definition bvec_ith {SIZE} (v : bvec SIZE) {i} (hidx : i < SIZE) :=
    Vector.nth v (Fin.of_nat_lt hidx).

  (* TODO rem? *)
  Definition bvec_eq {SIZE} (x y : bvec SIZE) :=
    forall i (hidx : i < SIZE), bvec_ith x hidx = bvec_ith y hidx.

  Axiom bvec_and : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.
  Axiom bvec_and_rel : forall {SIZE} (v1 v2 : bvec SIZE) {i} (hidx : i < SIZE),
      bvec_ith (bvec_and v1 v2) hidx = bit_and (bvec_ith v1 hidx) (bvec_ith v2 hidx).

  Axiom bvec_neg : forall {SIZE}, bvec SIZE -> bvec SIZE.
  Axiom bvec_neg_rel : forall {SIZE} (v1 : bvec SIZE) {i} (hidx : i < SIZE),
      bvec_ith (bvec_neg v1) hidx = bit_not (bvec_ith v1 hidx).

  Axiom bvec_or : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.
  Axiom bvec_or_rel : forall {SIZE} (v1 v2 : bvec SIZE) {i} (hidx : i < SIZE),
      bvec_ith (bvec_or v1 v2) hidx = bit_or (bvec_ith v1 hidx) (bvec_ith v2 hidx).

  Axiom bvec_xor : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.
  Axiom bvec_xor_rel : forall {SIZE} (v1 v2 : bvec SIZE) {i} (hidx : i < SIZE),
      bvec_ith (bvec_xor v1 v2) hidx = bit_xor (bvec_ith v1 hidx) (bvec_ith v2 hidx).

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

  Check Vector.cons.
  (* TODO doc somewhere above: I've checked this and found not of much use:
     https://docs.rocq-prover.org/v8.16/stdlib/Coq.Bool.Bvector.html
   *)

  Section bvec_multiplication.
    Fixpoint zerovec SIZE := match SIZE with
                             | 0 => Vector.nil bit
                             | S p => Vector.cons bit zero p (zerovec p)
                             end.

    Check (zerovec 4 : Vector.t bit 4).
    (* Compute zerovec 4. *)

    Definition bvec_mul_single {SIZE} y (x : bvec SIZE) := match y with
                                                           | zero => zerovec SIZE
                                                           | one => x
                                                           end.

    Lemma ltprv2 {i} {n} : S i < S n -> i < n.
      lia.
    Qed.

    (* TODO confirm the semantics of << and >> (zero-ext vs sign-ext) *)

    (* Because splitat takes Vector.t ?A (?l + ?r) *)
    Lemma bvec_splitcast1 {SIZE} {i} (x : Vector.t bit SIZE) (hidx : i <= SIZE) : Vector.t bit (SIZE - i + i).
      assert (H : SIZE - i + i = SIZE). lia.
      rewrite H. assumption.
    Qed.

    Lemma bvec_splitcast2 {SIZE} {i} (x : Vector.t bit SIZE) (hidx : i <= SIZE) : Vector.t bit (i + (SIZE - i)).
      assert (H : i + (SIZE - i) = SIZE). lia.
      rewrite H. assumption.
    Qed.

    Lemma bvec_splitcast2_rev {SIZE} {i} (x : Vector.t bit (i + (SIZE - i))) (hidx : i <= SIZE) : Vector.t bit SIZE.
      assert (H : i + (SIZE - i) = SIZE). lia.
      rewrite <- H. assumption.
    Qed.

    Definition bvec_lshift {SIZE} (x : Vector.t _ SIZE) {i} (hidx : i <= SIZE) : bvec SIZE :=
      let splt := Vector.splitat (SIZE - i) (bvec_splitcast1 x hidx) in
      let shiftres := Vector.append (zerovec i) (fst splt) in
      bvec_splitcast2_rev shiftres hidx.

    (* TODO test *)
    Definition bvec_rshift {SIZE} (x : Vector.t _ SIZE) {i} (hidx : i <= SIZE) : bvec SIZE :=
      let splt := Vector.splitat i (bvec_splitcast2 x hidx) in
      let shiftres := Vector.append (fst splt) (zerovec (SIZE - i)) in
      bvec_splitcast2_rev shiftres hidx.

    (* Testing *)
    Fixpoint onevec SIZE := match SIZE with
                            | 0 => Vector.nil bit
                            | S p => Vector.cons bit one p (onevec p)
                            end.

    Lemma le_2_8 : 2 <= 8. lia. Qed.
    Definition b252 := (bvec_lshift (onevec 8) le_2_8).
    Compute b252. (* TODO looks really awful, but seems correct, assuming head has the LSB *)

    Lemma lt_0_8 : 0 < 8. lia. Qed.
    Compute (bvec_ith b252 lt_0_8). (* zero *)

    Lemma lt_1_8 : 1 < 8. lia. Qed.
    Compute (bvec_ith b252 lt_1_8). (* zero *)

    Lemma lt_2_8 : 2 < 8. lia. Qed.
    Compute (bvec_ith b252 lt_2_8). (* unevaluated long term *)
    (* End Testing *)

    (* Based on Observation 18 from Harishankar et al. *)
    (* TODO test *)
    Section bvec_mul_without_rshift.
      Fixpoint bvec_mul_helper {SIZE} (x y : bvec SIZE) (acc : bvec SIZE) {i} (hidx : i < SIZE) :=
        match i return i < SIZE -> bvec SIZE with
        | 0 => fun _ => bvec_mul_single (bvec_ith y hidx) x
        | S p => fun hidx =>
                   let newacc := bvec_add acc (bvec_mul_single (bvec_ith y hidx) (bvec_lshift x hidx)) in
                   bvec_mul_helper x y newacc (ltprv hidx)
        end hidx.

      Definition bvec_mul_without_shift {n} (x y : bvec (S n)) :=
        bvec_mul_helper x y (zerovec (S n)) (PeanoNat.Nat.lt_0_succ n).
    End bvec_mul_without_rshift.

    Definition bvec_lsb {n} (x : bvec (S n)) := bvec_ith x (PeanoNat.Nat.lt_0_succ n).
  End bvec_multiplication.
End bvec.

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t SIZE := cons (v : bvec SIZE) (m : bvec SIZE).

  Definition v {SIZE} (P : t SIZE) := match P with cons _ v _ => v end.
  Definition m {SIZE} (P : t SIZE) := match P with cons _ _ m => m end.

  Definition ith_v {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (v tn) hidx.
  Definition ith_m {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (m tn) hidx.

  (* TODO rem? *)
  Definition eq {SIZE} (P Q : t SIZE) := bvec_eq (v P) (v Q) /\ bvec_eq (m P) (m Q).

  Definition wellformed {SIZE} (tn : t SIZE) :=
    forall {i} (hidx : i < SIZE), bvec_ith (m tn) hidx = one -> bvec_ith (v tn) hidx = zero.
  (*
    Definition wellformed_hari (tn : t) := bvec_and (v tn) (m tn) = zero64. (* TODO prove my wellformed <-> wellformed_hari *)
   *)

  Lemma ith_m_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_m (cons SIZE n1 n2) hidx = bvec_ith n2 hidx.
    unfold ith_m. simpl. reflexivity.
  Qed.

  Lemma ith_m_simplify2 {SIZE} n1 n2 i (hidx : i < SIZE) : bvec_ith (m (cons SIZE n1 n2)) hidx = bvec_ith n2 hidx.
    simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_v (cons SIZE n1 n2) hidx = bvec_ith n1 hidx.
    unfold ith_v. simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify2 {SIZE} n1 n2 i (hidx : i < SIZE) : bvec_ith (v (cons SIZE n1 n2)) hidx = bvec_ith n1 hidx.
    simpl. reflexivity.
  Qed.

  (* Using `unfold m` directly could cause unwanted expansions in some places. *)
  Lemma m_cons_simplify {SIZE} n1 n2 : m (cons SIZE n1 n2) = n2.
    unfold m. reflexivity.
  Qed.

  Lemma v_cons_simplify {SIZE} n1 n2 : v (cons SIZE n1 n2) = n1.
    unfold v. reflexivity.
  Qed.
End tnum.

Definition ingamma {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) : Prop :=
  forall i (hidx : i < SIZE),
    tnum.ith_m T hidx = zero -> bvec_ith x hidx = tnum.ith_v T hidx.

(* Based on Harishankar et al. *)
(* TODO prove member <-> ingamma *)
Definition member {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) : Prop :=
  bvec_and x (bvec_neg (tnum.m T)) = tnum.v T.


Ltac unwrap_bvec_ops := match goal with
                          _ => repeat rewrite bvec_and_rel;
                               repeat rewrite bvec_neg_rel;
                               repeat rewrite bvec_or_rel;
                               repeat rewrite bvec_xor_rel
                        end.

Ltac rewrite_if_holds H :=
  match type of H with
  | ?b = ?b -> _ => rewrite H
  end.


(* TODO rename *)
Ltac crush10 := match goal with
                | [ H : ?x = ?x -> zero = one |- _ ] => specialize (H eq_refl); easy
                | [ H : ?x = ?x -> one = zero |- _ ] => specialize (H eq_refl); easy
                end.

Section linux_tnum_addition.
  (* Mirrors the Linux kernel definition *)

  Definition tnum_ith_chi {SIZE} P Q [i] (hidx : i < SIZE) :=
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    bvec_ith chi hidx.

  Definition tnum_add {SIZE} P Q :=
    let sv := bvec_add (tnum.v P) (tnum.v Q) in
    let sm := bvec_add (tnum.m P) (tnum.m Q) in
    let sig := bvec_add sv sm in
    let chi := bvec_xor sig sv in
    let eta := bvec_or chi (bvec_or (tnum.m P) (tnum.m Q)) in
    tnum.cons SIZE (bvec_and sv (bvec_neg eta)) eta.

  (* TODO rename *)
  (* Unused, but still an interesting observation. *)
  Lemma helper14 {SIZE} v1 v2 {i} (hidx : i < SIZE) :
    bvec_ith (bvec_xor (bvec_add v1 v2) v1) hidx = bit_xor (bvec_ith v2 hidx) (bvec_incarry v1 v2 hidx).
  Proof.
    unwrap_bvec_ops.
    rewrite bvec_fulladd_result with (x := v1) (y := v2).
    destruct (bvec_ith v1 hidx); destruct (bvec_ith v2 hidx); destruct (bvec_incarry v1 v2 hidx); auto.
  Qed.

  (* Is chi is the mask bit of the incoming carry? No; it considers v bits as well. chi[i] in fact `tnum.ith_m (tnum_add P Q) hidx` excluding P.m[i] | Q.m[i] *)
  Lemma helper32 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      tnum.ith_m P hidx = zero /\ tnum.ith_m Q hidx = zero /\
        tnum_ith_chi P Q hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold tnum_ith_chi.
    intros wf1 wf2 i hidx.
    specialize (wf1 i hidx).
    specialize (wf2 i hidx).

    destruct i;
      unfold tnum_add;
      rewrite tnum.ith_m_simplify;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fulladd_result;
      unfold bvec_incarry;
      destruct (bvec_ith (tnum.m P) hidx);
      destruct (bvec_ith (tnum.m Q) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  Lemma helper66 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_incarry (tnum.m P) (tnum.m Q) hidx)
        (bvec_incarry (tnum.v P) (tnum.v Q) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
      destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  (* Interesting: proving only one side would seem easier, but it is actually
   * difficult, if not impossible. I suppose it is because that way the
   * induction hypothesis becomes weaker.
   *)
  Lemma helper63 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_incarry (tnum.m P) (tnum.m Q) hidx)
        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
           (bvec_add (tnum.m P) (tnum.m Q)) hidx) = zero /\
        bit_and (bvec_incarry (tnum.v P) (tnum.v Q) hidx)
          (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
             (bvec_add (tnum.m P) (tnum.m Q)) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    - intros hidx.
      repeat rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                    (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  Lemma helper45 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : S i < SIZE),
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero ->
      let sv := bvec_add (tnum.v P) (tnum.v Q) in
      let sm := bvec_add (tnum.m P) (tnum.m Q) in
      bvec_incarry sv sm hidx = zero ->
      bvec_incarry x y hidx = bvec_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed.
    unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq igp igq.

    induction i.
    - intro hidx.
      rewrite bvec_incarry_Si. simpl.
      repeat rewrite bvec_fulladd_result.
      unfold bvec_incarry.
      repeat simplify_bit_ops.

      specialize (wfp 0 (ltprv hidx)).
      specialize (wfq 0 (ltprv hidx)).
      specialize (igp 0 (ltprv hidx)).
      specialize (igq 0 (ltprv hidx)).

      destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
    - intro hidx.
      rewrite bvec_incarry_Si.
      rewrite bvec_incarry_Si with (x := x).
      repeat rewrite bvec_incarry_Si with (hidx := hidx).
      repeat rewrite bvec_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      assert (h64 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                         (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero /\
                      bit_and (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx))
                        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                           (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero).
      apply helper63; auto.


      specialize (wfp (S i) (ltprv hidx)).
      specialize (wfq (S i) (ltprv hidx)).
      specialize (igp (S i) (ltprv hidx)).
      specialize (igq (S i) (ltprv hidx)).

      destruct(bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                    (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
        destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));

        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;

        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;

        destruct (bvec_ith x (ltprv hidx));
        destruct (bvec_ith y (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try crush10.
  Qed.

  Lemma helper82 [x] [y] : bit_xor x y = zero -> bit_and y x = zero -> x = zero /\ y = zero.
    unfold bit_xor. unfold bit_and. destruct x; destruct y; auto.
  Qed.

  Lemma helper33 {SIZE} x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      bvec_incarry x y hidx = bvec_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.
    destruct H as (wfp & wfq & igP & igQ).
    destruct i.
    - unfold bvec_incarry. auto.
    -
      intros hidx.
      unfold tnum_add.
      rewrite tnum.ith_m_simplify.
      unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.

      intro H.
      assert (hmp : bvec_ith (tnum.m P) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m P) hidx);
        repeat simplify_bit_ops; try easy.

      assert (hmq : bvec_ith (tnum.m Q) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m Q) hidx);
        repeat simplify_bit_ops; try easy.

      apply bit_or_zero_zero in H as (H1 & H2).
      apply bit_xor_x_y_zero in H1.
      apply bit_xor_x_y_z_y in H1.

      revert H1. rewrite hmp. rewrite hmq. repeat simplify_bit_ops.

      pose (h63 := helper63 P Q wfp wfq hidx).
      destruct h63 as (h1 & h2). intro h3.
      pose (h82 := helper82 h3 h1). destruct h82.
      apply helper45; auto.
  Qed.

  Lemma wellformed_general {SIZE} inval mu :
    forall [i] (hidx : i < SIZE),
      bvec_ith mu hidx = one -> bvec_ith (bvec_and inval (bvec_neg mu)) hidx = zero.
  Proof.
    intros i hidx H.
    unwrap_bvec_ops. rewrite H. simpl.
    destruct (bvec_ith inval hidx); auto.
  Qed.

  Lemma tnum_add_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q -> tnum.wellformed (tnum_add P Q).
  Proof.
    unfold tnum.wellformed.
    intro H.
    unfold tnum_add.
    apply wellformed_general.
  Qed.

  (* Soundness: the result of adding abstract numbers P and Q include the results
   * of adding any concrete p and q (written less formally for simplicity).
   *)
  Lemma tnum_add_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_add P Q) /\
      ingamma (bvec_add x y) (tnum_add P Q).
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.

    pose (H'1 := helper33 x y P Q H).

    unfold tnum.ith_m in H.
    destruct H as (wf1 & wf2 & igP & igQ).

    split. apply tnum_add_wellformed; auto.

    pose (H'2 := helper32 P Q wf1 wf2). unfold tnum.ith_m in H'2. (* TODO rename *)
    unfold ingamma.

    intros i hidx rmskz.

    specialize (H'2 i hidx rmskz) as (xmskz & ymskz & cinmskz).
    specialize (H'1 i hidx rmskz).
    revert rmskz.

    revert cinmskz.

    unfold tnum_add.
    rewrite tnum.ith_m_simplify.
    rewrite tnum.ith_v_simplify.

    unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
    rewrite xmskz. rewrite ymskz. rewrite igP; auto. rewrite igQ; auto. simpl.

    unfold tnum.ith_v.

    intros H1 H2.

    (* Replaces the subexpression H2 from the goal with zero because it is
     * the ith bit of `mu` (the `mu` from `sv & ~mu`), which is zero as per
     * the assumption.
     *)
    rewrite H2. simpl.
    rewrite H'1.
    rewrite bit_and_right_one.
    auto.
  Qed.

  Section tnum_add_optimality.
    (* Finding the bits that can be uncertain (by propagation) involves taking the
     * difference of the maximum concrete sum and the minimum concrete sum of P and Q.
     * The idea comes from https://dougallj.wordpress.com/2020/01/13/bit-twiddling-addition-with-unknown-bits/
     *)
    Definition minsum {SIZE} (P : tnum.t SIZE) Q := bvec_add (tnum.v P) (tnum.v Q).
    Definition maxsum {SIZE} (P : tnum.t SIZE) Q :=
      bvec_add (bvec_or (tnum.v P) (tnum.m P)) (bvec_or (tnum.v Q) (tnum.m Q)).
    Definition minmask {SIZE} (P : tnum.t SIZE) Q := bvec_xor (minsum P Q) (maxsum P Q).

    (* TODO better, directly work on the result of tnum_add(). *)
    (* TODO FIXME wait, why just chi? ith `mu = chi | a.mask | b.mask`, right?
     * does this mean `a.mask | b.mask` is irrelevant? Not according to my brute-force experi.
     * Also, this looks unprovable:
     * bit_or (tnum_ith_chi P Q hidx) (bit_or (bvec_ith (tnum.m P) hidx) (bvec_ith (tnum.m Q) hidx)) = bvec_ith (minmask P Q) hidx.
     *)
    Lemma tnum_add_optimal {SIZE} P Q :
      tnum.wellformed P -> tnum.wellformed Q ->
      forall [i] (hidx : i < SIZE),
        tnum_ith_chi P Q hidx = bvec_ith (minmask P Q) hidx.
    Proof.
      unfold tnum.wellformed.
      intros wfp wfq i hidx.
      unfold tnum_ith_chi. unfold minmask. unfold maxsum. unfold minsum.
      induction i.
      -
        specialize (wfp 0 hidx).
        specialize (wfq 0 hidx).

        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        unfold bvec_incarry. unwrap_bvec_ops. repeat simplify_bit_ops.

        destruct (bvec_ith (tnum.m P) hidx);
        destruct (bvec_ith (tnum.m Q) hidx);
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) hidx);
        destruct (bvec_ith (tnum.v Q) hidx);
        repeat simplify_bit_ops; try easy.
      -
        assert (wfpi : bvec_ith (tnum.m P) hidx = one -> bvec_ith (tnum.v P) hidx = zero). apply wfp.
        assert (wfqi : bvec_ith (tnum.m Q) hidx = one -> bvec_ith (tnum.v Q) hidx = zero). apply wfq.
        assert (wfpp : bvec_ith (tnum.m P) (ltprv hidx) = one -> bvec_ith (tnum.v P) (ltprv hidx) = zero). apply wfp.
        assert (wfqp : bvec_ith (tnum.m Q) (ltprv hidx) = one -> bvec_ith (tnum.v Q) (ltprv hidx) = zero). apply wfq.
        specialize (IHi (ltprv hidx)).

        assert (h66 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                        (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
        apply helper66; auto.

        assert (h64 : bit_and (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                        (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                           (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero /\
                        bit_and (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx))
                          (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q))
                             (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero).
        apply helper63; auto.

        revert IHi.
        unwrap_bvec_ops. repeat rewrite bvec_fulladd_result.
        repeat rewrite bvec_incarry_Si. unwrap_bvec_ops. repeat simplify_bit_ops.
        repeat rewrite bvec_fulladd_result.

        destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
          destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
          destruct (bvec_incarry (bvec_add (tnum.v P) (tnum.v Q)) (bvec_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
          destruct (bvec_incarry (bvec_or (tnum.v P) (tnum.m P)) (bvec_or (tnum.v Q) (tnum.m Q)) (ltprv hidx)); try easy;
          destruct (bvec_ith (tnum.m P) (ltprv hidx));
          destruct (bvec_ith (tnum.m Q) (ltprv hidx));
          try rewrite_if_holds wfpp;
          try rewrite_if_holds wfqp;
          destruct (bvec_ith (tnum.v P) (ltprv hidx));
          destruct (bvec_ith (tnum.v Q) (ltprv hidx)); try easy;
          destruct (bvec_ith (tnum.m P) hidx);
          destruct (bvec_ith (tnum.m Q) hidx);
          try rewrite_if_holds wfpi;
          try rewrite_if_holds wfqi;
          destruct (bvec_ith (tnum.v P) hidx);
          destruct (bvec_ith (tnum.v Q) hidx); try easy.
    Qed.
  End tnum_add_optimality.
End linux_tnum_addition.

Section linux_tnum_subtraction.
  (* Mirrors the Linux kernel definition *)

  Definition tnum_sub_ith_chi {SIZE} P Q [i] (hidx : i < SIZE) :=
    let dv := bvec_sub (tnum.v P) (tnum.v Q) in
    let alpha := bvec_add dv (tnum.m P) in
    let beta := bvec_sub dv (tnum.m Q) in
    let chi := bvec_xor alpha beta in
    bvec_ith chi hidx.

  Definition tnum_sub {SIZE} P Q :=
    let dv := bvec_sub (tnum.v P) (tnum.v Q) in
    let alpha := bvec_add dv (tnum.m P) in
    let beta := bvec_sub dv (tnum.m Q) in
    let chi := bvec_xor alpha beta in
    let mu := bvec_or chi (bvec_or (tnum.m P) (tnum.m Q)) in
    tnum.cons SIZE (bvec_and dv (bvec_neg mu)) mu.

  Lemma sublemma32 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_sub P Q) hidx = zero ->
      tnum.ith_m P hidx = zero /\ tnum.ith_m Q hidx = zero /\
        tnum_sub_ith_chi P Q hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold tnum_sub_ith_chi.
    intros wf1 wf2 i hidx.
    specialize (wf1 i hidx).
    specialize (wf2 i hidx).

    destruct i;
      unfold tnum_sub;
      rewrite tnum.ith_m_simplify;
      unwrap_bvec_ops; unfold tnum.ith_m;
      rewrite bvec_fullsub_result;
      unfold bvec_inborrow;
      destruct (bvec_ith (tnum.m P) hidx);
      destruct (bvec_ith (tnum.m Q) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  Lemma xor_x_y_eq_z_y x y z : bit_xor x y = bit_xor z y -> x = z.
    unfold bit_xor; destruct x; destruct y; destruct z; try easy.
  Qed.

  Ltac easy_neg :=
    let H := fresh "H" in
    match goal with
    | [ |- ?x = bit_not ?x -> _ ] => unfold bit_not; easy
    end.

  (* concerns the borrows generated by dv and beta *)
  Lemma sublemma64 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) hidx)
        (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - auto.
    -
      intros hidx.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      repeat rewrite bvec_inborrow_Si. simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  (* TODO fuse with sublemma64? *)
  (* concerns the borrow generated by dv and the carry generated by alpha *)
  Lemma sublemma67 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bvec_inborrow (tnum.v P) (tnum.v Q) hidx = zero ->
        bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - auto.
    -
      intros hidx.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      repeat rewrite bvec_incarry_Si. repeat rewrite bvec_inborrow_Si. simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  Lemma sublemma42 {SIZE} P Q :
    forall [i] (hidx : S i < SIZE),
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero ->
      bit_and (bvec_ith (tnum.m P) (ltprv hidx)) (bvec_ith (tnum.m Q) (ltprv hidx)) = zero.
  Proof.
    unfold tnum.wellformed.
    intros i hidx.
    rewrite bvec_incarry_Si.
    destruct (bvec_ith (tnum.m P) (ltprv hidx));
      destruct (bvec_ith (tnum.m Q) (ltprv hidx));
      repeat simplify_bit_ops; try easy.
  Qed.

  Lemma sublemma43 {SIZE} P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
        bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx ->
      bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq.
    induction i.
    - unfold bvec_incarry. auto.
    -
      intro hidx.

      assert (bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx))
              (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx)) = zero).
      apply sublemma64; auto.

      assert (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx) = zero ->
              bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx) = zero).
      apply sublemma67; auto.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      rewrite bvec_incarry_Si.
      simpl.
      repeat rewrite bvec_fullsub_result. simpl.

      destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        try crush10; try easy.
  Qed.

  (* Turns out inborrow = incarry if the result has mask = 0. *)
  Lemma sublemma45 {SIZE} x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
        bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx ->
      bvec_inborrow x y hidx = bvec_inborrow (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq igP igQ.
    induction i.
    - unfold bvec_inborrow. auto.
    -
      intro hidx.

      intro H.
      (* Not true for borrow. TODO note: why is this the case? Consider the case of `mu - mu`; `P.mask - Q.mask` = `1 - 1 = 0`, no borrow; but the uncertainty should actually propagate; hence carry. *)
      assert (h43 : bvec_incarry (tnum.m P) (tnum.m Q) hidx = zero).
      apply sublemma43; auto.
      revert H. revert h43.
      intro H.

      assert (H1 : bit_and (bvec_ith (tnum.m P) (ltprv hidx)) (bvec_ith (tnum.m Q) (ltprv hidx)) = zero). apply sublemma42; auto. revert H.

      assert (bit_and (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx))
              (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx)) = zero).
      apply sublemma64; auto.

      assert (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx) = zero ->
              bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx) = zero).
      apply sublemma67; auto.

      repeat rewrite bvec_incarry_Si.
      repeat rewrite bvec_inborrow_Si.
      (* simpl. *) (* TODO see if doing this here makes some assertions unnecessary. *)
      repeat rewrite bvec_fullsub_result. simpl.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).
      specialize (igP i (ltprv hidx)).
      specialize (igQ i (ltprv hidx)).

      destruct (bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) (ltprv hidx));
        destruct (bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) (ltprv hidx));
        try rewrite_if_holds IHi; auto;
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igP;
        try rewrite_if_holds igQ;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops_ex_not; try easy;
        try easy_neg;
        destruct (bvec_ith x (ltprv hidx));
        destruct (bvec_ith y (ltprv hidx));
        destruct (bvec_inborrow (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try auto; try crush10.
  Qed.

  Lemma sublemma33 {SIZE} x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_sub P Q) hidx = zero ->
      bvec_inborrow x y hidx = bvec_inborrow (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intro H.
    destruct H as (wfp & wfq & igP & igQ).
    induction i.
    - unfold bvec_inborrow. auto.
    -
      intros hidx.
      unfold tnum_sub.
      rewrite tnum.ith_m_simplify2.
      unwrap_bvec_ops.
      repeat rewrite bvec_fulladd_result. repeat rewrite bvec_fullsub_result.

      (* TODO why don't reuse sublemma32 here? If doing, do the same for addition as well. *)

      intro H.
      assert (hmp : bvec_ith (tnum.m P) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m P) hidx);
        repeat simplify_bit_ops; try easy.

      assert (hmq : bvec_ith (tnum.m Q) hidx = zero). revert H.
      destruct (bvec_ith (tnum.m Q) hidx);
        repeat simplify_bit_ops; try easy.

      apply bit_or_zero_zero in H as (H1 & H2).
      apply bit_xor_x_y_zero in H1.

      rewrite hmp in H1. rewrite hmq in H1.
      apply xor_x_y_eq_z_y in H1.

      (* H1 seems interesting at this point:
         bvec_incarry (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m P) hidx =
         bvec_inborrow (bvec_sub (tnum.v P) (tnum.v Q)) (tnum.m Q) hidx
       *)
      apply sublemma45; auto.
  Qed.

  Lemma tnum_sub_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q -> tnum.wellformed (tnum_sub P Q).
  Proof.
    unfold tnum.wellformed.
    intro H.
    unfold tnum_sub.
    apply wellformed_general.
  Qed.

  Lemma tnum_sub_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_sub P Q) /\
      ingamma (bvec_sub x y) (tnum_sub P Q).
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.

    pose (H'1 := sublemma33 x y P Q H).

    unfold tnum.ith_m in H.
    destruct H as (wf1 & wf2 & igP & igQ).

    split. apply tnum_sub_wellformed; auto.

    pose (H'2 := sublemma32 P Q wf1 wf2). unfold tnum.ith_m in H'2. (* TODO rename *)
    unfold ingamma.

    intros i hidx rmskz.

    specialize (H'2 i hidx rmskz) as (xmskz & ymskz & binmskz).
    specialize (H'1 i hidx rmskz).
    revert rmskz.

    revert binmskz.

    unfold tnum_sub.
    rewrite tnum.ith_m_simplify.
    rewrite tnum.ith_v_simplify.

    unwrap_bvec_ops. repeat rewrite bvec_fullsub_result.
    rewrite xmskz. rewrite ymskz. rewrite igP; auto. rewrite igQ; auto. simpl.

    unfold tnum.ith_v.

    intros H1 H2.

    (* Replaces the subexpression H2 from the goal with zero because it is
     * the ith bit of `mu` (the `mu` from `sv & ~mu`), which is zero as per
     * the assumption.
     *)
    rewrite H2. simpl.
    rewrite H'1.
    rewrite bit_and_right_one.
    auto.
  Qed.
End linux_tnum_subtraction.

Module bmir. (* bvec_mul_iter_result *)
  Inductive t {n} := cons (a b acc : bvec (S n)).

  Definition a {n} (r : @bmir.t n) :=
    match r with cons a _ _ => a end.

  Definition b {n} (r : @bmir.t n) :=
    match r with cons _ b _ => b end.

  Definition acc {n} (r : @bmir.t n) :=
    match r with cons _ _ acc => acc end.
End bmir.

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
  (* TODO move *)
  Definition tnum_lshift {SIZE} (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :=
    tnum.cons SIZE (bvec_lshift (tnum.v P) hidx) (bvec_lshift (tnum.m P) hidx).

  Lemma tnum_lshift_wellformed {SIZE} (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :
    tnum.wellformed P -> tnum.wellformed (tnum_lshift P hidx).
  Proof.
    (* TODO *)
  Admitted.

  (* TODO includes wellformedness; update the users *)
  Lemma tnum_lshift_sound {SIZE} (x : bvec SIZE) (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_lshift P hidx) /\ ingamma (bvec_lshift x hidx) (tnum_lshift P hidx).
  Proof.
    (* TODO *)
  Admitted.
  
  Definition tnum_rshift {SIZE} (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :=
    tnum.cons SIZE (bvec_rshift (tnum.v P) hidx) (bvec_rshift (tnum.m P) hidx).


  Lemma tnum_rshift_wellformed {SIZE} (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :
    tnum.wellformed P -> tnum.wellformed (tnum_rshift P hidx).
  Proof.
    (* TODO *)
  Admitted.

  (* TODO includes wellformedness; update the users *)
  Lemma tnum_rshift_sound {SIZE} (x : bvec SIZE) (P : tnum.t SIZE) {i} (hidx : i <= SIZE) :
    tnum.wellformed P -> ingamma x P ->
    tnum.wellformed (tnum_rshift P hidx) /\ ingamma (bvec_rshift x hidx) (tnum_rshift P hidx).
  Proof.
    (* TODO *)
  Admitted.

  (* TODO move *)
  Definition tnum_union {SIZE} (P Q : tnum.t SIZE) :=
    let v := bvec_and (tnum.v P) (tnum.v Q) in
    let m := bvec_or (bvec_or (bvec_xor (tnum.v P) (tnum.v Q)) (tnum.m P)) (tnum.m Q) in
    tnum.cons SIZE (bvec_and v (bvec_neg m)) m.

  Lemma tnum_union_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    tnum.wellformed (tnum_union P Q).
  Proof.
    unfold tnum_union. unfold tnum.wellformed.
    intros wfP wfQ i hidx.
    rewrite tnum.ith_m_simplify2.
    rewrite tnum.ith_v_simplify2.
    unwrap_bvec_ops.
    specialize (wfP i hidx).
    specialize (wfQ i hidx).
    destruct (bvec_ith (tnum.m P) hidx); try rewrite_if_holds wfP;
      destruct (bvec_ith (tnum.m Q) hidx); try rewrite_if_holds wfQ; try easy;
      destruct (bvec_ith (tnum.v P) hidx);
      destruct (bvec_ith (tnum.v Q) hidx);
      repeat simplify_bit_ops; auto.
  Qed.

  Definition subset {SIZE} (P Q : tnum.t SIZE) :=
    forall x, ingamma x P -> ingamma x Q.

  Lemma tnum_union_sound {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset P U /\ subset Q U.
  Proof.
    unfold subset. intros wfP wfQ.
    split. apply tnum_union_wellformed; auto.
    split;
      unfold tnum.wellformed; unfold ingamma; unfold tnum.ith_m; unfold tnum.ith_v;
      intros x igx;
    unfold tnum_union; intros i hidx;
      specialize (wfP i hidx); specialize (wfQ i hidx); specialize (igx i hidx);
      rewrite tnum.ith_m_simplify2;
      rewrite tnum.ith_v_simplify2;
        unwrap_bvec_ops;
        destruct (bvec_ith (tnum.m P) hidx);
        destruct (bvec_ith (tnum.m Q) hidx);
        try rewrite_if_holds wfP;
        try rewrite_if_holds wfQ;
        destruct (bvec_ith (tnum.v P) hidx);
        destruct (bvec_ith (tnum.v Q) hidx);
        repeat simplify_bit_ops; try easy.
  Qed.

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

  Definition le_1_Sn {n} : 1 <= S n. lia. Qed.

  (* Compared to bvec_mul_without_rshift, written with rshift in
   * order to make the proof of tnum_mul easier.
   *)
  (* TODO test *)
  (* TODO move; rewrite bvec_mul based on this if successful (or prove the equivalence). *)
  Section bvec_mul_with_rshift.
    (* Written in the style of tnum_mul_iter for the ease of proving. *)
    Definition bvec_mul_iter {n} (input : @bmir.t n) :=
      let a := bmir.a input in let b := bmir.b input in let acc := bmir.acc input in
      let nxt_acc := match bvec_lsb a with
                     | one => bvec_add acc b
                     | zero => acc
                     end in
      let nxt_a := bvec_rshift a le_1_Sn in
      let nxt_b := bvec_lshift b le_1_Sn in
      bmir.cons nxt_a nxt_b nxt_acc.

    Definition bvec_mul {n} (a b : bvec (S n)) :=
      bmir.acc (Nat.iter (S n) bvec_mul_iter (bmir.cons a b (zerovec (S n)))).
  End bvec_mul_with_rshift.

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
    let nxt_a := tnum_rshift a le_1_Sn in
    let nxt_b := tnum_lshift b le_1_Sn in
    tmir.cons nxt_a nxt_b nxt_acc.

  Lemma tnum_mul_iter_wellformed {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.acc (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.acc (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfP wfQ wfA igx igy iga.

    unfold tnum_mul_iter.
    unfold tmir.acc. unfold tmir.a. unfold tmir.b.

    destruct (bvec_lsb (tnum.v P)).
    - destruct (bvec_lsb (tnum.m P)). auto.
      apply tnum_union_wellformed; auto. apply tnum_add_wellformed. auto.
    - apply tnum_add_wellformed. auto.
  Qed.

  (* TODO rem if unused *)
  (* TODO maybe merge with tnum_mul_iter_wellformed to avoid duplication *)
  (* TODO already included in tnum_mul_iter_sound_nxt_a? *)
  Lemma tnum_mul_iter_wellformed_nxt_a {n} (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    let tout := tmir.a (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout.
  Proof.
    (* TODO *)
  Admitted.

  Lemma tnum_mul_iter_wellformed_nxt_b {n} (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    let tout := tmir.b (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout.
  Proof.
    (* TODO *)
  Admitted.
  
  Lemma ltSi_imp_lt0 {i} {n} (hidx : S i < S n) : 0 < S n.
    lia.
  Qed.

  Lemma tnum_mul_iter_sound_nxt_a {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.a (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.a (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed_nxt_a P Q A).
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

    apply tnum_rshift_sound; auto.
  Qed.

  (* TODO try to combine? Same except for the final shift. *)
  Lemma tnum_mul_iter_sound_nxt_b {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.b (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.b (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed_nxt_b P Q A).
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

    apply tnum_lshift_sound; auto.
  Qed.

  (* TODO comment: prove that tnum_mul_iter abstracts bvec_mul_iter *)
  (* TODO DOC missing in the input: A is partial prod of P and Q; but that's not an issue; interesting. *)
  Lemma tnum_mul_iter_sound {n} x y a (P Q A : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q -> tnum.wellformed A ->
    ingamma x P -> ingamma y Q -> ingamma a A ->
    let bout := bmir.acc (bvec_mul_iter (bmir.cons x y a)) in
    let tout := tmir.acc (tnum_mul_iter (tmir.cons P Q A)) in
    tnum.wellformed tout /\ ingamma bout tout.
  Proof.
    assert (hwf := tnum_mul_iter_wellformed x y a P Q A).
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
      destruct (bvec_ith x (PeanoNat.Nat.lt_0_succ n)); auto. (* TODO later? *)
      (* Direct application of tnum_union_sound results in absurd goals,
       * solving which would result in unnecessary assert, pose, etc.
       *)
      apply tnum_union_sound_l; auto. apply tnum_add_wellformed; auto.
      apply tnum_union_sound_r; auto. apply tnum_add_wellformed; auto.
      apply tnum_add_sound; auto.
  Qed.

  (* TODO move to tnum and name tnum.zero *)
  Definition zerotnum n := tnum.cons n (zerovec n) (zerovec n).

  Definition tnum_mul {n} (a b : tnum.t (S n)) :=
      tmir.acc (Nat.iter (S n) tnum_mul_iter (tmir.cons a b (zerotnum (S n)))).

  Lemma tnum_mul_wellformed {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    let R := tnum_mul P Q in let r := bvec_mul x y in
    tnum.wellformed R.
  Proof.
    (* TODO *)
  Admitted.

  (* TODO move *)
  Lemma zero_wellformed {SIZE} : tnum.wellformed (zerotnum SIZE).
    (* TODO *)
  Admitted.

  (* TODO move *)
  Lemma zero_ingamma {SIZE} : ingamma (zerovec SIZE) (zerotnum SIZE).
    (* TODO *)
  Admitted.

  (* TODO rem if unused *)
  Lemma tnum_mul_loop_wellformed_all {n} (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall c,
      let R := Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n))) in
      tnum.wellformed (tmir.a R) /\ tnum.wellformed (tmir.b R) /\
        tnum.wellformed (tmir.acc R).
  Proof.
    (* TODO *)
  Admitted.

  Lemma tnum_mul_loop_sound_nxt_a {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    forall c,
      let r := bmir.a (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let R := tmir.a (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      (* tnum.wellformed R /\ (* TODO *) *)
      ingamma r R.
  Proof.
    unfold tnum.wellformed. unfold ingamma. unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfP wfQ igx igy.

    (*
    unfold Nat.iter. unfold nat_rect.
    apply tnum_mul_iter_sound.
     *)

    induction c.
    - simpl. auto.
    -
      pose(wfall := tnum_mul_loop_wellformed_all P Q).
      unfold Nat.iter. unfold nat_rect.
      unfold Nat.iter in wfall. unfold nat_rect in wfall.
(*
      pose(hsound_nxt_a := tnum_mul_iter_sound_nxt_a x y (zerovec (S n)) P Q (zerotnum (S n))).
      unfold Nat.iter in hsound_nxt_a. unfold nat_rect in hsound_nxt_a.
      apply hsound_nxt_a.
 *)
      (* TODO *)
  Admitted.

  Lemma tnum_mul_loop_sound_nxt_b {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    forall c,
      let r := bmir.b (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let R := tmir.b (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      (* tnum.wellformed R /\ (* TODO *) *)
      ingamma r R.
  Proof.
    (* TODO *)
  Admitted.

  (* TODO doc: this is needed because in tnum_mul_sound, both the width and the oter count are (S n). I want to induct on the iter count, but that would cause an induction on the width as well. But the width isn't meant to change between iterations. *)
  (* TODO avoid this intermediate lemma if no induction is happening inside. *)
  Lemma tnum_mul_loop_sound {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    forall c,
      let r := bmir.acc (Nat.iter c bvec_mul_iter (bmir.cons x y (zerovec (S n)))) in
      let R := tmir.acc (Nat.iter c tnum_mul_iter (tmir.cons P Q (zerotnum (S n)))) in
      (* tnum.wellformed R /\ (* TODO *) *)
      ingamma r R.
  Proof.
    unfold tnum.wellformed. unfold ingamma. unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfP wfQ igx igy.

    induction c.
    - simpl. auto.
    -
      pose(wfall := tnum_mul_loop_wellformed_all P Q).
      unfold Nat.iter. unfold nat_rect.
      unfold Nat.iter in wfall. unfold nat_rect in wfall.

      apply tnum_mul_iter_sound.
      apply wfall; auto. apply wfall; auto. apply wfall; auto.

      apply tnum_mul_loop_sound_nxt_a; auto.
      apply tnum_mul_loop_sound_nxt_b; auto.

      revert IHc. unfold Nat.iter. unfold nat_rect. intro IHc.
      unfold ingamma.
      apply IHc.
  Qed.

  Lemma tnum_mul_sound {n} x y (P Q : tnum.t (S n)) :
    tnum.wellformed P -> tnum.wellformed Q ->
    ingamma x P -> ingamma y Q ->
    let R := tnum_mul P Q in let r := bvec_mul x y in
    tnum.wellformed R /\ ingamma r R.
  Proof.
    assert (hwf := tnum_mul_wellformed x y P Q).
    revert hwf.

    unfold tnum.wellformed. unfold ingamma. unfold tnum.ith_m. unfold tnum.ith_v.
    intros hwf wfP wfQ igx igy.

    split. auto. (* Well-formedness *)
    apply tnum_mul_loop_sound; auto. (* Soundness *)
  Qed.
End linux_tnum_multiplication.
