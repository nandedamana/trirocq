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

Definition bvec SIZE := Vector.t bit SIZE.
Definition bvec_ith {SIZE} (v : bvec SIZE) {i} (hidx : i < SIZE) :=
  Vector.nth v (Fin.of_nat_lt hidx).

Axiom bvec_add : forall {SIZE}, bvec SIZE -> bvec SIZE -> bvec SIZE.

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

Require Import Lia.
Lemma ltprv {i} {n} : S i < n -> i < n.
  lia.
Qed.

Definition p_from_pltq {p q} (pltq : p < q) := p.

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

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t SIZE := cons (v : bvec SIZE) (m : bvec SIZE).

  Definition v {SIZE} (P : t SIZE) := match P with cons _ v _ => v end.
  Definition m {SIZE} (P : t SIZE) := match P with cons _ _ m => m end.

  Definition ith_v {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (v tn) hidx.
  Definition ith_m {SIZE} (tn : t SIZE) {i} (hidx : i < SIZE) := bvec_ith (m tn) hidx.

  Definition wellformed {SIZE} (tn : t SIZE) :=
    forall {i} (hidx : i < SIZE), bvec_ith (m tn) hidx = one -> bvec_ith (v tn) hidx = zero.
  (*
    Definition wellformed_hari (tn : t) := bvec_and (v tn) (m tn) = zero64. (* TODO prove my wellformed <-> wellformed_hari *)
   *)

  Lemma ith_m_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_m (cons SIZE n1 n2) hidx = bvec_ith n2 hidx.
    unfold ith_m. simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify {SIZE} n1 n2 i (hidx : i < SIZE) : ith_v (cons SIZE n1 n2) hidx = bvec_ith n1 hidx.
    unfold ith_v. simpl. reflexivity.
  Qed.
End tnum.

Definition ingamma {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) : Prop :=
  forall i (hidx : i < SIZE),
    tnum.ith_m T hidx = zero -> bvec_ith x hidx = tnum.ith_v T hidx.

(* Based on Harishankar et al. *)
(* TODO prove member <-> ingamma *)
Definition member {SIZE} (x : bvec SIZE) (T : tnum.t SIZE) : Prop :=
  bvec_and x (bvec_neg (tnum.m T)) = tnum.v T.

(* On my own *)
(* We need to define otnum addition with the following properties:
 * 1. Soundness: the result of adding abstract numbers P and Q include the results
 *    of adding any concrete p and q (written less formally for simplicity).
 * 2. TODO optimality.
 *)

Section linux_tnum_addition.
  (* The tnum addition routine in the kernel consists of half a dozen non-obvious steps.
   * On the other hand, otnum addition is easier to reason about. Here we try to
   * establish the relationship between the Linux tnum addition and our otnum addition.
   * Once this is done, the correctness proof for otnum addition automatically
   * becomes the correctness proof for Linux tnum addition.
   *)

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

  (* Why this thin wrapper? Because direct use of `rewrite bvec_and_rel` fails to find
   * v1 and v2 automatically.
   *)
  Lemma bvec_ith_unwrap_and {SIZE} v1 v2 i (hidx : i < SIZE) :
    bvec_ith (bvec_and v1 v2) hidx = bit_and (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof.
    apply bvec_and_rel.
  Qed.

  Lemma bvec_ith_unwrap_neg {SIZE} v i (hidx : i < SIZE) :
    bvec_ith (bvec_neg v) hidx = bit_not (bvec_ith v hidx).
  Proof.
    apply bvec_neg_rel.
  Qed.

  Lemma bvec_ith_unwrap_or {SIZE} v1 v2 i (hidx : i < SIZE) :
    bvec_ith (bvec_or v1 v2) hidx = bit_or (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof.
    apply bvec_or_rel.
  Qed.

  Lemma bvec_ith_unwrap_xor {SIZE} v1 v2 i (hidx : i < SIZE) :
    bvec_ith (bvec_xor v1 v2) hidx = bit_xor (bvec_ith v1 hidx) (bvec_ith v2 hidx).
  Proof.
    apply bvec_xor_rel.
  Qed.

  Ltac unwrap_bvec_ops := match goal with
                           _ => repeat rewrite bvec_ith_unwrap_and;
                                repeat rewrite bvec_ith_unwrap_neg;
                                repeat rewrite bvec_ith_unwrap_or;
                                repeat rewrite bvec_ith_unwrap_xor
                         end.

  Lemma bit_xor_self x : bit_xor x x = zero.
    destruct x; auto.
  Qed.

  Ltac rewrite_if_holds H :=
    match type of H with
    | ?b = ?b -> _ => rewrite H
    end.

  (* TODO rename *)
  (* Unused, but still an interesting observation. *)
  Lemma helper14 {SIZE} v1 v2 {i} (hidx : i < SIZE) :
    bvec_ith (bvec_xor (bvec_add v1 v2) v1) hidx = bit_xor (bvec_ith v2 hidx) (bvec_incarry v1 v2 hidx).
  Proof.
    unwrap_bvec_ops.
    rewrite bvec_fulladd_result with (x := v1) (y := v2).
    destruct (bvec_ith v1 hidx); destruct (bvec_ith v2 hidx); destruct (bvec_incarry v1 v2 hidx); auto.
  Qed.

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

  Ltac simplify_bit_ops :=
    try rewrite bit_and_left_zero;
    try rewrite bit_and_right_zero;
    try rewrite bit_and_left_one;
    try rewrite bit_and_right_one;
    try rewrite bit_or_left_zero;
    try rewrite bit_or_right_zero;
    try rewrite bit_or_left_one;
    try rewrite bit_or_right_one;
    try rewrite bit_xor_left_zero;
    try rewrite bit_xor_right_zero;
    unfold bit_not.

  Ltac destruct_some_x_eq_some_y := match goal with
                                      [ |- Some ?x = Some _ -> _ ] => destruct x
                                    end.

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

  (* TODO rename *)
  Ltac crush10 := match goal with
                    [ H : ?x = ?x -> zero = one |- _ ] => specialize (H eq_refl); easy
                  end.

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

      destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (bvec_ith (tnum.m P) (ltprv hidx));
        destruct (bvec_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (bvec_ith (tnum.v P) (ltprv hidx));
        destruct (bvec_ith (tnum.v Q) (ltprv hidx));

        destruct (bvec_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
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
        destruct (bvec_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
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

  Lemma bit_xor_x_y_zero x y : bit_xor x y = zero -> x = y.
    intros. destruct x; destruct y; auto.
  Qed.

  Lemma bit_xor_x_y_z_y x y z : bit_xor x (bit_xor y z) = y -> bit_xor x z = zero.
    intros. destruct x; destruct y; destruct z; easy.
  Qed.

  Lemma bit_or_zero_zero x y : bit_or x y = zero -> x = zero /\ y = zero.
    intros. destruct x; destruct y; auto.
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

  Lemma tnum_add_sound {SIZE} x y (P Q : tnum.t SIZE) :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_add P Q) /\
      ingamma (bvec_add x y) (tnum_add P Q).
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.

    pose (H'1 := helper33 x y P Q H).

    unfold tnum.ith_m in H. (* TODO rename *)
    destruct H as (wf1 & wf2 & igP & igQ).

    split. apply tnum_add_wellformed; auto.
    
    pose (H'2 := helper32 P Q wf1 wf2). unfold tnum.ith_m in H'2. (* TODO rename *)
    unfold ingamma.

    intros i hidx rmskz.

    specialize (H'2 i hidx rmskz) as (xmskz & ymskz & cinmskz).
    specialize (H'1 i hidx rmskz). (* TODO rename; TODO useless? *)
    revert rmskz.

    revert cinmskz.

    unfold tnum_add.
    rewrite tnum.ith_m_simplify.
    rewrite tnum.ith_v_simplify.

    rewrite bvec_ith_unwrap_or.
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
End linux_tnum_addition.
