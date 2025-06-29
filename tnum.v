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

Definition SIZE := 64. (* TODO use n *)
Definition v64 := Vector.t bit SIZE.
Definition v64_ith (v : v64) {i} (hidx : i < SIZE) :=
  Vector.nth v (Fin.of_nat_lt hidx).

Axiom v64_add : v64 -> v64 -> v64.

Axiom v64_and : v64 -> v64 -> v64.
Axiom v64_and_rel : forall v1 v2 v3, v3 = v64_and v1 v2 -> forall i (hidx : i < SIZE), v64_ith v3 hidx = bit_and (v64_ith v1 hidx) (v64_ith v2 hidx).

Axiom v64_neg : v64 -> v64.
Axiom v64_neg_rel : forall v1 v2, v2 = v64_neg v1 -> forall i (hidx : i < SIZE), v64_ith v2 hidx = bit_not (v64_ith v1 hidx).

Axiom v64_or : v64 -> v64 -> v64.
Axiom v64_or_rel : forall v1 v2 v3, v3 = v64_or v1 v2 -> forall i (hidx : i < SIZE), v64_ith v3 hidx = bit_or (v64_ith v1 hidx) (v64_ith v2 hidx).

Axiom v64_xor : v64 -> v64 -> v64.
Axiom v64_xor_rel : forall v1 v2 v3, v3 = v64_xor v1 v2 -> forall i (hidx : i < SIZE), v64_ith v3 hidx = bit_xor (v64_ith v1 hidx) (v64_ith v2 hidx).

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
Fixpoint v64_incarry (x y : v64) {i} (hidx : i < SIZE) : bit :=
  match i return i < SIZE -> bit with
  | 0 => fun _ => zero
  | S i' => fun hidx => let a := v64_ith x (ltprv hidx) in
                        let b := v64_ith y (ltprv hidx) in
                        let cin := v64_incarry x y (ltprv hidx) in
                        bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin)
  end hidx.

(* Takes away the convoy pattern, making some upcoming proofs simpler *)
Lemma v64_incarry_Si (x y : v64) {i} (hidx : S i < SIZE) :
  v64_incarry x y hidx = let a := v64_ith x (ltprv hidx) in
                          let b := v64_ith y (ltprv hidx) in
                          let cin := v64_incarry x y (ltprv hidx) in
                          bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin).
Proof.
  auto.
Qed.

Axiom v64_fulladd_result : forall x y [i] (hidx : i < SIZE), v64_ith (v64_add x y) hidx = bit_xor (v64_incarry x y hidx) (bit_xor (v64_ith x hidx) (v64_ith y hidx)).

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t := cons (v : v64) (m : v64) : t.

  Definition v P := match P with cons v _ => v end.
  Definition m P := match P with cons _ m => m end.

  Definition ith_v (tn : t) {i} (hidx : i < SIZE) := v64_ith (v tn) hidx.
  Definition ith_m (tn : t) {i} (hidx : i < SIZE) := v64_ith (m tn) hidx.

  Definition wellformed (tn : t) := forall {i} (hidx : i < SIZE), v64_ith (m tn) hidx = one -> v64_ith (v tn) hidx = zero.
  (*
  Definition wellformed_hari (tn : t) := v64_and (v tn) (m tn) = zero64. (* TODO prove my wellformed <-> wellformed_hari *)
   *)

  Lemma ith_m_simplify n1 n2 i (hidx : i < SIZE) : ith_m (cons n1 n2) hidx = v64_ith n2 hidx.
    unfold ith_m. simpl. reflexivity.
  Qed.

  Lemma ith_v_simplify n1 n2 i (hidx : i < SIZE) : ith_v (cons n1 n2) hidx = v64_ith n1 hidx.
    unfold ith_v. simpl. reflexivity.
  Qed.
End tnum.

Definition ingamma (x : v64) (T : tnum.t) : Prop :=
  forall i (hidx : i < SIZE),
    tnum.ith_m T hidx = zero -> v64_ith x hidx = tnum.ith_v T hidx.

(* Based on Harishankar et al. *)
(* TODO prove member <-> ingamma *)
Definition member (x : v64) (T : tnum.t) : Prop :=
  v64_and x (v64_neg (tnum.m T)) = tnum.v T.

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

  Definition tnum_ith_chi P Q [i] (hidx : i < SIZE) :=
    let sv := v64_add (tnum.v P) (tnum.v Q) in
    let sm := v64_add (tnum.m P) (tnum.m Q) in
    let sig := v64_add sv sm in
    let chi := v64_xor sig sv in
    v64_ith chi hidx.

  Definition tnum_add P Q :=
    let sv := v64_add (tnum.v P) (tnum.v Q) in
    let sm := v64_add (tnum.m P) (tnum.m Q) in
    let sig := v64_add sv sm in
    let chi := v64_xor sig sv in
    let eta := v64_or chi (v64_or (tnum.m P) (tnum.m Q)) in
    tnum.cons (v64_and sv (v64_neg eta)) eta.

  (* Why this thin wrapper? Because direct use of `rewrite v64_and_rel` fails to find
   * v1 and v2 automatically.
   *)
  Lemma v64_ith_unwrap_and v1 v2 i (hidx : i < SIZE) :
    v64_ith (v64_and v1 v2) hidx = bit_and (v64_ith v1 hidx) (v64_ith v2 hidx).
  Proof.
    apply v64_and_rel. reflexivity.
  Qed.

  Lemma v64_ith_unwrap_neg v i (hidx : i < SIZE) :
    v64_ith (v64_neg v) hidx = bit_not (v64_ith v hidx).
  Proof.
    apply v64_neg_rel. reflexivity.
  Qed.

  Lemma v64_ith_unwrap_or v1 v2 i (hidx : i < SIZE) :
    v64_ith (v64_or v1 v2) hidx = bit_or (v64_ith v1 hidx) (v64_ith v2 hidx).
  Proof.
    apply v64_or_rel. reflexivity.
  Qed.

  Lemma v64_ith_unwrap_xor v1 v2 i (hidx : i < SIZE) :
    v64_ith (v64_xor v1 v2) hidx = bit_xor (v64_ith v1 hidx) (v64_ith v2 hidx).
  Proof.
    apply v64_xor_rel. reflexivity.
  Qed.

  Ltac unwrap_v64_ops := match goal with
                           _ => repeat rewrite v64_ith_unwrap_and;
                                repeat rewrite v64_ith_unwrap_neg;
                                repeat rewrite v64_ith_unwrap_or;
                                repeat rewrite v64_ith_unwrap_xor
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
  Lemma helper14 v1 v2 {i} (hidx : i < SIZE) :
    v64_ith (v64_xor (v64_add v1 v2) v1) hidx = bit_xor (v64_ith v2 hidx) (v64_incarry v1 v2 hidx).
  Proof.
    unwrap_v64_ops.
    rewrite v64_fulladd_result with (x := v1) (y := v2).
    destruct (v64_ith v1 hidx); destruct (v64_ith v2 hidx); destruct (v64_incarry v1 v2 hidx); auto.
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
  Lemma helper32 P Q :
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
      unwrap_v64_ops; unfold tnum.ith_m;
      rewrite v64_fulladd_result;
      unfold v64_incarry;
      destruct (v64_ith (tnum.m P) hidx);
      destruct (v64_ith (tnum.m Q) hidx);
      repeat simplify_bit_ops; split; try easy.
  Qed.

  (* TODO rename *)
  Ltac crush10 := match goal with
                    [ H : ?x = ?x -> zero = one |- _ ] => specialize (H eq_refl); easy
                  end.

  Lemma helper66 P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (v64_incarry (tnum.m P) (tnum.m Q) hidx)
        (v64_incarry (tnum.v P) (tnum.v Q) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold v64_incarry. auto.
    - intros hidx.
      repeat rewrite v64_incarry_Si. simpl.
      repeat rewrite v64_fulladd_result.

      specialize (IHi (ltprv hidx)).
      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (v64_ith (tnum.m P) (ltprv hidx));
        destruct (v64_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (v64_ith (tnum.v P) (ltprv hidx));
        destruct (v64_ith (tnum.v Q) (ltprv hidx));

        destruct (v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  (* Interesting: proving only one side would seem easier, but it is actually
   * difficult, if not impossible. I suppose it is because that way the
   * induction hypothesis becomes weaker.
   *)
  Lemma helper63 P Q :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall [i] (hidx : i < SIZE),
      bit_and (v64_incarry (tnum.m P) (tnum.m Q) hidx)
        (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
           (v64_add (tnum.m P) (tnum.m Q)) hidx) = zero /\
        bit_and (v64_incarry (tnum.v P) (tnum.v Q) hidx)
          (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
             (v64_add (tnum.m P) (tnum.m Q)) hidx) = zero.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intros wfp wfq.
    induction i.
    - unfold v64_incarry. auto.
    - intros hidx.
      repeat rewrite v64_incarry_Si. simpl.
      repeat rewrite v64_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      specialize (wfp i (ltprv hidx)).
      specialize (wfq i (ltprv hidx)).

      destruct (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        destruct (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
                    (v64_add (tnum.m P) (tnum.m Q)) (ltprv hidx));

        destruct (v64_ith (tnum.m P) (ltprv hidx));
        destruct (v64_ith (tnum.m Q) (ltprv hidx));
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        destruct (v64_ith (tnum.v P) (ltprv hidx));
        destruct (v64_ith (tnum.v Q) (ltprv hidx));

        destruct (v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
  Qed.

  Lemma helper45 x y P Q :
    tnum.wellformed P -> tnum.wellformed Q -> ingamma x P -> ingamma y Q ->
    forall [i] (hidx : S i < SIZE),
      v64_incarry (tnum.m P) (tnum.m Q) hidx = zero ->
      let sv := v64_add (tnum.v P) (tnum.v Q) in
      let sm := v64_add (tnum.m P) (tnum.m Q) in
      v64_incarry sv sm hidx = zero ->
      v64_incarry x y hidx = v64_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed.
    unfold ingamma.
    unfold tnum.ith_m. unfold tnum.ith_v.
    intros wfp wfq igp igq.

    induction i.
    - intro hidx.
      rewrite v64_incarry_Si. simpl.
      repeat rewrite v64_fulladd_result.
      unfold v64_incarry.
      repeat simplify_bit_ops.

      specialize (wfp 0 (ltprv hidx)).
      specialize (wfq 0 (ltprv hidx)).
      specialize (igp 0 (ltprv hidx)).
      specialize (igq 0 (ltprv hidx)).

      destruct (v64_ith (tnum.m P) (ltprv hidx));
        destruct (v64_ith (tnum.m Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;
        destruct (v64_ith (tnum.v P) (ltprv hidx));
        destruct (v64_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy.
    - intro hidx.
      rewrite v64_incarry_Si.
      rewrite v64_incarry_Si with (x := x).
      repeat rewrite v64_incarry_Si with (hidx := hidx).
      repeat rewrite v64_fulladd_result.

      specialize (IHi (ltprv hidx)).

      assert (h66 : bit_and (v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx)) = zero).
      apply helper66; auto.

      assert (h64 : bit_and (v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx))
                      (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
                         (v64_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero /\
                      bit_and (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx))
                        (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
                           (v64_add (tnum.m P) (tnum.m Q)) (ltprv hidx)) = zero).
      apply helper63; auto.


      specialize (wfp (S i) (ltprv hidx)).
      specialize (wfq (S i) (ltprv hidx)).
      specialize (igp (S i) (ltprv hidx)).
      specialize (igq (S i) (ltprv hidx)).

      destruct(v64_incarry (tnum.m P) (tnum.m Q) (ltprv hidx));
        destruct (v64_incarry (v64_add (tnum.v P) (tnum.v Q))
                    (v64_add (tnum.m P) (tnum.m Q)) (ltprv hidx));
        destruct (v64_incarry (tnum.v P) (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;
        destruct (v64_ith (tnum.m P) (ltprv hidx));
        destruct (v64_ith (tnum.m Q) (ltprv hidx));

        try rewrite_if_holds wfp;
        try rewrite_if_holds wfq;
        try rewrite_if_holds igp;
        try rewrite_if_holds igq;
        repeat simplify_bit_ops; try easy;

        destruct (v64_ith (tnum.v P) (ltprv hidx));
        destruct (v64_ith (tnum.v Q) (ltprv hidx));
        repeat simplify_bit_ops; try easy;

        destruct (v64_ith x (ltprv hidx));
        destruct (v64_ith y (ltprv hidx));
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

  Lemma helper33 x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    forall [i] (hidx : i < SIZE),
      tnum.ith_m (tnum_add P Q) hidx = zero ->
      v64_incarry x y hidx = v64_incarry (tnum.v P) (tnum.v Q) hidx.
  Proof.
    unfold tnum.wellformed. unfold ingamma.
    intro H.
    destruct H as (wfp & wfq & igP & igQ).
    destruct i.
    - unfold v64_incarry. auto.
    -
      intros hidx.
      unfold tnum_add.
      rewrite tnum.ith_m_simplify.
      unwrap_v64_ops. repeat rewrite v64_fulladd_result.

      intro H.
      assert (hmp : v64_ith (tnum.m P) hidx = zero). revert H.
      destruct (v64_ith (tnum.m P) hidx);
        repeat simplify_bit_ops; try easy.

      assert (hmq : v64_ith (tnum.m Q) hidx = zero). revert H.
      destruct (v64_ith (tnum.m Q) hidx);
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

  Lemma wellformed_general inval mu :
    forall [i] (hidx : i < SIZE),
      v64_ith mu hidx = one -> v64_ith (v64_and inval (v64_neg mu)) hidx = zero.
  Proof.
    intros i hidx H.
    unwrap_v64_ops. rewrite H. simpl.
    destruct (v64_ith inval hidx); auto.
  Qed.

  Lemma tnum_add_wellformed P Q :
    tnum.wellformed P /\ tnum.wellformed Q -> tnum.wellformed (tnum_add P Q).
  Proof.
    unfold tnum.wellformed.
    intro H.
    unfold tnum_add.
    apply wellformed_general.
  Qed.

  Lemma tnum_add_sound x y P Q :
    tnum.wellformed P /\ tnum.wellformed Q /\ ingamma x P /\ ingamma y Q ->
    tnum.wellformed (tnum_add P Q) /\
      ingamma (v64_add x y) (tnum_add P Q).
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

    rewrite v64_ith_unwrap_or.
    unwrap_v64_ops. repeat rewrite v64_fulladd_result.
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
