From trirocq.Z Require Import
  Bit
  BitVector
  Tnum.

From Stdlib Require Import Lia.

(** printing < %\texttt{<}% *)

Section tnum_union.
  Definition tnum_union {SIZE} (P Q : tnum.t SIZE) :=
    let v := bvec_and (tnum.v P) (tnum.v Q) in
    let m := bvec_or (bvec_or (bvec_xor (tnum.v P) (tnum.v Q)) (tnum.m P)) (tnum.m Q) in
    tnum.cons SIZE (bvec_and v (bvec_neg m)) m.

  Lemma tnum_union_wellformed {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed (tnum_union P Q).
  Proof.
    unfold tnum_union.
    intros i hi.
    cbn.
    unwrap_bvec_ops.
    repeat destruct (bvec_ith _ _); easy.
    assumption.
  Qed.

  Lemma tnum_union_sound {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    let U := tnum_union P Q in
    tnum.wellformed U /\ subset P U /\ subset Q U.
  Proof.
    unfold subset. intros wfP wfQ.
    split. apply tnum_union_wellformed; auto.
    unfold tnum.wellformed; unfold ingamma.
    split;
      unfold ingamma, tnum.ith_m, tnum.ith_v; cbn;
      intros x igx i hi;
      unwrap_bvec_ops;
      specialize (wfP i); specialize (wfQ i); specialize (igx i);
      repeat destruct (bvec_ith (tnum.m _));
      try rewrite_if_holds wfP;
      try rewrite_if_holds wfQ; cbn; try easy;
      repeat destruct (bvec_ith (tnum.v _));
      cbn; try easy; try bool_imp_easy;
      auto.
  Qed.

  Definition concrete_union_element {SIZE} (P Q : tnum.t SIZE) :=
    { x | ingamma x P \/ ingamma x Q }.

  (* NOTE: x and y can be both from P or Q *)
  Lemma tnum_union_optimal {SIZE} (P Q : tnum.t SIZE) :
    tnum.wellformed P -> tnum.wellformed Q ->
    forall i, i < SIZE ->
      tnum.ith_m (tnum_union P Q) i = true ->
      exists (x y : concrete_union_element P Q),
        bvec_ith (proj1_sig x) i <> bvec_ith (proj1_sig y) i.
  Proof.
    unfold tnum.wellformed, tnum.ith_m.
    intros wfp wfq i hi ithm.

    unfold tnum_union in ithm. simpl in ithm.
    repeat rewrite bvec_or_rel in ithm.
    repeat rewrite bvec_xor_rel in ithm.

    specialize (wfp i hi).
    specialize (wfq i hi).

    destruct (bvec_ith (tnum.m P) i) eqn : pmi;
      destruct (bvec_ith (tnum.m Q) i) eqn : qmi.
    - (* P.m[i] = Q.m[i] = 1 *)

      (* Just reuse the proof from the last case. *)
      (* Take P.v as x *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (tnum.v P) (or_introl (ingamma_value P))).

      (* Take (P.v | P.m) as y *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (bvec_or (tnum.v P) (tnum.m P)) (or_introl (ingamma_value_bitor_mask P))).

      simpl.
      revert ithm.
      rewrite bvec_or_rel.
      rewrite pmi. rewrite wfp; easy.
    - (* P.m[i] = 1, Q.m[i] = 0 *)

      (* Take P.v as x *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (tnum.v P) (or_introl (ingamma_value P))).

      (* Take (P.v | P.m) as y *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (bvec_or (tnum.v P) (tnum.m P)) (or_introl (ingamma_value_bitor_mask P))).

      simpl.
      revert ithm.
      rewrite bvec_or_rel.
      rewrite pmi. rewrite wfp; easy.
    - (* P.m[i] = 0, Q.m[i] = 1 *)

      (* Take Q.v as x *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (tnum.v Q) (or_intror (ingamma_value Q))).

      (* Take (Q.v | Q.m) as y *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (bvec_or (tnum.v Q) (tnum.m Q)) (or_intror (ingamma_value_bitor_mask Q))).

      simpl.
      revert ithm.
      rewrite bvec_or_rel.
      rewrite qmi. rewrite wfq; easy.
    - (* P.m[i] = Q.m[i] = 0 *)

      (* Take P.v as x *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (tnum.v P) (or_introl (ingamma_value P))).

      (* Take Q.v as y *)
      exists (exist (fun x => ingamma x P \/ ingamma x Q) (tnum.v Q) (or_intror (ingamma_value Q))).

      simpl.
      revert ithm.
      repeat destruct (bvec_ith (tnum.v _) _); easy.
  Qed.
End tnum_union.
