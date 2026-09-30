(* Boilerplate copied from Software Foundations Verifiable C *)
Require Import VST.floyd.proofauto.
Require Import trirocq.Verification.tnumSplitDotC.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

From Stdlib Require Import
  Arith
  ZArith.

From trirocq Require Import
  BitVector
  BitSub
  Tnum
  TnumAdd.

Module Ztnum.
  (**
   * Avoiding modulo for simplicity; operations and proofs
   * will have to enforce it.
   *)
  Record t := new { value : Z; mask : Z }.

  Lemma eq_by_v_m (a b : t) : value a = value b -> mask a = mask b -> a = b.
    destruct a, b. cbn. intros. subst. reflexivity.
  Qed.

  Definition add (a b : t) : t :=
    let av := value a in
    let am := mask a in
    let bv := value b in
    let bm := mask b in

    let sm := (am + bm) mod Int64.modulus in
    let sv := (av + bv) mod Int64.modulus in
    let sigma := (sm + sv) mod Int64.modulus in
    let chi := Z.lxor sigma sv in
    let mu := Z.lor (Z.lor chi am) bm in
    new (Z.land sv ((Z.lnot mu) mod Int64.modulus)) mu.

  Definition of_tnum {SIZE} (a : tnum.t SIZE) :=
    new (Z.of_nat (tnum.v a)) (Z.of_nat (tnum.v a)).

  Coercion of_tnum : tnum.t >-> t.

  Lemma modulus_matches : Int64.modulus = 2 ^ 64. auto. Qed.

  (* TODO Prove inside theories/BitVector.v;
   * rebase on top of dev and remove these stubs.
   *)
  Section bvec_stubs.
    Context {SIZE : nat}.

    Lemma bvec_denote_bvec_and (a b : bvec SIZE) :
      bvec_denote (bvec_and a b) = Nat.land (bvec_denote a) (bvec_denote b).
    Admitted.

    Lemma bvec_denote_bvec_neg (a : bvec SIZE) :
      bvec_denote (bvec_neg a) = Nat.lnot (bvec_denote a) SIZE.
    Admitted.
  End bvec_stubs.

  Lemma add_correct (a b : Ztnum.t) (p q : tnum.t 64) :
    Ztnum.value a = Z.of_nat (bvec_denote (tnum.v p)) ->
    Ztnum.mask a  = Z.of_nat (bvec_denote (tnum.m p)) ->
    Ztnum.value b = Z.of_nat (bvec_denote (tnum.v q)) ->
    Ztnum.mask b  = Z.of_nat (bvec_denote (tnum.m q)) ->
    add a b = tnum_add p q. (* TODO mod *)
  Proof.
    intros ave ame bve bme.
    unfold add, tnum_add.

    Set Printing Coercions.
    unfold of_tnum.

    (* TODO distribute Z.of_nat in the RHS and rewrite using ave, ame, etc. *)
    simpl.
    assert (bvec_denote_bvec_and :
             forall SIZE (a b : bvec SIZE), bvec_denote (bvec_and a b) = Nat.land a b). admit.


    rewrite bvec_denote_bvec_and.

    assert (Nat2Z_land : forall x y,
               Z.of_nat (Nat.land x y) = Z.land (Z.of_nat x) (Z.of_nat y)).
    admit.

    rewrite !Nat2Z_land.
    rewrite !bvec_add_correct_Z.
    rewrite <- ave, <- bve.
    change (2 ^ (Z.of_nat 63 + 1)) with Int64.modulus.

    apply eq_by_v_m; cbn.
    -
      assert (TODO99 : forall a x y, x = y -> Z.land a x = Z.land a y).
      admit.

      match goal with
      | [ |- Z.land ?a ?x = Z.land ?a ?y ] => apply (TODO99 a x y)
      end.

      rewrite bvec_denote_bvec_neg.

      assert (bvec_denote_bvec_or : forall SIZE (a b : bvec SIZE),
                 bvec_denote (bvec_or a b) = Nat.lor (bvec_denote a) (bvec_denote b)).
      admit.

      assert (bvec_denote_bvec_xor : forall SIZE (a b : bvec SIZE),
                 bvec_denote (bvec_xor a b) = Nat.lxor (bvec_denote a) (bvec_denote b)).
      admit.

      rewrite !bvec_denote_bvec_or.
      rewrite bvec_denote_bvec_xor.
      rewrite !bvec_add_correct.

      Search (Nat.lnot _ _).
      (* TODO REM UNUSED *)
      (* rewrite Nat.lnot_sub_low. *)
      unfold Nat.lnot.

      (*
      assert (TODO91 : forall x : Z,
                 0 <= x < Int64.modulus ->
                 Z.lnot x mod Int64.modulus =
                   Z.of_nat (Nat.lxor (Z.of_nat x) (Nat.ones 64))).

      (-x - 1) mod Int64.modulus = (Z.of_nat (Nat.ones 64) - x) mod Int64.modulus).



      rewrite Z.lnot_eq_pred_opp.
      Search (Z.of_nat (Z.ones _)).
      rewrite Nat2Z.inj_sub.
       *)

      assert (Nat2Z_lxor : forall x y,
                 Z.of_nat (Nat.lxor x y) = Z.lxor (Z.of_nat x) (Z.of_nat y)).
      admit.

      assert (Nat2Z_lor : forall x y,
                 Z.of_nat (Nat.lor x y) = Z.lor (Z.of_nat x) (Z.of_nat y)).
      admit.

      rewrite Nat2Z_lxor.
      rewrite !Nat2Z_lor.
      rewrite Nat2Z_lxor.
      rewrite Nat2Z.inj_mod.
      rewrite Nat2Z.inj_add.
      rewrite !Nat2Z.inj_mod.
      rewrite !Nat2Z.inj_add.
      repeat rewrite <- ave, <- bve.
      repeat rewrite <- ame, <- bme.

      assert (TODO91 : forall x y : Z,
                 0 <= x < Int64.modulus ->
                 0 <= y < Int64.modulus ->
                 x = y ->
                 Z.lnot x mod Int64.modulus =
                   Z.lxor y (Z.of_nat (Nat.ones 64))).
      admit.
      apply TODO91.

      change Int64.modulus with (2 ^ 64).

(*

      rewrite Nat.add_mod. (* TODO use Div0.add_mod *)
      Search ((_ mod _ + _ mod _) mod _).

      rewrite !Nat2Z.inj_mod.
      rewrite !Nat2Z.inj_add.
 *)

      assert (TODO91 : forall x : Z,
                 0 <= x < Int64.modulus ->
                 (-x - 1) mod Int64.modulus = (Z.of_nat (Nat.ones 64) - x) mod Int64.modulus).

      change Int64.modulus with (2 ^ 64).
      intros.
      replace ((-x - 1) mod (2 ^ 64)) with (((2 ^ 64) - x) mod (2 ^ 64)).

      Check Z.mod_add.
      Search (_ - _ = _).


      admit.
      rewrite TODO91.
      change Int64.modulus with (2 ^ 64).
      replace (Z.of_nat (2 ^ 64)) with (2 ^ 64).
      reflexivity.

      rewrite Nat2Z.inj_pow. lia.



Check Z.ones_equiv.

End Ztnum.

Definition tnum_add_split_m_Z (av am bv bm : Z) : Z :=
  Ztnum.mask (Ztnum.add (Ztnum.new av am) (Ztnum.new bv bm)).

(* TODO no Uint64, Vulong, etc. Make sure this is okay. *)
Definition tnum_add_m_spec : ident * funspec :=
  DECLARE _tnum_add_m
    WITH av : Z, am : Z, bv : Z, bm : Z
                                        PRE [ tulong, tulong, tulong, tulong ]
                                        PROP ( 0 <= av <= Int64.max_unsigned;
                                               0 <= am <= Int64.max_unsigned;
                                               0 <= bv <= Int64.max_unsigned;
                                               0 <= bm <= Int64.max_unsigned
                                        )
                                        PARAMS (Vlong (Int64.repr av);
                                                Vlong (Int64.repr am);
                                                Vlong (Int64.repr bv);
                                                Vlong (Int64.repr bm))
                                        GLOBALS ()
                                        SEP ()
                                        POST [ tulong ]
                                        EX mu : Z,  PROP (mu = tnum_add_split_m_Z av am bv bm)
                                        RETURN (Vlong (Int64.repr mu))
                                        SEP ().

Definition Gprog := [ tnum_add_m_spec ].

(* See https://softwarefoundations.cis.upenn.edu/vc-current/Verif_sumarray.html
 * for an explanation of semax_body.
 * f_tnum_add is the body of tnum_add parsed by ClightGen.
 *)
Lemma body_tnum_add_spec : semax_body Vprog Gprog f_tnum_add_m tnum_add_m_spec.
Proof.
  start_function.
  repeat forward.
  Exists (tnum_add_split_m_Z av am bv bm).
  entailer!.
  unfold tnum_add_split_m_Z. simpl.

  repeat rewrite <- or64_repr.
  unfold Int64.xor.
  autorewrite with norm.

  rewrite !Int64.unsigned_repr_eq.

  replace ((am + bm + (av + bv)) mod Int64.modulus)
    with
    (((am + bm) mod Int64.modulus + (av + bv) mod Int64.modulus) mod Int64.modulus).
  reflexivity.

  rewrite <- Z.add_mod. reflexivity. easy.
Qed.
