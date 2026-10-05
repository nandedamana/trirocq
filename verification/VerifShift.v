(* Boilerplate copied from Software Foundations Verifiable C *)
Require Import VST.floyd.proofauto.
Require Import trirocq.Verification.tnumPtrDotC.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

From Stdlib Require Import
  Arith
  ZArith.

From trirocq.Z Require Import
  BitVector
  Tnum.

From trirocq.Verification Require Import
  Common.

Definition u8 := bvec 8.

(* Assuming shift is less than the word size. Without this,
 * 1) It is undefined behavior
 * 2) The proof gets stuck at `shift < Int.unsigned Int64.iwordsize'`
 *)
Definition tnum_lshift_spec : ident * funspec :=
  DECLARE _tnum_lshift
    WITH a : val, sha : share,
         shift : u8,
         r : val, shr : share,
         av : u64, am : u64, rv : u64, rm : u64
    PRE [ tptr(Tstruct _tnum noattr), tuchar, tptr(Tstruct _tnum noattr) ]
    PROP ( readable_share sha; writable_share shr; bvec2Z _ shift < 64 )
    PARAMS (a; Vint (Int.repr (bvec2Z _ shift)); r)
    GLOBALS ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ rv)), Vlong (Int64.repr (bvec2Z _ rm))) r
    )
    POST [ tvoid ]
    EX (sum : tnum.t 64), PROP (sum = tnum_lshift (tnum.cons _ av am) (Z.to_nat (bvec2Z _ shift)))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ (tnum.v sum))), Vlong (Int64.repr (bvec2Z _ (tnum.m sum)))) r
    ).

Definition tnum_rshift_spec : ident * funspec :=
  DECLARE _tnum_rshift
    WITH a : val, sha : share,
         shift : u8,
         r : val, shr : share,
         av : u64, am : u64, rv : u64, rm : u64
    PRE [ tptr(Tstruct _tnum noattr), tuchar, tptr(Tstruct _tnum noattr) ]
    PROP ( readable_share sha; writable_share shr; bvec2Z _ shift < 64 )
    PARAMS (a; Vint (Int.repr (bvec2Z _ shift)); r)
    GLOBALS ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ rv)), Vlong (Int64.repr (bvec2Z _ rm))) r
    )
    POST [ tvoid ]
    EX (sum : tnum.t 64), PROP (sum = tnum_rshift (tnum.cons _ av am) (Z.to_nat (bvec2Z _ shift)))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ (tnum.v sum))), Vlong (Int64.repr (bvec2Z _ (tnum.m sum)))) r
    ).

Definition Gprog := [ tnum_lshift_spec; tnum_rshift_spec ].

Lemma body_tnum_lshift_spec : semax_body Vprog Gprog f_tnum_lshift tnum_lshift_spec.
Proof.
  start_function.

  forward.
  forward.
  entailer!.

  rewrite !Int.unsigned_repr_eq.
  destruct shift as [shift hshift]. cbn.
  rewrite Z.mod_small.
  cbn in H. compute. destruct shift; auto.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.

  forward.
  forward.
  entailer!.
  rewrite !Int.unsigned_repr_eq.
  destruct shift as [shift hshift]. cbn.
  rewrite Z.mod_small. compute. destruct shift; auto.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.

  Exists (tnum_lshift (tnum.cons _ av am) (Z.to_nat (bvec2Z _ shift))).
  repeat forward.

  unfold tnum_lshift. cbn [tnum.v tnum.m].
  rewrite !Int.unsigned_repr_eq.

  replace ((bvec2Z _ shift) mod Int.modulus) with (bvec2Z _ shift).
  rewrite !Int64.lshift_reprbvec.
  apply derives_refl.
  auto. auto. lia. auto. lia.

  rewrite Z.mod_small; auto.
  destruct shift as [shift hshift]. cbn.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.
Qed.

Lemma body_tnum_rshift_spec : semax_body Vprog Gprog f_tnum_rshift tnum_rshift_spec.
Proof.
  start_function.

  forward.
  forward.
  entailer!.

  rewrite !Int.unsigned_repr_eq.
  destruct shift as [shift hshift]. cbn.
  rewrite Z.mod_small.
  cbn in H. compute. destruct shift; auto.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.

  forward.
  forward.
  entailer!.
  rewrite !Int.unsigned_repr_eq.
  destruct shift as [shift hshift]. cbn.
  rewrite Z.mod_small. compute. destruct shift; auto.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.

  Exists (tnum_rshift (tnum.cons _ av am) (Z.to_nat (bvec2Z _ shift))).
  repeat forward.

  unfold tnum_rshift. cbn [tnum.v tnum.m].
  rewrite !Int.unsigned_repr_eq.

  replace ((bvec2Z _ shift) mod Int.modulus) with (bvec2Z _ shift).
  rewrite !Int64.rshift_reprbvec.
  apply derives_refl.
  auto. auto. lia. auto. lia.

  rewrite Z.mod_small; auto.
  destruct shift as [shift hshift]. cbn.
  assert (modulus 8 < Int.modulus). compute. reflexivity.
  lia.
Qed.
