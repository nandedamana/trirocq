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
  Tnum
  TnumUnion.

From trirocq.Verification Require Import
  Common.

Definition tnum_union_spec : ident * funspec :=
  DECLARE _tnum_union
    WITH a : val, sha : share,
         b : val, shb : share,
         r : val, shr : share,
         av : u64, am : u64, bv : u64, bm : u64, rv : u64, rm : u64
    PRE [ tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr) ]
    PROP ( readable_share sha; readable_share shb; writable_share shr )
    PARAMS (a; b; r)
    GLOBALS ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ bv)), Vlong (Int64.repr (bvec2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ rv)), Vlong (Int64.repr (bvec2Z _ rm))) r
    )
    POST [ tvoid ]
    EX (sum : tnum.t 64), PROP (sum = tnum_union (tnum.cons _ av am) (tnum.cons _ bv bm))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ bv)), Vlong (Int64.repr (bvec2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ (tnum.v sum))), Vlong (Int64.repr (bvec2Z _ (tnum.m sum)))) r
    ).

Definition Gprog := [ tnum_union_spec ].

Lemma body_tnum_union_spec : semax_body Vprog Gprog f_tnum_union tnum_union_spec.
Proof.
  start_function.

  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  Exists (tnum_union (tnum.cons _ av am) (tnum.cons _ bv bm)).
  repeat forward.
  entailer!.
  unfold tnum_union.
  cbn [tnum.v tnum.m].

  Set Printing Coercions.
  unfold Int64.xor.

  rewrite Z.land_bvec.
  rewrite !Int64.unsigned_repr_eq.
  rewrite !mod_bvec2Z.
  rewrite Z.lxor_bvec.
  rewrite !Int64.or_reprbvec.
  rewrite Int64.not_to_bvec_neg.
  rewrite !Int64.and_reprbvec.
  repeat rewrite <- and64_repr.
  apply derives_refl.
Qed.
