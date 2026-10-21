(* Boilerplate copied from Software Foundations Verifiable C *)
(* See https://vst.cs.princeton.edu/download/VC.pdf for refman *)
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
  TnumMul.

From trirocq.Verification Require Import
  Common
  VerifMulLoopRec.

Definition tnum_mul_spec : ident * funspec :=
  DECLARE _tnum_mul
    WITH a : val, sha : share,
         b : val, shb : share,
         r : val, shr : share,
         av : u64, am : u64, bv : u64, bm : u64
    PRE [ tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr), tptr(Tstruct _tnum noattr) ]
    PROP ( readable_share sha; readable_share shb; writable_share shr )
    PARAMS (a; b; r)
    GLOBALS ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ av)), Vlong (Int64.repr (uint2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ bv)), Vlong (Int64.repr (uint2Z _ bm))) b;
          data_at_ shr (Tstruct _tnum noattr) r
    )
    POST [ tvoid ]
    EX (expacc : tnum.t 64), PROP (expacc = tnum_mul (tnum.cons _ av am) (tnum.cons _ bv bm))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ av)), Vlong (Int64.repr (uint2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ bv)), Vlong (Int64.repr (uint2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (uint2Z _ (tnum.v expacc))), Vlong (Int64.repr (uint2Z _ (tnum.m expacc)))) r
    ).

Definition Gprog := [ tnum_mul_spec; tnum_mul_loop_spec ].

Lemma z2u_wordsize : forall n (x : uint n), Z2uint n x = x.
  intros n x.
  destruct x as [x hx]. cbn.
  apply Logic.ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma body_tnum_mul_spec : semax_body Vprog Gprog f_tnum_mul tnum_mul_spec.
Proof.
  start_function.

  repeat forward.
  forward_call ((Z2uint 64 64 : u64), a, sha, b, shb, r, shr,
               av, am, bv, bm, (zerovec 64), (zerovec 64)).

  split.
  - destruct av as [av avh]. cbn.
    change (modulus 64) with (2 ^ 64) in avh.
    rewrite Z.mod_small by lia. reflexivity.
  - destruct am as [am amh]. cbn.
    change (modulus 64) with (2 ^ 64) in amh.
    rewrite Z.mod_small by lia. reflexivity.
  -
    Intros vret.
    Exists (tnum_mul (tnum.cons 64 av am) (tnum.cons 64 bv bm)).
    entailer!.
    unfold tnum_mul.
    autorewrite with convuint_db.
    unfold zerotnum.
    change (Z.to_nat 64) with 64%nat.

    unfold trunctnum.
    rewrite !z2u_wordsize.
    entailer!.
    unfold modulus. lia.
Qed.
