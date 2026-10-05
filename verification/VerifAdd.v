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
  TnumAdd.

From trirocq.Verification Require Import
  Common.

(* No preconditions regarding bounds since u64 itself contains proof. *)
Definition tnum_add_spec : ident * funspec :=
  DECLARE _tnum_add
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
    EX (sum : tnum.t 64), PROP (sum = tnum_add (tnum.cons _ av am) (tnum.cons _ bv bm))
    RETURN ()
    SEP ( data_at sha (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ av)), Vlong (Int64.repr (bvec2Z _ am))) a;
          data_at shb (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ bv)), Vlong (Int64.repr (bvec2Z _ bm))) b;
          data_at shr (Tstruct _tnum noattr)
            (Vlong (Int64.repr (bvec2Z _ (tnum.v sum))), Vlong (Int64.repr (bvec2Z _ (tnum.m sum)))) r
    ).

Definition Gprog := [ tnum_add_spec ].

(* See https://softwarefoundations.cis.upenn.edu/vc-current/Verif_sumarray.html
 * for an explanation of semax_body.
 * f_tnum_add is the body of tnum_add parsed by ClightGen.
 *)
Lemma body_tnum_add_spec : semax_body Vprog Gprog f_tnum_add tnum_add_spec.
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
  forward.
  Exists (tnum_add (tnum.cons _ av am) (tnum.cons _ bv bm)).
  repeat forward.
  entailer!.
  unfold tnum_add. simpl.

  repeat rewrite <- or64_repr.
  repeat rewrite <- and64_repr.

  rewrite bvec64_not_repr.

  repeat rewrite <- or64_repr.
  unfold Int64.xor.
  unfold Int64.and.
  autorewrite with norm.

  rewrite !Int64.unsigned_repr_eq.
  Set Printing Coercions.
  unfold bvec2Z.
  destruct am, av, bm, bv. cbn.
  repeat rewrite <- Z.add_mod.
  replace 18446744073709551616 with Int64.modulus.
  replace (x + x1 + (x0 + x2)) with (x0 + x2 + (x + x1)).
  rewrite Z.mod_mod.

  apply derives_refl.

  compute; easy.
  lia.
  compute; easy.
  easy.
Qed.
