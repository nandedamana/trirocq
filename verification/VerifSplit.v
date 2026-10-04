(* Boilerplate copied from Software Foundations Verifiable C *)
Require Import VST.floyd.proofauto.
Require Import trirocq.Verification.tnumSplitDotC.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

From Stdlib Require Import
  Arith
  ZArith.

From trirocq.Z Require Import
  BitVector
  Tnum
  TnumAdd.

Definition u64 := bvec 64.

Definition tnum_add_split_m_Z (av am bv bm : u64) : u64 :=
  tnum.m (tnum_add (tnum.cons _ av am) (tnum.cons _ bv bm)).

(* TODO no Uint64, Vulong, etc. Make sure this is okay. *)
Definition tnum_add_m_spec : ident * funspec :=
  DECLARE _tnum_add_m
    WITH av : u64, am : u64, bv : u64, bm : u64
                                        PRE [ tulong, tulong, tulong, tulong ]
                                        PROP ()
                                        PARAMS (Vlong (Int64.repr (bvec2Z _ av));
                                                Vlong (Int64.repr (bvec2Z _ am));
                                                Vlong (Int64.repr (bvec2Z _ bv));
                                                Vlong (Int64.repr (bvec2Z _ bm)))
                                        GLOBALS ()
                                        SEP ()
                                        POST [ tulong ]
                                        EX mu : u64,  PROP (mu = tnum_add_split_m_Z av am bv bm)
                                        RETURN (Vlong (Int64.repr (bvec2Z _ mu)))
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
  Set Printing Coercions.
  unfold bvec2Z.
  destruct am, av, bm, bv. cbn.
  repeat rewrite <- Z.add_mod.
  replace Int64.modulus with 18446744073709551616.
  replace (x + x1 + (x0 + x2)) with (x0 + x2 + (x + x1)).
  reflexivity.

  lia.
  compute. reflexivity.
  lia.
Qed.
