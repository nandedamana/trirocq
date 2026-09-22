(* Boilerplate copied from Software Foundations Verifiable C *)
Require Import VST.floyd.proofauto.
Require Import trirocq.Verification.tnumSplitDotC.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tnum_add_split_m_Z (av am bv bm : Z) : Z :=
  let sm := (am + bm) mod Int64.modulus in
  let sv := (av + bv) mod Int64.modulus in
  let sigma := (sm + sv) mod Int64.modulus in
  let chi := Z.lxor sigma sv in
  let mu := Z.lor (Z.lor chi am) bm in
  mu.

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
  unfold tnum_add_split_m_Z.

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
