(* Generated using clightgen; see Makefile *)

From Stdlib Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.17".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "tnum.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___compound : ident := $"__compound".
Definition __res : ident := $"_res".
Definition __res__1 : ident := $"_res__1".
Definition __res__2 : ident := $"_res__2".
Definition __res__3 : ident := $"_res__3".
Definition __res__4 : ident := $"_res__4".
Definition __res__5 : ident := $"_res__5".
Definition _a : ident := $"a".
Definition _acc : ident := $"acc".
Definition _alpha : ident := $"alpha".
Definition _b : ident := $"b".
Definition _beta : ident := $"beta".
Definition _chi : ident := $"chi".
Definition _dv : ident := $"dv".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _mu : ident := $"mu".
Definition _shift : ident := $"shift".
Definition _sigma : ident := $"sigma".
Definition _sm : ident := $"sm".
Definition _sv : ident := $"sv".
Definition _tnum : ident := $"tnum".
Definition _tnum_add : ident := $"tnum_add".
Definition _tnum_lshift : ident := $"tnum_lshift".
Definition _tnum_mul : ident := $"tnum_mul".
Definition _tnum_rshift : ident := $"tnum_rshift".
Definition _tnum_sub : ident := $"tnum_sub".
Definition _tnum_union : ident := $"tnum_union".
Definition _v : ident := $"v".
Definition _value : ident := $"value".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition f_tnum_lshift := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) :: (_shift, tuchar) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) ::
              (___compound, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'2 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
          (Sassign
            (Efield (Evar ___compound (Tstruct _tnum noattr)) _value tulong)
            (Ebinop Oshl (Etempvar _t'2 tulong) (Etempvar _shift tuchar)
              tulong)))
        (Ssequence
          (Sset _t'1 (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
          (Sassign
            (Efield (Evar ___compound (Tstruct _tnum noattr)) _mask tulong)
            (Ebinop Oshl (Etempvar _t'1 tulong) (Etempvar _shift tuchar)
              tulong))))
      (Sassign
        (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
          (Tstruct _tnum noattr)) (Evar ___compound (Tstruct _tnum noattr))))
    (Sreturn None)))
|}.

Definition f_tnum_rshift := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) :: (_shift, tuchar) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) ::
              (___compound, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'2 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
          (Sassign
            (Efield (Evar ___compound (Tstruct _tnum noattr)) _value tulong)
            (Ebinop Oshr (Etempvar _t'2 tulong) (Etempvar _shift tuchar)
              tulong)))
        (Ssequence
          (Sset _t'1 (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
          (Sassign
            (Efield (Evar ___compound (Tstruct _tnum noattr)) _mask tulong)
            (Ebinop Oshr (Etempvar _t'1 tulong) (Etempvar _shift tuchar)
              tulong))))
      (Sassign
        (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
          (Tstruct _tnum noattr)) (Evar ___compound (Tstruct _tnum noattr))))
    (Sreturn None)))
|}.

Definition f_tnum_add := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) ::
                (_b, (Tstruct _tnum noattr)) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) :: (_b, (Tstruct _tnum noattr)) ::
              (___compound, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_sm, tulong) :: (_sv, tulong) :: (_sigma, tulong) ::
               (_chi, tulong) :: (_mu, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Sassign (Evar _b (Tstruct _tnum noattr))
      (Etempvar _b (Tstruct _tnum noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'5 (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
        (Ssequence
          (Sset _t'6 (Efield (Evar _b (Tstruct _tnum noattr)) _mask tulong))
          (Sset _sm
            (Ebinop Oadd (Etempvar _t'5 tulong) (Etempvar _t'6 tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _t'3 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
          (Ssequence
            (Sset _t'4
              (Efield (Evar _b (Tstruct _tnum noattr)) _value tulong))
            (Sset _sv
              (Ebinop Oadd (Etempvar _t'3 tulong) (Etempvar _t'4 tulong)
                tulong))))
        (Ssequence
          (Sset _sigma
            (Ebinop Oadd (Etempvar _sm tulong) (Etempvar _sv tulong) tulong))
          (Ssequence
            (Sset _chi
              (Ebinop Oxor (Etempvar _sigma tulong) (Etempvar _sv tulong)
                tulong))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
                (Ssequence
                  (Sset _t'2
                    (Efield (Evar _b (Tstruct _tnum noattr)) _mask tulong))
                  (Sset _mu
                    (Ebinop Oor
                      (Ebinop Oor (Etempvar _chi tulong)
                        (Etempvar _t'1 tulong) tulong) (Etempvar _t'2 tulong)
                      tulong))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sassign
                      (Efield (Evar ___compound (Tstruct _tnum noattr))
                        _value tulong)
                      (Ebinop Oand (Etempvar _sv tulong)
                        (Eunop Onotint (Etempvar _mu tulong) tulong) tulong))
                    (Sassign
                      (Efield (Evar ___compound (Tstruct _tnum noattr)) _mask
                        tulong) (Etempvar _mu tulong)))
                  (Sassign
                    (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
                      (Tstruct _tnum noattr))
                    (Evar ___compound (Tstruct _tnum noattr))))
                (Sreturn None)))))))))
|}.

Definition f_tnum_sub := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) ::
                (_b, (Tstruct _tnum noattr)) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) :: (_b, (Tstruct _tnum noattr)) ::
              (___compound, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_dv, tulong) :: (_alpha, tulong) :: (_beta, tulong) ::
               (_chi, tulong) :: (_mu, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Sassign (Evar _b (Tstruct _tnum noattr))
      (Etempvar _b (Tstruct _tnum noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'5 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
        (Ssequence
          (Sset _t'6 (Efield (Evar _b (Tstruct _tnum noattr)) _value tulong))
          (Sset _dv
            (Ebinop Osub (Etempvar _t'5 tulong) (Etempvar _t'6 tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _t'4 (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
          (Sset _alpha
            (Ebinop Oadd (Etempvar _dv tulong) (Etempvar _t'4 tulong) tulong)))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield (Evar _b (Tstruct _tnum noattr)) _mask tulong))
            (Sset _beta
              (Ebinop Osub (Etempvar _dv tulong) (Etempvar _t'3 tulong)
                tulong)))
          (Ssequence
            (Sset _chi
              (Ebinop Oxor (Etempvar _alpha tulong) (Etempvar _beta tulong)
                tulong))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
                (Ssequence
                  (Sset _t'2
                    (Efield (Evar _b (Tstruct _tnum noattr)) _mask tulong))
                  (Sset _mu
                    (Ebinop Oor
                      (Ebinop Oor (Etempvar _chi tulong)
                        (Etempvar _t'1 tulong) tulong) (Etempvar _t'2 tulong)
                      tulong))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sassign
                      (Efield (Evar ___compound (Tstruct _tnum noattr))
                        _value tulong)
                      (Ebinop Oand (Etempvar _dv tulong)
                        (Eunop Onotint (Etempvar _mu tulong) tulong) tulong))
                    (Sassign
                      (Efield (Evar ___compound (Tstruct _tnum noattr)) _mask
                        tulong) (Etempvar _mu tulong)))
                  (Sassign
                    (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
                      (Tstruct _tnum noattr))
                    (Evar ___compound (Tstruct _tnum noattr))))
                (Sreturn None)))))))))
|}.

Definition f_tnum_union := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) ::
                (_b, (Tstruct _tnum noattr)) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) :: (_b, (Tstruct _tnum noattr)) ::
              (___compound, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_v, tulong) :: (_mu, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Sassign (Evar _b (Tstruct _tnum noattr))
      (Etempvar _b (Tstruct _tnum noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'5 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
        (Ssequence
          (Sset _t'6 (Efield (Evar _b (Tstruct _tnum noattr)) _value tulong))
          (Sset _v
            (Ebinop Oand (Etempvar _t'5 tulong) (Etempvar _t'6 tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _t'1 (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
          (Ssequence
            (Sset _t'2
              (Efield (Evar _b (Tstruct _tnum noattr)) _value tulong))
            (Ssequence
              (Sset _t'3
                (Efield (Evar _a (Tstruct _tnum noattr)) _mask tulong))
              (Ssequence
                (Sset _t'4
                  (Efield (Evar _b (Tstruct _tnum noattr)) _mask tulong))
                (Sset _mu
                  (Ebinop Oor
                    (Ebinop Oor
                      (Ebinop Oxor (Etempvar _t'1 tulong)
                        (Etempvar _t'2 tulong) tulong) (Etempvar _t'3 tulong)
                      tulong) (Etempvar _t'4 tulong) tulong))))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sassign
                (Efield (Evar ___compound (Tstruct _tnum noattr)) _value
                  tulong)
                (Ebinop Oand (Etempvar _v tulong)
                  (Eunop Onotint (Etempvar _mu tulong) tulong) tulong))
              (Sassign
                (Efield (Evar ___compound (Tstruct _tnum noattr)) _mask
                  tulong) (Etempvar _mu tulong)))
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
                (Tstruct _tnum noattr))
              (Evar ___compound (Tstruct _tnum noattr))))
          (Sreturn None))))))
|}.

Definition f_tnum_mul := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _tnum noattr))) ::
                (_a, (Tstruct _tnum noattr)) ::
                (_b, (Tstruct _tnum noattr)) :: nil);
  fn_vars := ((_a, (Tstruct _tnum noattr)) :: (_b, (Tstruct _tnum noattr)) ::
              (_acc, (Tstruct _tnum noattr)) ::
              (__res__1, (Tstruct _tnum noattr)) ::
              (__res__2, (Tstruct _tnum noattr)) ::
              (__res__3, (Tstruct _tnum noattr)) ::
              (__res__4, (Tstruct _tnum noattr)) ::
              (__res__5, (Tstruct _tnum noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _a (Tstruct _tnum noattr))
    (Etempvar _a (Tstruct _tnum noattr)))
  (Ssequence
    (Sassign (Evar _b (Tstruct _tnum noattr))
      (Etempvar _b (Tstruct _tnum noattr)))
    (Ssequence
      (Sassign (Efield (Evar _acc (Tstruct _tnum noattr)) _value tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign (Efield (Evar _acc (Tstruct _tnum noattr)) _mask tulong)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
                  (Sifthenelse (Etempvar _t'4 tulong)
                    (Sset _t'1 (Econst_int (Int.repr 1) tint))
                    (Ssequence
                      (Sset _t'5
                        (Efield (Evar _a (Tstruct _tnum noattr)) _mask
                          tulong))
                      (Sset _t'1 (Ecast (Etempvar _t'5 tulong) tbool)))))
                (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield (Evar _a (Tstruct _tnum noattr)) _value tulong))
                  (Sifthenelse (Ebinop Oand (Etempvar _t'2 tulong)
                                 (Econst_int (Int.repr 1) tint) tulong)
                    (Ssequence
                      (Scall None
                        (Evar _tnum_add (Tfunction
                                          ((tptr (Tstruct _tnum noattr)) ::
                                           (Tstruct _tnum noattr) ::
                                           (Tstruct _tnum noattr) :: nil)
                                          tvoid
                                          {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
                        ((Eaddrof (Evar __res__5 (Tstruct _tnum noattr))
                           (tptr (Tstruct _tnum noattr))) ::
                         (Evar _acc (Tstruct _tnum noattr)) ::
                         (Evar _b (Tstruct _tnum noattr)) :: nil))
                      (Sassign (Evar _acc (Tstruct _tnum noattr))
                        (Evar __res__5 (Tstruct _tnum noattr))))
                    (Ssequence
                      (Sset _t'3
                        (Efield (Evar _a (Tstruct _tnum noattr)) _mask
                          tulong))
                      (Sifthenelse (Ebinop Oand (Etempvar _t'3 tulong)
                                     (Econst_int (Int.repr 1) tint) tulong)
                        (Ssequence
                          (Ssequence
                            (Scall None
                              (Evar _tnum_add (Tfunction
                                                ((tptr (Tstruct _tnum noattr)) ::
                                                 (Tstruct _tnum noattr) ::
                                                 (Tstruct _tnum noattr) ::
                                                 nil) tvoid
                                                {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
                              ((Eaddrof
                                 (Evar __res__3 (Tstruct _tnum noattr))
                                 (tptr (Tstruct _tnum noattr))) ::
                               (Evar _acc (Tstruct _tnum noattr)) ::
                               (Evar _b (Tstruct _tnum noattr)) :: nil))
                            (Scall None
                              (Evar _tnum_union (Tfunction
                                                  ((tptr (Tstruct _tnum noattr)) ::
                                                   (Tstruct _tnum noattr) ::
                                                   (Tstruct _tnum noattr) ::
                                                   nil) tvoid
                                                  {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
                              ((Eaddrof
                                 (Evar __res__4 (Tstruct _tnum noattr))
                                 (tptr (Tstruct _tnum noattr))) ::
                               (Evar _acc (Tstruct _tnum noattr)) ::
                               (Evar __res__3 (Tstruct _tnum noattr)) :: nil)))
                          (Sassign (Evar _acc (Tstruct _tnum noattr))
                            (Evar __res__4 (Tstruct _tnum noattr))))
                        Sskip))))
                (Ssequence
                  (Ssequence
                    (Scall None
                      (Evar _tnum_rshift (Tfunction
                                           ((tptr (Tstruct _tnum noattr)) ::
                                            (Tstruct _tnum noattr) ::
                                            tuchar :: nil) tvoid
                                           {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
                      ((Eaddrof (Evar __res__2 (Tstruct _tnum noattr))
                         (tptr (Tstruct _tnum noattr))) ::
                       (Evar _a (Tstruct _tnum noattr)) ::
                       (Econst_int (Int.repr 1) tint) :: nil))
                    (Sassign (Evar _a (Tstruct _tnum noattr))
                      (Evar __res__2 (Tstruct _tnum noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _tnum_lshift (Tfunction
                                           ((tptr (Tstruct _tnum noattr)) ::
                                            (Tstruct _tnum noattr) ::
                                            tuchar :: nil) tvoid
                                           {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
                      ((Eaddrof (Evar __res__1 (Tstruct _tnum noattr))
                         (tptr (Tstruct _tnum noattr))) ::
                       (Evar _b (Tstruct _tnum noattr)) ::
                       (Econst_int (Int.repr 1) tint) :: nil))
                    (Sassign (Evar _b (Tstruct _tnum noattr))
                      (Evar __res__1 (Tstruct _tnum noattr)))))))
            Sskip)
          (Ssequence
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _tnum noattr)))
                (Tstruct _tnum noattr)) (Evar _acc (Tstruct _tnum noattr)))
            (Sreturn None)))))))
|}.

Definition composites : list composite_definition :=
(Composite _tnum Struct
   (Member_plain _value tulong :: Member_plain _mask tulong :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_tnum_lshift, Gfun(Internal f_tnum_lshift)) ::
 (_tnum_rshift, Gfun(Internal f_tnum_rshift)) ::
 (_tnum_add, Gfun(Internal f_tnum_add)) ::
 (_tnum_sub, Gfun(Internal f_tnum_sub)) ::
 (_tnum_union, Gfun(Internal f_tnum_union)) ::
 (_tnum_mul, Gfun(Internal f_tnum_mul)) :: nil).

Definition public_idents : list ident :=
(_tnum_mul :: _tnum_union :: _tnum_sub :: _tnum_add :: _tnum_rshift ::
 _tnum_lshift :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


