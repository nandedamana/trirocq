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

(* TODO module for v64 *)
(* TODO switch to 64 after testing *)
Definition SIZE := 4.
Definition v64 := Vector.t bit SIZE.
Definition v64_ith (v : v64) {i} (hidx : i < SIZE) :=
  Vector.nth v (Fin.of_nat_lt hidx).

Axiom v64_add : v64 -> v64 -> v64.

Axiom v64_and : v64 -> v64 -> v64.
Axiom v64_and_rel : forall v1 v2 v3, v3 = v64_add v1 v2 -> forall i (hidx : i < SIZE), v64_ith v3 hidx = bit_and (v64_ith v1 hidx) (v64_ith v2 hidx).

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
Fixpoint v64_prvcarry (x y : v64) {i} (hidx : i < SIZE) : bit :=
  match i return i < SIZE -> bit with
  | 0 => fun _ => zero
  | S i' => fun hidx => let a := v64_ith x (ltprv hidx) in
                        let b := v64_ith y (ltprv hidx) in
                        let cin := v64_prvcarry x y (ltprv hidx) in
                        bit_or (bit_or (bit_and a b) (bit_and a cin)) (bit_and b cin)
  end hidx.

Axiom v64_fulladd_result : forall (x y z : v64), z = v64_add x y -> forall i (hidx : i < SIZE), v64_ith z hidx = bit_xor (v64_prvcarry x y hidx) (bit_xor (v64_ith x hidx) (v64_ith y hidx)).

Module tnum.
  (* Type tnum reflects the Kernel tnum, which is a record consisting of
   * v, the value bits, and m, the mask bits (Greek mu).
   *)
  Variant t := cons (v : v64) (m : v64) : t.

  Definition v P := match P with cons v _ => v end.
  Definition m P := match P with cons _ m => m end.
  
  Definition ith_v (tn : t) {i} (hidx : i < SIZE) := v64_ith (v tn) hidx.
  Definition ith_m (tn : t) {i} (hidx : i < SIZE) := v64_ith (m tn) hidx.
End tnum.

Module otnum.
  (* The Kernel representation technically allows four values per trit,
   * but forbids the combination {.v = 1, .m = 1} by convention (i.e.,
   * the value bit should be reset if the mask is set). The representation
   * we use here is a true tristate one, ruling out illegal constructions
   * in any intermediate steps.
   *)

  Definition t := Vector.t (option bit) SIZE.
  Definition nil := Vector.nil (option bit).
  Definition cons := Vector.cons (option bit).
  Arguments cons _ {_} _.

  Definition ith (v : t) {i} (hidx : i < SIZE) :=
    Vector.nth v (Fin.of_nat_lt hidx).

  (* TODO reverse the representation so that i=0 would mean LSB? *)
  Example vt10 := (cons (Some one) (cons (Some zero) (cons (Some one) (cons (Some zero) nil)))).
  Example vt3  := (cons (Some zero) (cons (Some zero) (cons (Some one) (cons (Some one) nil)))).
End otnum.

Definition ingamma (x : v64) (T : otnum.t) : Prop :=
    forall i (hidx : i < SIZE),
      (forall b, otnum.ith T hidx = Some b -> v64_ith x hidx = b).

(* On my own *)
(* We need to define otnum addition with the following properties:
 * 1. Soundness: the result of adding abstract numbers P and Q include the results
 *    of adding any concrete p and q (written less formally for simplicity).
 * 2. TODO optimality:
 *)

Axiom otnum_add : otnum.t -> otnum.t -> otnum.t.

(*
0 0 0
0 1 1
0 x x
1 0 1
1 1 0
1 x x
x 0 x
x 1 x
x x x
*)
Definition obit_xor (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_xor p q)
  | _, _ => None
  end.

Lemma obit_xor_mu_right (x : option bit) : obit_xor x None = None.
  unfold obit_xor. destruct x. destruct b.
  reflexivity. reflexivity. reflexivity.
Qed.

Lemma obit_xor_mu_left (y : option bit) : obit_xor None y = None.
  unfold obit_xor. destruct y; reflexivity.
Qed.

(*
0 0 0
0 1 0
0 x 0
1 0 0
1 1 1
1 x x
x 0 0
x 1 x
x x x
*)
Definition obit_and (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_and p q)
  | _, _ => None
  end.

(*
0 0 0
0 1 1
0 x x
1 0 1
1 1 1
1 x 1
x 0 x
x 1 1
x x x
*)
Definition obit_or (x y : option bit) :=
  match x, y with
  | Some p, Some q => Some (bit_or p q)
  | Some one, _ => Some one
  | _, Some one => Some one
  | _, _ => None
  end.

Fixpoint otnum_prvcarry (P Q : otnum.t) {i} (hidx : i < SIZE) : option bit :=
  match i return i < SIZE -> option bit with
  | 0 => fun _ => Some zero
  | S i' => fun hidx => let a := otnum.ith P (ltprv hidx) in
                        let b := otnum.ith Q (ltprv hidx) in
                        let cin := otnum_prvcarry P Q (ltprv hidx) in
                        obit_or (obit_or (obit_and a b) (obit_and a cin)) (obit_and b cin)
  end hidx.

(* Analogue of v64_fulladd_result *)
Axiom otnum_fulladd_result : forall (P Q R : otnum.t), R = otnum_add P Q -> forall i (hidx : i < SIZE), otnum.ith R hidx = obit_xor (otnum_prvcarry P Q hidx) (obit_xor (otnum.ith P hidx) (otnum.ith Q hidx)).

(* TODO move; placed here for the time being because some trailing proofs are slow *)
Section linux_tnum_addition.
  (* The tnum addition routine in the kernel consists of half a dozen non-obvious steps.
   * On the other hand, otnum addition is easier to reason about. Here we try to
   * establish the relationship between the Linux tnum addition and our otnum addition.
   * Once this is done, the correctness proof for otnum addition automatically
   * becomes the correctness proof for Linux tnum addition.
   *)

  Definition tnum_eq_otnum (t : tnum.t) (o : otnum.t) :=
    forall i (hidx : i < SIZE), (tnum.ith_m t hidx = one -> otnum.ith o hidx = None) /\
                                  (tnum.ith_m t hidx = zero -> otnum.ith o hidx = Some (tnum.ith_v t hidx)).

  (* Part of the otnum model; doesn't require a proof. *)
  Axiom otnum_xor : otnum.t -> otnum.t -> otnum.t.
  Axiom otnum_xor_ith : forall (a b : otnum.t) i (hidx : i < SIZE),
    otnum.ith (otnum_xor a b) hidx = obit_xor (otnum.ith a hidx) (otnum.ith b hidx).

  (* Mirrors the Linux kernel definition *)
  (* TODO not exactly; add the mask neg part *)
  Definition tnum_xor (a b : tnum.t) := tnum.cons (v64_xor (tnum.v a) (tnum.v b)) (v64_or (tnum.m a) (tnum.m b)).

  Lemma tnum_xor_rel t1 t2 :
    let t3 := tnum_xor t1 t2 in
    forall i (hidx : i < SIZE), tnum.ith_v t3 hidx = bit_xor (tnum.ith_v t1 hidx) (tnum.ith_v t2 hidx) /\
                                  tnum.ith_m t3 hidx = bit_or (tnum.ith_m t1 hidx) (tnum.ith_m t2 hidx).
  Proof.
    unfold tnum_xor. unfold tnum.ith_v. unfold tnum.ith_m. simpl;
    intros; split; try apply v64_xor_rel; try apply v64_or_rel; auto.
  Qed.

  Lemma tnum_xor_rel_m t1 t2 :
    let t3 := tnum_xor t1 t2 in
    forall i (hidx : i < SIZE), tnum.ith_m t3 hidx = bit_or (tnum.ith_m t1 hidx) (tnum.ith_m t2 hidx).
  Proof.
    intros. apply tnum_xor_rel.
  Qed.

  Lemma tnum_xor_rel_v t1 t2 :
    let t3 := tnum_xor t1 t2 in
    forall i (hidx : i < SIZE), tnum.ith_v t3 hidx = bit_xor (tnum.ith_v t1 hidx) (tnum.ith_v t2 hidx).
  Proof.
    intros. apply tnum_xor_rel.
  Qed.
  
  Ltac specialize_ith H :=
    match goal with
    | [ hidx : ?i < SIZE |- _ ] => match type of H with
                                     forall i (hidx : i < SIZE), _ =>
                                       let H' := fresh "H'" in assert (H' := H i hidx); auto;
                                                               destruct H'
                                 end
    end.

  Ltac rewrite_biteq_if_holds H :=
    match type of H with
    | ?b = ?b -> _ =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        assert (H1 : b = b); auto; assert (H2 := H H1); rewrite H2
    end.
  
  Lemma tnum_xor_correct t1 t2 o1 o2 : tnum_eq_otnum t1 o1 /\ tnum_eq_otnum t2 o2 -> tnum_eq_otnum (tnum_xor t1 t2) (otnum_xor o1 o2).
    unfold tnum_eq_otnum.
    
    intros H. destruct H as (eq1 & eq2).
    intros i hidx.

    rewrite tnum_xor_rel_m.
    rewrite otnum_xor_ith.

    specialize_ith eq1. specialize_ith eq2.
    destruct (tnum.ith_m t1 hidx); destruct (tnum.ith_m t2 hidx);

    try rewrite_biteq_if_holds H;
      try rewrite_biteq_if_holds H0;
      try rewrite_biteq_if_holds H1;
      try rewrite_biteq_if_holds H2;

      split; try easy; rewrite tnum_xor_rel_v;
      destruct (tnum.ith_v t1 hidx); destruct (tnum.ith_v t2 hidx);
      simpl; auto.
  Qed.

  
(* TODO try to come up with a tnum addition routine based on otnum_fulladd_result instead of proving what's there in the kernel. *)
  
  (* Dealing with kernel addition part by part *)

  Definition tnum_add_sm P Q := v64_add (tnum.m P) (tnum.m Q).
  
  (* sv masked with the newly computed mask forms the value part of the sum. *)  
  Definition tnum_add_sv P Q := v64_add (tnum.v P) (tnum.v Q).

  Lemma tnum_add_sound_sm t1 t2 msk o1 o2 o3 :
    tnum_eq_otnum t1 o1 /\ tnum_eq_otnum t2 o2 /\ msk = tnum_add_sm t1 t2 /\ o3 = otnum_add o1 o2 ->
    forall i (hidx : i < SIZE), (otnum.ith o3 hidx = None -> v64_ith msk hidx = one) /\ (exists b, otnum.ith o3 hidx = Some b -> v64_ith msk hidx = zero).

    unfold tnum_eq_otnum.
    intro H. destruct H as (eq1 & eq2 & hmsk & mo3).

  (* TODO move above *)
  Axiom tnum_add : tnum.t -> tnum.t -> tnum.t.
  Axiom tnum_add_rel : forall P Q R, R = tnum_add P Q ->
                                     let sv := v64_add (tnum.v P) (tnum.v Q) in
                                     let sm := v64_add (tnum.m P) (tnum.m Q) in
                                     let sig := v64_add sv sm in
                                     let chi := v64_xor sig sv in
                                     let eta := v64_or chi (v64_or (tnum.m P) (tnum.m Q)) in
                                     R = tnum.cons (v64_and sv (v64_neg eta)) eta.

  Lemma tnum_add_sound t1 t2 t3 o1 o2 o3 :
    tnum_eq_otnum t1 o1 /\ tnum_eq_otnum t2 o2 /\ t3 = tnum_add t1 t2 /\ o3 = otnum_add o1 o2 ->
    tnum_eq_otnum t3 o3.

    unfold tnum_eq_otnum.
    intros H. destruct H as (eq1 & eq2 & ht3 & ho3).
    intros i hidx.
    split.

    intro t3one.
    
    rewrite tnum_add_rel with (P := t1) (Q := t2) (R := t3) in ht3.

    assert (H : forall (i : nat) (hidx : i < SIZE), otnum.ith o3 hidx = obit_xor (otnum_prvcarry o1 o2 hidx) (obit_xor (otnum.ith o1 hidx) (otnum.ith o2 hidx))).
    apply otnum_fulladd_result. auto.

    

End linux_tnum_addition.

Lemma and_obit_bit a b c : obit_and (Some a) (Some b) = Some c -> bit_and a b = c.
  unfold obit_and. intro H. injection H. auto.
Qed.

Lemma or_obit_bit a b c : obit_or (Some a) (Some b) = Some c -> bit_or a b = c.
  unfold obit_or. unfold bit_or. destruct a.
  all: intro H. injection H. auto.
  injection H. auto.
Qed.

Ltac destruct_bit :=
  match goal with
  | [ b : option bit |- _ ] => destruct b
  | [ b : bit |- _ ] => destruct b
  end.

(* TODO rename *)
Ltac crush1 := compute; easy.
Ltac crush2 :=
  match goal with
  | [ |- _ -> exists p q, Some ?x = Some p /\ Some ?y = Some q /\ bit_and p q = ?c ] => exists x
  | [ |- exists q, _ /\ Some ?x = Some q /\ _ ] => exists x
  end.

Lemma obit_and_imp x y c : obit_and x y = Some c -> exists p q, x = Some p /\ y = Some q /\ bit_and p q = c.
  unfold obit_and. repeat destruct_bit. all: repeat crush1 || crush2.
Qed.

Lemma obit_and_imp2 a b c : obit_and (Some a) (Some b) = Some c -> bit_and a b = c.
  unfold obit_and. repeat destruct_bit. all: repeat crush1 || crush2.
Qed.

Lemma obit_or_imp x y c : obit_or x y = Some c -> x = Some c \/ y = Some c.
  unfold obit_or. repeat destruct_bit. all: compute; auto.
Qed.

(* TODO this works, but are the arg H and the H in the context actually matched? In other words, still works if the arg H is removed?
 * -- maybe use `type of` like I did in specialize_ith
 *)
Ltac assert_and_rel H :=
  match goal with
    | [ H : obit_and ?x ?y = Some _ |- bit_and ?p ?q = _ ] =>
        assert (forall x', x = Some x' -> p = x');
        assert (forall y', y = Some y' -> q = y')
  end.

(* TODO this works, but are the arg H and the H in the context actually matched? In other words, still works if the arg H is removed?
 * -- maybe use `type of` like I did in specialize_ith
 *)
Ltac assert_or_rel H :=
  match goal with
    | [ H : obit_or ?x ?y = Some _ |- bit_or ?p ?q = _ ] =>
        assert (forall x', x = Some x' -> p = x');
        assert (forall y', y = Some y' -> q = y')
  end.

Ltac destruct_oband H :=
  let H' := fresh "H'" in
  let x := fresh "x" in
  let hx := fresh "hx" in
  let hx' := fresh "hx'" in
  assert (H' := H); apply obit_and_imp in H';
  destruct H' as (x & hx); remember hx as hx'; destruct hx'.

Ltac destruct_obor H :=
  let H' := fresh "H'" in
  let h1 := fresh "h1" in
  let h2 := fresh "h2" in
  assert (H' := H); apply obit_or_imp in H'; destruct H' as [h1 | h2];
  try destruct_obor h1; try destruct_oband h1; try destruct_obor h2; try destruct_oband h2.

Ltac ingam_rel P :=
  match goal with
  | [ H : ingamma ?x P, hidx : ?i < SIZE |- _ ] =>
    let H1 := fresh "H1" in
    assert (H1 : forall b, otnum.ith P (ltprv hidx) = Some b -> v64_ith x (ltprv hidx) = b); auto
  end.

Ltac rewrite_obit_and :=
  match goal with
  | [ h1 : ?P = _, h2 : obit_and ?P _ = _ |- _ ] => repeat rewrite h1 in h2
  | [ h1 : ?P = _, h2 : obit_and _ ?P = _ |- _ ] => repeat rewrite h1 in h2
  end.

(* Destructs unknown terms only *)
Ltac destruct_Pi P :=
  match goal with
  | [ _ : otnum.ith P ?hidx = Some _ |- _ ] => idtac
  | _ => let b0 := fresh "b0" in
         let b1 := fresh "b1" in
         match goal with
         | [ Pimpx : forall b : bit, otnum.ith P ?hidx = Some b -> v64_ith ?x ?hidx = b |- _ ] =>
             destruct (otnum.ith P hidx) as [b0|b1]; try rewrite Pimpx with (b := b0)
         end
  end.

Ltac destruct_Ci P Q :=
  match goal with
  | [ _ : otnum_prvcarry P Q ?hidx = Some _ |- _ ] => idtac
  | _ => let b0 := fresh "b0" in
         let b1 := fresh "b1" in
         match goal with
         | [ Pimpx : forall b : bit, otnum_prvcarry P Q ?hidx = Some b -> v64_prvcarry ?x ?y ?hidx = b |- _ ] =>
             destruct (otnum_prvcarry P Q hidx) as [b0|b1]; try rewrite Pimpx with (b := b0)
         end
  end.

Ltac intro_obit_imp_bit :=
  let H := fresh "H" in
  let b := fresh "b" in
  match goal with
  | [ |- obit_and _ _ = Some ?x -> bit_and _ _ = ?x ] =>
      intro H; try assert_or_rel H; try assert_and_rel H; auto
  | [ |- obit_or _ _ = Some ?x -> bit_or _ _ = ?x ] =>
      intro H; try assert_or_rel H; try assert_and_rel H; auto
  | [ |- forall x, obit_and _ _ = Some x -> bit_and _ _ = x ] =>
      intro b; intro_obit_imp_bit
  | [ |- forall x, obit_or _ _ = Some x -> bit_or _ _ = x ] =>
      intro b; intro_obit_imp_bit
  end.

(* TODO rename *)
Ltac crush14 H H3 :=
    try rewrite H; try rewrite H3; try apply obit_and_imp2; auto;
    repeat destruct_bit; simpl in H3; try easy; try auto.

Lemma matching_carry (P Q : otnum.t) (x y : v64) :
  ingamma x P /\ ingamma y Q ->
  forall i (hidx : i < SIZE),
    (forall b, otnum_prvcarry P Q hidx = Some b -> v64_prvcarry x y hidx = b).

  intros ingamXY i hidx.
  induction i.
  - intro b. unfold otnum_prvcarry. unfold v64_prvcarry. intro H. injection H. auto.
  - intro b.

    assert (H1 : forall b, otnum_prvcarry P Q (ltprv hidx) = Some b -> v64_prvcarry x y (ltprv hidx) = b).
    apply IHi.

    destruct ingamXY as (ingamX & ingamY).

    (* TODO remove altogether since assert_and_rel creates these hypos (FIXME not in some cases) *)
    ingam_rel Q. assert (Qimpy := H0).
    ingam_rel P. assert (Pimpx := H2).

    unfold otnum_prvcarry. fold otnum_prvcarry.
    unfold v64_prvcarry. fold v64_prvcarry.

    intro_obit_imp_bit.
    intro_obit_imp_bit.
    destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    intro_obit_imp_bit.
    intro_obit_imp_bit.
    destruct_Pi P; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    intro_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    intro_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    destruct (v64_ith y (ltprv hidx)); simpl; auto.

    intro_obit_imp_bit.
    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    destruct_Pi P; destruct_Pi Q; destruct_Ci P Q; (* TODO pick automatically *)
      crush14 H H3.

    destruct (v64_ith y (ltprv hidx)); simpl; auto.
    destruct (v64_ith x (ltprv hidx)); simpl; auto.
Qed.

(* Mirrors Harishankar et al. except for dropping `wellformed` *)
Lemma otnum_add_sound (P Q R : otnum.t) (x y : v64) :
  R = otnum_add P Q /\ ingamma x P /\ ingamma y Q -> ingamma (v64_add x y) R.
Proof.
  intro H.
  destruct H as (HR & ingamX & ingamY).

  assert (hxy : ingamma x P /\ ingamma y Q). split; trivial.

  unfold ingamma. intros i hidx b Hri.
  unfold ingamma in ingamX.
  unfold ingamma in ingamY.
  apply otnum_fulladd_result with (i := i) (hidx := hidx) in HR.
  rewrite HR in Hri.

  (* Get rid of the `= None` cases *)
  assert (hpi : exists bp, otnum.ith P hidx = Some bp).
  destruct (otnum.ith P hidx). destruct (otnum.ith Q hidx).
  exists b0. reflexivity.
  rewrite obit_xor_mu_right in Hri. easy.
  rewrite obit_xor_mu_left in Hri. rewrite obit_xor_mu_right in Hri. easy.

  (* TODO dedeup and move out *)
  assert (hqi : exists bq, otnum.ith Q hidx = Some bq).
  destruct (otnum.ith P hidx). destruct (otnum.ith Q hidx).
  exists b1. reflexivity.
  rewrite obit_xor_mu_right in Hri. easy.
  rewrite obit_xor_mu_left in Hri. rewrite obit_xor_mu_right in Hri. easy.

  assert (hci : exists bc, otnum_prvcarry P Q hidx = Some bc).
  destruct (otnum_prvcarry P Q hidx).
  exists b0. reflexivity.
  rewrite obit_xor_mu_left in Hri. easy.

  destruct hpi as (bp & hbp).
  destruct hqi as (bq & hbq).
  destruct hci as (bc & hbc).

  assert (hcarry : forall b, otnum_prvcarry P Q hidx = Some b -> v64_prvcarry x y hidx = b).
  apply matching_carry. assumption.

  rewrite v64_fulladd_result with (x := x) (y := y).

  rewrite ingamX with (b := bp).
  rewrite ingamY with (b := bq).
  rewrite hcarry with (b := bc).

  rewrite hbp in Hri. rewrite hbq in Hri. rewrite hbc in Hri.
  unfold obit_xor in Hri. injection Hri. trivial.

  exact hbc. exact hbq. exact hbp. trivial.
Qed.
