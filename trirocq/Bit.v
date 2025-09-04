From Stdlib Require Vector.

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

Section bitops_simplification.
  Lemma bit_and_left_zero x : bit_and zero x = zero.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_right_zero x : bit_and x zero = zero.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_left_one x : bit_and one x = x.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_and_right_one x : bit_and x one = x.
    unfold bit_and; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_left_zero x : bit_or zero x = x.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_right_zero x : bit_or x zero = x.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_left_one x : bit_or one x = one.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_or_right_one x : bit_or x one = one.
    unfold bit_or; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_left_zero x : bit_xor zero x = x.
    unfold bit_xor; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_right_zero x : bit_xor x zero = x.
    unfold bit_xor; destruct x; simpl; reflexivity.
  Qed.

  Lemma bit_xor_x_y_zero x y : bit_xor x y = zero -> x = y.
    intros. destruct x; destruct y; auto.
  Qed.

  Lemma bit_xor_x_y_z_y x y z : bit_xor x (bit_xor y z) = y -> bit_xor x z = zero.
    intros. destruct x; destruct y; destruct z; easy.
  Qed.

  Lemma bit_or_zero_zero x y : bit_or x y = zero -> x = zero /\ y = zero.
    intros. destruct x; destruct y; auto.
  Qed.
End bitops_simplification.

(* Not accessible from other sections if put inside bitops_simplification. *)
Ltac simplify_bit_ops_ex_not :=
  try rewrite bit_and_left_zero;
  try rewrite bit_and_right_zero;
  try rewrite bit_and_left_one;
  try rewrite bit_and_right_one;
  try rewrite bit_or_left_zero;
  try rewrite bit_or_right_zero;
  try rewrite bit_or_left_one;
  try rewrite bit_or_right_one;
  try rewrite bit_xor_left_zero;
  try rewrite bit_xor_right_zero.

Ltac simplify_bit_ops :=
  unfold bit_not;
  simplify_bit_ops_ex_not.
