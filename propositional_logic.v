Inductive bool : Type :=
  | true
  | false.

Definition neg (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Notation "~ x" := (neg x).

Definition and (b : bool) (c : bool) : bool :=
  match b with
  | true => c
  | false => false
  end.
Notation "x && y" := (and x y).

Definition or (b : bool) (c : bool) : bool :=
  match b with
  | true => true
  | false => c
  end.
Notation "x || y" := (or x y).

Theorem de_morgan_1 : forall (b c : bool), (~(b && c)) = ((~b) || (~c)).
Proof. intros [] c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem de_morgan_2 : forall (b c : bool), (~(b || c)) = ((~b) && (~c)).
Proof. intros [] c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_1 : forall b : bool, (b && true) = b.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_2 : forall b : bool, (b || false) = b.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem domination_1 : forall b : bool, (b && false) = false.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem domination_2 : forall b : bool, (b || true) = true.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem idempotent_1 : forall b : bool, (b && b) = b.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem idempotent_2 : forall b : bool, (b || b) = b.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem double_neg : forall b : bool, (~(~b)) = b.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negation_1 : forall b : bool, (b || (~b)) = true.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negation_2 : forall b : bool, (b && (~b)) = false.
Proof. intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem or_commutative : forall b c : bool, b || c = c || b.
Proof. intros [] c.
  - simpl. rewrite domination_2. reflexivity.
  - simpl. rewrite identity_2. reflexivity.
Qed.

Theorem and_commutative : forall b c : bool, b && c = c && b.
Proof. intros [] c.
  - simpl. rewrite identity_1. reflexivity.
  - simpl. rewrite domination_1. reflexivity.
Qed.

Theorem or_associative : forall a b c : bool, (a || b) || c = a || (b || c).
Proof. intros [] b c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem and_associative : forall a b c : bool, (a && b) && c = a && (b && c).
Proof. intros [] b c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem distribute_or_on_and : forall a b c : bool, (a || (b && c)) = (a || b) && (a || c).
Proof. intros [] b c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem distribute_and_on_or : forall a b c : bool, (a && (b || c)) = (a && b) || (a && c).
Proof. intros [] b c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem absorption_1 : forall b c : bool, b || (b && c) = b.
Proof. intros [] c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem absorption_2 : forall b c : bool, b && (b || c) = b.
Proof. intros [] c.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

