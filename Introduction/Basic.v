Inductive day : Type := 
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday(d: day) : day := 
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Compute (next_weekday (next_weekday friday)).


Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.
Proof.
    simpl.
    reflexivity.
Qed.

Inductive bool : Type := 
    | true
    | false.

Definition negb (a: bool) : bool :=
    match a with
    | true => false
    | false => true
    end.

Example test_negb1:
    (negb true) = false.
Proof. simpl. reflexivity. Qed.

Example test_negb2:
    (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (a: bool) (b: bool) : bool :=
    match a with
    | true => b
    | false => false
    end.

Definition orb (a: bool) (b: bool) : bool :=
    match a with 
    | true => true
    | false => b
    end.

Example test_orb1:
    (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2:
    (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3:
    (orb false true) = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:
    true || false || false = true.
Proof. simpl. reflexivity. Qed.

Check true: bool.
Check orb: bool -> bool -> bool.

Inductive nat: Type :=
    | O
    | S (n: nat).

Definition pred (n: nat) : nat := 
    match n with
    | O => O
    | S n' => n'
    end.

Definition minus_two (n: nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Example test_minus_two:
    minus_two (S (S (S (S O)))) = S (S O).
Proof. simpl. reflexivity. Qed.

Check S (S (S (S O))) : nat.

Fixpoint even (n : nat) : bool := 
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Example test_even1:
    even (S (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (a: nat) (b: nat) : nat :=
    match a with
    | O => b
    | S n' => S (plus n' b)
    end.

Example test_plus1:
    (plus (S O) (S O)) = S (S O).
Proof. simpl. reflexivity. Qed.

Fixpoint multiply (a: nat) (b: nat) : nat :=
    match a with
    | O => O
    | S n' => plus (multiply n' b) b
    end.

Example test_multiply1:
    (multiply (S (S O)) (S (S O))) = S (S (S (S O))).
Proof. simpl. reflexivity. Qed.
