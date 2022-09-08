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

Definition negb' (a: bool) : bool :=
    if a then false
    else true.

Definition andb' (a b: bool) : bool :=
    if a then b
    else false.

Definition orb' (a b: bool) : bool :=
    if a then true
    else b.

Compute (andb' true true).

Example test_andb'1:
    (andb' true false) = false.
Proof. reflexivity. Qed.

Module NatPlayground.

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

Fixpoint minus (n m: nat) : nat := 
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

Example test_3_minus_2:
    minus (S (S (S O))) (S (S O)) = (S O).
Proof. reflexivity. Qed.

End NatPlayground.

Compute S (S (S (S O))).

Example test_equals_4:
    S (S (S (S O))) = 4.
Proof. simpl. reflexivity. Qed.

Module NatPlayground3.

Fixpoint eqb (n m : nat) : bool :=
    match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => eqb n' m'
    end.

Example test_eqb_1:
    eqb 3 2 = false.
Proof. reflexivity. Qed.

Example test_eqb2:
    eqb 3 3 = true.
Proof. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
    match n, m with
    | O, O => false
    | S _, O => false
    | O, S _ => true
    | S n', S m' => leb n' m'
    end.

Example test_less1:
    leb 4 4 = false.
Proof. reflexivity. Qed.

Example test_less2:
    leb 114 514 = true.
Proof. simpl. reflexivity. Qed.

Example test_less3:
    leb 114 113 = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n.
    simpl. reflexivity. Qed.

Theorem plus_1_left : forall n : nat, 1 + n = S n.
Proof. intros n.
    simpl. reflexivity. Qed.

Theorem multiply_0_left : forall n : nat, 0 * n = 0.
Proof. intros n.
    simpl. reflexivity. Qed.

End NatPlayground3.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
    Qed.

(*Exercise 1*)
Theorem plus_id_exercise1: forall n m o: nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros H1.
    intros H2.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
    Qed.

Theorem mult_n_0_m_0 : forall n m : nat,
    (n * 0) + (m * 0) = 0.
Proof.
    intros n m.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
    Qed.

Theorem mult_n_1: forall p : nat,
    p * 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
    Qed.