From LF Require Export Basics.

Theorem add_0_r : forall n : nat,
    n + 0 = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem minus_n_n: forall n : nat,
    minus n n = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem mult_n_0: forall n : nat,
  n * 0 = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + S m.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem add_comm: forall n m : nat,
  n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl.
      rewrite -> add_0_r.
      reflexivity.
    - simpl.
      rewrite -> IHn'.
      rewrite -> plus_n_Sm.
      reflexivity.
Qed.

Theorem add_assoc: forall n m p : nat,
    (n + m) + p = n + (m + p).
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - simpl.
      reflexivity.
    - simpl. 
      rewrite -> IHn'.
      reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl. 
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n ?= n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.


Theorem even_S : forall n : nat,
  (even (S n)) = (negb (even n)).
Proof.
  intros n.
  induction n as [| m IHm].
  - simpl. reflexivity.
  - assert (H1 : even (S (S m)) = even m).
    { simpl. reflexivity. }
    rewrite -> H1.
    rewrite -> IHm.
    rewrite -> negb_involution.
    reflexivity.
  Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. } 
  rewrite -> H.
  reflexivity.
  Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
  Qed.

(*Exercise 3 : multiplicative commutative.*)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H1: n + (m + p) = n + m + p).
    { rewrite -> add_assoc. reflexivity. }
  rewrite -> H1.
  assert (H2: n + m = m + n).
    { rewrite -> add_comm. reflexivity. }
  rewrite -> H2.
  rewrite -> add_assoc.
  reflexivity.
  Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> add_shuffle3.
    reflexivity.
  Qed.  

Theorem mult_comm : forall n m : nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. 
    rewrite -> mult_n_0.
    reflexivity.
  - simpl. 
    rewrite -> mult_n_Sm.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem plus_leb_compat_l : forall n m p: nat,
  n <=? m = true ->
    (p + n) <=? (p + m) = true.
Proof.
  intros n m p H1.
  induction p as [| p' IHp'].
  - simpl.
    rewrite -> H1.
    reflexivity.
  - simpl. 
    rewrite -> IHp'.
    reflexivity.
  Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  intros n.
  simpl. 
  rewrite -> add_0_r.
  reflexivity.
  Qed.

Check mult_n_0.