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
    rewrite -> add_0_r.
    - simpl.
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

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = n * p + m * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> add_assoc.
    reflexivity.
  Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> mult_plus_distr_r.
    rewrite -> IHn'.
    reflexivity.
  Qed.

(*Exercise: 2 stars, standard, optional (add_shuffle3')*)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite -> add_comm.
    reflexivity.
  Qed.

(*Exercise: 3 stars, standard, especially useful (binary_commute)*)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (increase b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [|b' IHb' | b'' IHb''].
  - (* Case b = Z *)
    reflexivity.
  - (* Case b = (B0 b') *)
    reflexivity.
  - (* Case b = (B1 b'') *) 
    simpl.
    repeat rewrite -> add_0_r.
    simpl.
    rewrite -> IHb''.
    rewrite -> add_shuffle3.
    repeat rewrite <- add_assoc.
    reflexivity.
  Qed.

(* Exercise: 3 stars, standard (nat_bin_nat) *)
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => increase (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* Case n = O *)
    reflexivity.
  - (* Case n = S n' *)
    simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem double_increase : forall n : nat,
  double (S n) = S (S (double n)).
Proof.
  intros n.
  reflexivity.
  Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | _ => (B0 b)
  end.

Example test_double_bin_5:
  (bin_to_nat (double_bin (B1 (B0 (B1 Z))))) = 10.
Proof.
  reflexivity.
  Qed.

Example double_bin_zero:
  (double_bin Z) = Z.
Proof.
  reflexivity.
  Qed.

Lemma double_increase_bin : forall b : bin,
  double_bin (increase b) = increase (increase (double_bin b)).
Proof.
  intros b.
  destruct b eqn:Eqb.
  - (* Case b = Z *)
    reflexivity.
  - (* Case b = (B0 b')*)
    reflexivity.
  - (* Case b = (B1 b') *)
    reflexivity.
  Qed.

(* Exercise: 4 stars, advanced (bin_nat_bin) *)
(* Trying to elimiating the redundant leading zeros in a bin expression with 
   the normalize function. 
     The root cause that (nat_to_bin (bin_to_nat b)) != b is that there are 
   infinity valid representation for Z (i.e. Z). For example 
   (B0 Z), (B0 (B0 Z)), (B0 (B0 (B0 Z))) ...... are all representing 0. *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 n' => (double_bin (normalize n'))
  | B1 n' => (B1 (normalize n'))
  end.

Compute (normalize (B1 (B0 (B0 (B0 Z))))).

Lemma double_eq_n_plus_n : forall n : nat,
  (double n) = n + n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* Case n = O *)
    reflexivity.
  - (* Case n = S n' *)
    simpl.
    rewrite <- plus_n_Sm.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem nat_to_bin_double : forall n : nat,
  (nat_to_bin (double n)) = (double_bin (nat_to_bin n)).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* Case n = O *)
    reflexivity.
  - (* Case n = S n' *)
    rewrite -> double_increase.
    simpl.
    rewrite -> double_increase_bin.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem increase_double_bin : forall b : bin,
  (increase (double_bin b)) = (B1 b).
Proof.
  intros b.
  destruct b eqn:Eqb.
  - (* Case b = Z *)
    reflexivity.
  - (* Case b = (B0 b') *)
    reflexivity.
  - (* Case b = (B1 b'') *)
    reflexivity.
  Qed.

Theorem bin_nat_bin : forall b : bin,
  (nat_to_bin (bin_to_nat b)) = (normalize b).
Proof.
  intros b.
  induction b as [| b' IHb'| b'' IHb''].
  - (* Case b = Z *)
    reflexivity.
  - (* Case b = (B0 b') *)
    simpl.
    rewrite -> add_0_r. 
    rewrite <- double_eq_n_plus_n.
    rewrite -> nat_to_bin_double.
    rewrite -> IHb'.
    reflexivity.
  - (* Case b = (B1 b'') *)
    simpl.
    rewrite -> add_0_r.
    rewrite <- double_eq_n_plus_n.
    rewrite -> nat_to_bin_double.
    rewrite -> IHb''.
    rewrite -> increase_double_bin.
    reflexivity.
  Qed.