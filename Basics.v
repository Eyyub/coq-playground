Inductive day : Type :=
  | lundi : day
  | mardi : day
  | mercredi : day
  | jeudi : day
  | vendredi : day
  | samedi : day
  | dimanche : day.

Definition next_day (d : day) : day := 
  match d with
  | lundi => mardi
  | mardi => mercredi
  | mercredi => jeudi
  | jeudi => vendredi
  | vendredi => samedi
  | samedi => dimanche
  | dimanche => lundi
  end.

Eval compute in (next_day vendredi).
Eval compute in (next_day (next_day samedi)).

Example test_next_day:
  next_day (next_day dimanche) = mardi.

Proof.
  simpl. (* optional 'cause reflexivity seems to perform simpl automatically*)
  reflexivity.
Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Example test_negb1 : negb true = false.
Proof. 
  reflexivity.
Qed.

Example test_negb2 : negb false = true.
Proof. 
  reflexivity.
Qed.

Definition andb (a : bool) (b : bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

Example test_andb1 : andb false false = false.
Proof.
  reflexivity.
Qed.

Example test_andb2 : andb true false = false.
Proof.
  reflexivity.
Qed.

Example test_andb3 : andb false true = false.
Proof.
  reflexivity.
Qed.

Example test_andb4 : andb true true = true.
Proof.
  reflexivity.
Qed.

Definition orb (a : bool) (b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

Example test_orb1 : orb false false = false.
Proof.
  reflexivity.
Qed.

Example test_orb2 : orb true false = true.
Proof.
  reflexivity.
Qed.

Example test_orb3 : orb true false = true.
Proof.
  reflexivity.
Qed.

Example test_ordb4 : orb true true = true.
Proof.
  reflexivity.
Qed.

(* Exercises *)

(* nandb *)
Definition nandb (a : bool) (b : bool) : bool :=
  negb (andb a b).

Example test_nandb1: nandb true false = true.
Proof.
  reflexivity.
Qed.

Example test_nandb2: nandb false false = true.
Proof.
  reflexivity.
Qed.

Example test_nandb3: nandb false true = true.
Proof.
  reflexivity.
Qed.

Example test_nandb4: nandb true true = false.
Proof.
  reflexivity.
Qed.

(* andb3 *)

Definition andb3 (a : bool) (b : bool) (c : bool) : bool :=
  andb (andb a b) c.

Example test_andb31: andb3 true true true = true.
Proof.
  reflexivity.
Qed.

Example test_andb32: andb3 false true true = false.
Proof.
  reflexivity.
Qed.

Example test_andb33: andb3 true false true = false.
Proof.
  reflexivity.
Qed.

Example test_andb34: andb3 true true false = false.
Proof.
  reflexivity.
Qed.

(* Numbers *)

Module MyNat.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End MyNat.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Module Playground1.

  Fixpoint my_plus (a b : nat) : nat :=
    match b with
    | O => a
    | S n => plus (S a) n
    end.

  (* from sf *)
  Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

  Example test_plus510: plus 5 10 = 15.
  Proof.
    reflexivity.
  Qed.

  Eval compute in (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. reflexivity. Qed.

  (* Exercises *)

  Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => S O
    | S n' => mult n (factorial n')
    end.

  Example test_fact0 : factorial O = S O.
  Proof.
    reflexivity.
  Qed.

  Example test_fact3 : factorial 3 = 6.
  Proof.
    reflexivity.
  Qed.

  Example test_fact4 : factorial 4 = 4 * factorial 3.
  Proof.
    reflexivity.
  Qed.

  Example test_fact5 : factorial 5 = mult 10 12.
  Proof.
    reflexivity.
  Qed.

End Playground1.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  ble_nat n (m - 1).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

(* Exercises *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S _, O
  | O, S _ => false
  | S n', S m' => beq_nat n' m'
  end.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n' ].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n' ].
  reflexivity.
  reflexivity.
Qed.

Theorem identify_fn_applied_twice :
  forall (f : bool -> bool),
  (forall x : bool,
  f x = x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem neg_fn_applied_twice :
  forall (f : bool -> bool),
  (forall x : bool,
  f x = negb x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(* mmh works but seems bad *)
Theorem andb_eq_orb :
  forall b c : bool,
  andb b c = orb b c -> b = c.
Proof.
  intros b.
  intros c.
  destruct b.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.
