Require Coq.Arith.Arith.
Require Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Import ListNotations.
Import NPeano.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly_ex :
     (forall n, even n = true -> odd (S n) = true) ->
     even 3 = true ->
     odd 4 = true.
Proof.
  intros H.
  apply H.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = EqNat.beq_nat n 5 ->
     EqNat.beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H.
Qed.


Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite eq1, eq2.
  reflexivity.
Qed.

Definition minustwo (n : nat) : nat :=
  n - 2.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  apply trans_eq with m; assumption.
Qed.

