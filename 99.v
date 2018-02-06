Module NinetyNine.

  (*
   *  H-99: Ninety-Nine Haskell Problems
   *
   *  An Attempt in Coq
   *  Pascal Sommer, Feb. 2018
   *
   *  https://wiki.haskell.org/H-99:_Ninety-Nine_Haskell_Problems
   *)


  Require Import Coq.Arith.Plus.
  Require Import Coq.Arith.Arith.
  Require Import Coq.Arith.EqNat.

  
  (* 
   *  Some datatypes, because we're cool like that
   *  and don't just use the standard library for
   *  everything. (this might be a big mistake)
   *)
  
  Inductive maybe (X : Type) :=
  | nothing : maybe X
  | just : X -> maybe X.

  Arguments nothing {X}.
  Arguments just {X} _.
  
  Inductive list (X : Type) :=
  | nil : list X
  | cons : X -> list X -> list X.

  Arguments nil {X}.
  Arguments cons {X} _ _.

  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).
  Notation "[ ]" := nil.
  Notation "x :: xs" := (cons x xs).

  Fixpoint beq_natlist (a b : list nat) : bool :=
    match a, b with
    | nil, nil => true
    | x::xs, y::ys => andb (beq_nat x y) (beq_natlist xs ys)
    | _, _ => false
    end.

  Theorem beq_natlist_refl :
    forall l : list nat,
      beq_natlist l l = true.
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      rewrite <- beq_nat_refl.
      rewrite -> IHl.
      reflexivity.
  Qed.
  
                          
  (*
   *  ######## Problem 1
   *)
  
  Fixpoint myLast {X : Type} (l : list X) : maybe X :=
    match l with
    | [] => nothing
    | [x] => just x
    | x::xs => myLast xs
    end.

  Example ex_myLast_1 :
    myLast [1;2;3;4] = just 4.
  Proof. reflexivity. Qed.

  Example ex_myLast_2 :
    myLast [] = @nothing nat.
  Proof. reflexivity. Qed.


  (*
   *  ######## Problem 2
   *)

  Fixpoint myButLast {X : Type} (l : list X) : maybe X :=
    match l with
    | [] => nothing
    | [x] => nothing
    | [x;y] => just x
    | x::xs => myButLast xs
    end.

  Example ex_myButLast_1 :
    myButLast [1;2;3;4] = just 3.
  Proof. reflexivity. Qed.

  Example ex_myButLast_2 :
    myButLast [1] = nothing.
  Proof. reflexivity. Qed.


  (*
   *  ######## Problem 3
   *)

  Fixpoint elementAt {X : Type} (l : list X) (n : nat) : maybe X :=
    match n, l with
    | _, [] => nothing
    | 0, x::_ => just x
    | S n', _::xs => elementAt xs n'
    end.

  Example ex_elementAt_1 :
    elementAt [1;2;3;4] 2 = just 3.
  Proof. reflexivity. Qed.

  Example ex_elementAt_2 :
    elementAt [1;2;3] 3 = nothing.
  Proof. reflexivity. Qed.


  (*
   *  Problem 4
   *)

  Fixpoint myLength {X : Type} (l : list X) : nat :=
    match l with
    | nil => 0
    | x::xs => S (myLength xs)
    end.

  Example ex_myLength_1 :
    myLength [1;2;3] = 3.
  Proof. reflexivity. Qed.

  Example ex_myLength_2 :
    myLength (@nil nat) = 0.
  Proof. reflexivity. Qed.

  Theorem cons_increases_length :
    forall (l : list nat) (n : nat),
      myLength (n :: l) = S (myLength l).
  Proof. reflexivity. Qed.

  Print myLength.
  

  (*
   *  ######## Problem 5
   *
   *  It would be possible to define list reversion without
   *  append in linear time, but then it's a lot harder to
   *  prove that the length is preserved.
   *)
  
  Fixpoint append {X : Type} (a b : list X) : list X :=
    match a with
    | nil => b
    | x::xs => x :: (append xs b)
    end.

  Notation "a ++ b" := (append a b).

  Theorem append_preserves_length :
    forall (a b : list nat),
      myLength (a ++ b) = myLength a + myLength b.
  Proof.
    induction a.
    - reflexivity.
    - simpl. intros b.
      rewrite IHa.
      reflexivity.
  Qed.

  Theorem append_neutral_l :
    forall (X : Type) (a : list X),
      a = [] ++ a.
  Proof. reflexivity. Qed.

  Theorem append_neutral_r :
    forall (X : Type) (a : list X),
      a = a ++ [].
  Proof.
    induction a.
    - reflexivity.
    - simpl. rewrite <- IHa.
      reflexivity.
  Qed.

  Theorem append_assoc :
    forall (X : Type) (a b c : list X),
      a ++ (b ++ c) = (a ++ b) ++ c.
  Proof.
    intros X a b c.
    induction a.
    - reflexivity.
    - simpl. rewrite <- IHa.
      reflexivity.
  Qed.

  
  Fixpoint myReverse {X : Type} (l : list X) : list X :=
    match l with
    | nil => nil
    | x :: xs => (myReverse xs) ++ [x]
    end.

  Example ex_myReverse_1 :
    myReverse [] = @nil nat.
  Proof. reflexivity. Qed.

  Theorem reverse_preserves_length :
    forall (l : list nat),
      myLength l = myLength (myReverse l).
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      rewrite -> append_preserves_length.
      rewrite <- IHl.      
      rewrite plus_comm.
      reflexivity.
  Qed.

  Theorem reverse_append :
    forall (X : Type) (a b : list X),
      myReverse (a ++ b) = myReverse b ++ myReverse a.
  Proof.
    induction a.
    - simpl. intros b. rewrite <- append_neutral_r.
      reflexivity.
    - simpl. intros b. rewrite IHa, append_assoc.
      reflexivity.
  Qed.

  Theorem reverse_involution :
    forall (X : Type) (l : list X),
      myReverse (myReverse l) = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite reverse_append, IHl.
      reflexivity.
  Qed.
  

  (*
   *  ######## Problem 6
   *)
  
  Definition isPalindrome (l : list nat) : bool :=
    beq_natlist (myReverse l) l.

  Example ex_isPalindrome_1 :
    isPalindrome [1;2;3;2;1] = true.
  Proof. reflexivity. Qed.

  Theorem rev_append_is_palindrome :
    forall l : list nat,
      isPalindrome (l ++ myReverse l) = true.
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      
  
End NinetyNine.