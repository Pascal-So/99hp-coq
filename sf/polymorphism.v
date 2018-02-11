Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Import ListNotations.



Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | (x,y) :: ls => let rest := split ls in (x :: fst rest, y :: snd rest)
  end.

Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter f xs else filter f xs
  end.


Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. auto. Qed.



Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (NPeano.leb 7 n) (NPeano.even n)) l.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. auto. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. auto. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
  : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition NPeano.odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. auto. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. auto. Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    List.map f (List.rev l) = List.rev (List.map f l).
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite map_app, IHl.
    reflexivity.
Qed.

Fixpoint foldr {X Y : Type} (f : X -> Y -> Y) (y : Y) (l : list X) : Y :=
  match l with
  | [] => y
  | x :: xs => f x (foldr f y xs)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  foldr (fun _ n => S n) 0 l.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. auto. Qed.
Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    unfold fold_length. simpl. reflexivity.
Qed.

Module Church.
  Definition nat := forall X : Type, (X -> X) -> X -> X.
  
  Definition one : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f x.
  
  Definition two : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (f x).

  Definition three : nat :=
    fun X f (x : X) => f (f (f x)).
  
  Definition zero : nat :=
    fun (X : Type) (f : X -> X) (x : X) => x.
  
  Definition succ (n : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (n X f x).
                                
  Example succ_1 : succ zero = one.
  Proof. auto. Qed.
  
  Example succ_2 : succ one = two.
  Proof. auto. Qed.


  Definition plus (n m : nat) : nat :=
    fun X (f : X -> X) (x : X) => n X f (m X f x).
  
  Example plus_1 : plus zero one = one.
  Proof. auto. Qed.
  
  
  Definition mult (n m : nat) : nat :=
    fun X f => n X (m X f).
  
  Example mult_1 : mult one one = one.
  Proof. auto. Qed.

  Example mult_2 : mult zero (plus three three) = zero.
  Proof. auto. Qed.
  
  Example mult_3 : mult two three = plus three three.
  Proof. auto. Qed.
  
  Definition exp (n m : nat) : nat :=
    (*n nat (mult m) one.*)
    fun X => m ((X -> X) -> X -> X) ((fun n' m' f => n' (m' f)) (n X)) (one X).
                                 
  Example exp_1 : exp two two = plus two two.
  Proof. auto. Qed.
  Example exp_2 : exp three two = plus (mult two (mult two two)) one.
  Proof. auto. Qed.
  Example exp_3 : exp three zero = one.
  Proof. auto. Qed.
  
End Church.