Set Implicit Arguments.
Require Import Setoid.
Require Import Bool.

(* && and, || or *)

Notation "! X" := (negb X) (at level 7).



Goal forall X Y : bool, (X && !Y) || (!X && !Y) || (!X && Y) = !X || !Y.
Proof. destruct X, Y.
- simpl. reflexivity.
- simpl. reflexivity. 
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Goal forall X Y Z : bool, !(!X && Y && Z) && !(X && Y && !Z) && (X && !Y && Z)
  = (X && !Y && Z). 
Proof. destruct X, Y, Z.
- simpl. reflexivity.
- simpl. reflexivity. 
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity. 
- simpl. reflexivity.
- simpl. reflexivity.
Qed.