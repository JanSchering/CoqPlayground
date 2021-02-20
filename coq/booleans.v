Inductive bool : Type :=
  | true : bool
  | false : bool.
(* We can define our own boolean type like this *)
(* NOTE: Obviously, coq provides booleans in the
 standard library, we can check for that under
 Coq.Init.Datatypes 
*)


(* For training sake, we can try writing some standard boolean functions from scratch *)


Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
(*Takes a boolean parameter b and negates it.*)


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
(*Logical AND: returns TRUE IFF b1 and b2 are true
  takes 2 boolean parameters b1 and b2, observe that the
  value is showing the multi-argument syntax:
    - if b1 evaluates to false, we can just return false
    - if b1 evaluates to true, the return value is the evaluation of b2
*)


Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
(*Logical OR: returns TRUE IFF either b1 or b2 or both are true*)


(*We can use examples to build up a truth table that covers all cases of the 
  or function 
  OBSERVE: We did not explicity use a [simpl.] step, because the
  reflexivity step automatically applies simplification. 
*)
Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.



(*Excercise 1A: NANDB  *)

(*Should return TRUE if either, or both of the inputs are FALSE*)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.

(*Truth table to test the correctness of the definition*)
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.


(*Excercise 1B: AND3 *)

(*Should return True if all 3 inputs are true, false otherwise.*)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

(*Truth table to check correctne*)
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.





