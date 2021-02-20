(** 
  TECHNICAL NOTE: 
    Coq provides a fairly sophisticated module system, 
    to aid in organizing large developments.
    If we enclose a collection of declarations between
    Module X and End X markers, then, in the remainder
    of the file after the End, these definitions will
    be referred to by names like X.foo instead of just foo.

    Here, we use this feature to introduce the definition
    of the type nat in an inner module so that it does not
    shadow the one from the standard library!
 **)

Module Playground1.


(**
  An interesting way of defining a type is to give a 
  collection of "inductive rules" describing its elements. 
  For example, we can define the natural numbers as follows:
    - O is a natural number
    - S is a "constructor" that takes a natural number and yields another one ("Successor of ...")
**)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.



(**
  We can write simple functions that pattern match on
  natural numbers just as we did above — for example,
 the predecessor function:
**)
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.
(**Read as: 
  - if Origin, return origin
  - if n is the successor of some nat number n', return n'
**)

End Playground1.


Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.


(**
  TECHNICAL NOTE:
    Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and
    printing them: ordinary arabic numerals can be used as an
    alternative to the "unary" notation defined by the constructors S and O.

    Coq prints numbers in arabic form by default and can parse
    arabic numerals it gets as input:
**)
(** EXAMPLE: **)
Check (S (S (S (S O)))).
Eval compute in (minustwo 4).



(*
  TECHNICAL NOTE:
  For most function definitions over numbers, pure pattern matching
  is not enough: we also need recursion. 
  EXAMPLE: to check that a number n is even, we may need to recursively
  check whether n-2 is even. 
  ==> To write such functions, we use the keyword ["Fixpoint."]
*)


(** Even Function: returns TRUE IFF the input is an even number. **)
(**
  OBSERVE: We are using a recursive definition for the function:
    A) we start the recursive definition by declaring a "Fixpoint"
    B) if n is the Origin O, return TRUE (We mathematically define that 0 is even)
    C) if n is the Successor of the Origin O, return FALSE, this fulfills 2 purposes:
      1.) It simply states that 1 is not even
      2.) Together with B) we now have a full set of exit conditions for the recursion,
          every call of this function will at some point end with either 0 or 1, 
          thus yealding TRUE if we end with a 0 (meaning n % 2 == 0),
          or FALSE if we end up with a 1 (meaning n % 2 == 1)
**)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


(**
  Now that we wrote the "even" function, we can combine it with a logic negation
  function to get a simple definition of the "ODD" function: 
**)
Definition oddb (n:nat) : bool := negb (evenb n).



(** Some Tests to ensure the behavior of our function **)
Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.


Module Playground2.


(** 
  Of course, we can also define multi argument recursive functions 
  EXAMPLE: we can define the "Plus" function recursively as follows:
**)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Checking the behavior: **)
Eval compute in (plus (S (S (S O))) (S (S O))).
(** Plus(3,2) => 5 **)

(** 
  We can visualize how Coq comes to this conclusion in the following
  way:
    plus (S (S (S O))) (S (S O))    
    ==> S (plus (S (S O)) (S (S O))) by the second clause of the match
    ==> S (S (plus (S O) (S (S O)))) by the second clause of the match
    ==> S (S (S (plus O (S (S O))))) by the second clause of the match
    ==> S (S (S (S (S O))))          by the first clause of the match
**)



Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
(**
  TECHNICAL NOTE: 
    if two or more arguments have the same type, they can be written together.
    (n m : nat) means just the same as if we had written (n : nat) (m : nat). 
**)

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.


(** We can match two or more variables by separating them with a comma. **)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
(**
  OBSERVE: We used "_" in the matchings. The underscore represents a "Wild Card"
**)

End Playground2.


Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.



(** EXCERCISE 1: FACTORIAL FUNCTION **)
(** 
  translate the factorial function into Coq:
    -factorial(0)  =  1 
    -factorial(n)  =  n * factorial(n-1)     (if n>0)
**)
Fixpoint factorial (n:nat) : nat :=
  match n with 
  | O => 1
  | S n' => mult n (factorial n')
  end.


Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.


(**
    TECHNICAL NOTE:
    We can make numerical expressions a little easier to read and write by
    introducing "notations" for addition, multiplication, and subtraction.

**)
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x × y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).


(** DEFINING EQUALITIES OF NUMBERS **)
(**
    When we say that Coq comes with nothing built-in, we really mean it:
    even equality testing for numbers is a user-defined operation!
    The beq_nat function tests natural numbers for equality, yielding a boolean.
    Note the use of nested matches 
    (we could also have used a simultaneous match, as we did in minus.)
**)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.



(** Similarly, the ble_nat function tests natural numbers for less-or-equal, yielding a boolean. **)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(** Some Examples to showcase and test the behavior. **)
Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.


(** EXCERCISE 2: LESS THAN FUNCTION **)
(**
    The blt_nat function tests natural numbers for less-than, yielding a boolean.
    Instead of making up a new Fixpoint for this one, define it in terms of a 
    previously defined function.
**)
Definition blt_nat (n m : nat) : bool :=
  match n with 
  | O => false
  | S n' => match m with 
            | O => false
            | S m' => andb (ble_nat n m) (negb (beq_nat n m))
            end
  end.

Eval compute in (blt_nat 3 4).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof.
simpl.
reflexivity.
Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof.
simpl.
reflexivity.
Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof.
simpl.
reflexivity.
Qed.
