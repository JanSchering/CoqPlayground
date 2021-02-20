Require Import Strings.String.
Local Open Scope string_scope.
Definition test : string := "Hello World!".

Definition monday : string := "monday".

Inductive day : Type :=
  | monday : day
  | "tuesday" : day
  | "wednesday" : day
  | "thursday" : day
  | "friday" : day
  | "saturday" : day
  | "sunday" : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
(* ==> monday : day *)

Eval compute in (next_weekday friday).
(* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
(* This defines an example/test case, we assert that
 the result of the computation will be 'tuesday' *)

Proof. simpl. reflexivity. Qed.
(* Having defined the test case above, we can actually
 reference it and prove that it is true.
 This statement can be broken down into 4 steps:
  - Proof: start of the mathematical proof
  - simpl: simplify both sides of the equation
  - reflexivity: Assert reflexivity to both sides of the equation (tuesday=tuesday)
  - Qed: "quod erat demonstrandum" -> end of the proof
*)
