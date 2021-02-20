(*We can use the [Check] command to get the type of an expression*)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)


(*Check can also be applied to functions, which will return a function type*)
(*This example can be read as:
 "given an input of type bool, it returns an expression of type bool"
*)
Check negb.
(* ===> negb : bool -> bool *)