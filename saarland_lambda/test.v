Require Import deBruijn.

(* dB : preterm -> dBterm *)
(* pre n : dBterm -> preterm  (* n -- initial bound of free variables *) *)

(* f 4 *)
(* g 5 *)
(* x 0 *)
(* y 1 *)
(* z 2 *)
Definition f : preterm := Var 4.
Definition g : preterm := Var 5.
Definition x : preterm := Var 0.
Definition y : preterm := Var 1.
Definition z : preterm := Var 2.
Definition p1 : preterm := x.                   (* x *)
Definition p2 : preterm := Lambda 0 x.          (* λx.x *)
Definition p3 : preterm := App x y.             (* xy *)
Definition p4 : preterm := Lambda 1 y.          (* λy.y *)
Definition p5 : preterm := App p4 x.            (* (λy.y)x *)
Definition p6 : preterm := Lambda 0 (App f x).  (* (λx.fx) *)

Definition d1 : dBterm := dB p1.  (* 0   *)
Definition d2 : dBterm := dB p2.  (* λ0  *)
Definition d3 : dBterm := dB p3.  (* 0 1 *)
Definition d4 : dBterm := dB p4.  (* λ0  *)
Definition d5 : dBterm := dB p5.  (* (λ0)0 *)
Definition d6 : dBterm := dB p6.  (* λ(5 0) *)


Eval compute in dB p1.
Eval compute in dB p2.
Eval compute in dB p3.
Eval compute in dB p4.
Eval compute in dB p5.
Eval compute in p6.
Eval compute in dB p6.

Eval compute in pre 1 d5.
Eval compute in pre 2 d5.
Eval compute in pre 6 d6.
Eval compute in dB (pre 6 d6).


Definition p7 : preterm := Lambda 5 (App (Var 0) (Var 5)).
Definition d7 : dBterm := dB p7.
Eval compute in d7.
Eval compute in pre 2 d7.

Definition p8 : preterm := App (Lambda 0 (Lambda 1 (App (App (Var 100) (Var 1)) (Var 0)))) (Var 0).
Eval compute in dB p8.

Definition p9 : preterm := App (Lambda 10 (Lambda 11 (App (App (Var 8) (Var 11)) (Var 10)))) (Var 10).
Eval compute in dB p9.
Eval compute in pre 11 (dB p9).

Eval compute in L 3 10.

Definition p10 : preterm := Lambda 0 (Lambda 1 (Lambda 2 (App (App (Var 0) (Var 1)) (Var 2)))).
Eval compute in dB p10.

Definition p11 : preterm := App (Lambda 11 (App (Var 10) (Lambda 12 (Var 11)))) (Lambda 11 (Var 10)).
Eval compute in dB p11.

Definition p12 : preterm := Lambda 10 (App (Lambda 11 (Var 11)) (Var 10)).
Eval compute in dB p12.
