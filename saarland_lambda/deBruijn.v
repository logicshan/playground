(** De Bruijn terms as retract of preterms *)

From Coq Require Import Arith Lia List.
Import ListNotations.
Ltac inv H := (inversion H; subst; clear H).

Inductive dBterm : Type :=
| var (x: nat) 
| app (s t: dBterm)
| lambda (s: dBterm).

Inductive preterm : Type :=
| Var (x: nat) 
| App (M N: preterm)
| Lambda (x: nat) (M: preterm).

Implicit Types n d x : nat.
Implicit Types s t : dBterm.
Implicit Types M N : preterm.
Implicit Types C : list nat.

(* Preterm -> dBterm: 
   Collect bound names on stack *)
 
Fixpoint B' C x : nat :=
  match C with
  | [] => x
  | y::C' => if Nat.eq_dec x y then 0 else S (B' C' x)
  end.

Fixpoint B M C : dBterm :=
  match M with
  | Var x => var (B' C x)
  | App M N => app (B M C) (B N C)
  | Lambda x N => lambda (B N (x::C))
  end.

(* dBterm -> preterm: 
   Given initial bound n of free variables and number d
   of dominating binders use n+d as next argument variable *)
   
Fixpoint P n d s : preterm :=
  match s with
  | var x => if le_lt_dec d x then Var (x-d) else Var (n+d-S x)
  | app s t => App (P n d s) (P n d t)
  | lambda s => Lambda (n+d) (P n (S d) s)
  end.

(* bound s n iff x<n for all free variables x in s *)

Inductive bound: dBterm -> nat -> Prop :=
| boundV x n : x < n -> bound (var x) n 
| boundA s t n : bound s n -> bound t n -> bound (app s t) n 
| boundL s n : bound s (S n) -> bound (lambda s) n.

(* L n d := [n+d-1,...,n] *)

Fixpoint L n d : list nat :=
  match d with
  | 0 => []
  | S d' => n+d' :: L n d'
  end.
 
Fact L_bnd n d x :
  n <= x < n + d -> B' (L n d) x = n + d - S x.
Proof.
  induction d; intros H; cbn.
  - lia.
  - destruct Nat.eq_dec; lia.
Qed.
  
Fact L_free n d x :
  x < n -> B' (L n d) x = x + d.
Proof.
  induction d; intros H; cbn.
  - lia.
  - destruct Nat.eq_dec; lia.
Qed.
 
Lemma retract' s n d :
  bound s (n + d) -> B (P n d s) (L n d) = s.
Proof.
  induction s in d |-*; intros H; inv H; cbn.
  - destruct le_lt_dec; cbn; f_equal.
    + rewrite L_free; lia.
    + rewrite L_bnd; lia.
  - rewrite IHs1, IHs2; trivial.
  - rewrite IHs. reflexivity.
    replace (n + S d) with (S (n + d)) by lia.
    assumption.
Qed.

Definition dB M := B M [].
Definition pre n s := P n 0 s.

Theorem retract s n :
  bound s n -> dB (pre n s) = s.
Proof.
  intros H. apply (retract' s n 0).
  replace (n + 0) with n by lia.
  exact H.
Qed.

Definition alpha_equiv M N := (dB M = dB N).
Definition pbound M n := bound (dB M) n.

Corollary PB M n :
  pbound M n -> alpha_equiv (pre n (dB M)) M.
Proof.
  intros H. unfold alpha_equiv.
  rewrite retract; trivial.
Qed.
  
