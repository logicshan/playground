(** Untyped lambda terms in de Bruijn representation *)
Require Import Setoid Equivalence Morphisms.

Require Import confluence abstractLambdaBeta.

Implicit Types (s t : term) (σ τ : nat -> term) (ξ : nat -> nat).

Variable funext : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.

(** Function composition *)

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.

(** This is also composition of renamings *)
Notation "f ⊚ g" := (funcomp f g)
  (at level 56, left associativity).

(** Stream cons *)

Definition scons {X : Type} (s : X) (xs : nat -> X) (x : nat) : X :=
  match x with S y => xs y | _ => s end.
Notation "s .: xr" := (scons s xr)
  (at level 55, xr at level 56, right associativity).

Lemma scons_comp X Y (x : X) (f : nat -> X) (g : X -> Y) :
  (x .: f) ⊚ g = (g x) .: (f ⊚ g).
Proof. apply funext;intros [|n]; reflexivity. Qed.

(** * Definition of Instantiation. *)

(** We first need to define everything for renaming so that our definitions are structurally recursive. *)

(** 'up' on renamings *)
Definition upr ξ := 0 .: (ξ ⊚ S).

Definition ren ξ := fun x => var (ξ x).

Reserved Notation "s '.⟨' σ ⟩"
  (at level 2, σ at level 200, left associativity,
   format "s '.⟨' σ ⟩" ).

Fixpoint rename ξ s : term :=
  match s with
  | var n => var (ξ n)
  | app s t => app s.⟨ξ⟩ t.⟨ξ⟩
  | lambda s => lambda s.⟨upr ξ⟩
  end
where "s .⟨ σ ⟩" := (rename σ s).

Definition up σ := var 0 .: (σ ⊚ rename S).
Arguments up σ x /.
Notation "⇑" := up.

Reserved Notation "s .[ σ ]" 
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).

Fixpoint inst σ s :=
  match s with
  | var n => σ n
  | app s t => app s.[σ] t.[σ]
  | lambda s => lambda s.[up σ]
  end
where "s .[ σ ]" := (inst σ s).

Definition scomp σ τ := σ ⊚ inst τ.
Arguments scomp σ τ x /.
Notation "σ ∘ τ" := (scomp σ τ) (at level 56).

Notation "s .[ σ ]" := (inst σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).

(** Renaming is a special case of institution *)

Lemma upr_up ξ : ren (upr ξ) = up (ren ξ).
Proof. apply funext;now intros []. Qed.

Lemma rename_inst ξ :
  rename ξ = inst (ren ξ).
Proof.
  apply funext. intros s. revert ξ. induction s; simpl; intros.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - now rewrite IHs, <- upr_up.
Qed.


(** * Basic Equations *)
Definition I (n:nat):=var n.
Definition β s t := s.[t.:I].

Lemma beta_def s t :
  β s t = s.[t.:I].
Proof.
  reflexivity.
Qed.

Arguments β : simpl never. (*never unfold beta automatically by cbn *)

Lemma up_def σ:
  up σ = (var 0).:(σ ∘ ren S).
Proof.
  apply funext. intros [].
  -reflexivity.
  -cbn. now rewrite rename_inst.
Qed.


Lemma inst_app (s t:term) σ:
  (app s t).[σ] = s.[σ] t.[σ].
Proof.  reflexivity.  Qed.


Lemma inst_lam (s:term) σ:
  (lambda s).[σ] = lambda (s.[⇑ σ]).
Proof. reflexivity. Qed.

Lemma inst_0_cons (s:term) σ:
  (var 0).[s.:σ] = s.
Proof. reflexivity. Qed.

Section inst_I.
  Lemma up_I :
    ⇑ I = I.
  Proof. apply funext. intros []. all:reflexivity. Qed.
  
  Lemma inst_I (s:term):
    s.[I] = s.
  Proof.
    induction s.
    all:cbn [inst].
    -reflexivity.
    -congruence.
    -rewrite up_I. congruence.
  Qed.
End inst_I.


Section inst_comp.
  
  (** We need a few helper lemmas here *)
  Fact aux1 τ:
    ren S ∘ ⇑ τ = τ ∘ ren S.
  Proof.
    apply funext. cbn. rewrite rename_inst. reflexivity.
  Qed.

  Fact aux2 ξ σ:
    (⇑ (ren ξ)) ∘ (⇑ σ) = ⇑ (ren ξ ∘ σ).
  Proof. apply funext;intros [|n]. all:reflexivity. Qed.

  Fact aux3 s ξ τ:
    s.⟨ξ⟩.[τ] = s.[ren ξ ∘ τ].
  Proof.
    induction s in ξ,τ |- *. all:cbn [inst rename].
    -reflexivity.
    -now rewrite IHs1,IHs2.
    -now rewrite IHs,upr_up,aux2.
  Qed.

  
  Fact aux4 ξ σ:
    (⇑ σ) ∘ (⇑ (ren ξ)) = ⇑ (σ ∘ (ren ξ)).
  Proof.
    apply funext;intros [|n].
    1:now reflexivity.
    cbn.
    rewrite aux3,aux1.
    rewrite <- rename_inst with (ξ:=ξ).
    rewrite rename_inst with (ξ:=S).
    rewrite aux3. reflexivity.
  Qed.

  Fact aux5 s ξ σ:
    s.[σ].⟨ξ⟩ = s.[σ ∘ ren ξ].
  Proof.
    induction s in ξ,σ |- *. all:cbn [inst rename].
    -now rewrite rename_inst.
    -now rewrite IHs1,IHs2.
    -now rewrite IHs,upr_up,aux4.
  Qed.

  Fact aux6 σ τ:
    (⇑ σ) ∘ (⇑ τ) = ⇑ (σ ∘ τ).
  Proof.
    apply funext;intros [|n].
    1:now reflexivity.
    cbn.
    now rewrite aux3,aux5,aux1. 
  Qed.
  
  Lemma inst_comp s σ τ :
    s.[σ].[τ] = s.[σ ∘ τ].
  Proof.
    induction s in σ,τ|-*.
    1,2:now cbn;congruence. 
    cbn. now rewrite IHs,aux6. 
  Qed.
End inst_comp.

Lemma cons_0_S :
  (var 0).:ren S = I.
Proof. apply funext. intros []. all:reflexivity. Qed.

Lemma comp_I_r σ :
  σ ∘ I = σ.
Proof.
  apply funext;intros n. cbn. now rewrite inst_I.
Qed.

Lemma comp_I_l σ :
  I ∘ σ = σ.
Proof. reflexivity. (* Follows by eta conversion *) Qed.

Lemma comp_assoc σ τ μ :
  (σ ∘ τ) ∘ μ = σ ∘ (τ ∘ μ).
Proof. apply funext;intros n. cbn. now rewrite inst_comp. Qed.

Lemma cons_comp s σ τ :
  (s.:σ) ∘ τ = (s.[τ]).:(σ ∘ τ).
Proof. apply funext;intros [];cbn. all:reflexivity. Qed. 

Lemma comp_S_cons s σ:
  ren S ∘ (s.:σ) = σ.
Proof.  apply funext;intros [];cbn. all:reflexivity. Qed.

Lemma head_cons_tail σ :
  (var 0).[σ].:(ren S ∘ σ) = σ.
Proof. apply funext;intros [];cbn. all:reflexivity. Qed.

(** Now we have shown all basic equations, thus we disable automatic reduction *)
Arguments inst : simpl never.
Arguments up : simpl never.

(* We do not add beta_def up_def to keep the abstraction layer it provides *)
Hint Rewrite inst_app inst_lam inst_0_cons inst_I inst_comp cons_0_S comp_I_l comp_I_r comp_assoc cons_comp comp_S_cons head_cons_tail: basic_equations.

Lemma distributivity_beta_up s t σ:
  (β s t).[σ] = β (s.[⇑ σ]) (t.[σ]).
Proof.
  rewrite !beta_def,!up_def. now autorewrite with basic_equations.
Qed.

(** * Strong Substitutivity of Parallel Reduction *)
Local Notation "s ≫ t" := (pstep β s t) (at level 70).

Lemma substitutivity_pstep s t σ:
  s ≫ t -> s.[σ] ≫ t.[σ].
Proof.
  induction 1 in σ |-*.
  -apply pstep_refl.
  -rewrite distributivity_beta_up.
   autorewrite with basic_equations.
   all:auto using pstep.
  -autorewrite with basic_equations.
   auto using pstep.
  -autorewrite with basic_equations.
   auto using pstep.
Qed.

Notation "σ ⋙ τ" := (forall n, σ n ≫ τ n) (at level 70).

Lemma compatibility_pstep_up σ τ:
  σ ⋙ τ -> ⇑ σ ⋙ ⇑ τ.
Proof.
  intros H [|n];unfold up;cbn. 
  1:now apply pstep_refl.
  rewrite rename_inst.
  eapply substitutivity_pstep, H.
Qed.

Lemma strong_substitutivity_pstep s t σ τ:
  s ≫ t -> σ ⋙ τ -> s.[σ] ≫ t.[τ].
Proof.
  induction 1 in σ,τ |-*;intros Hσ.
  -unfold inst. apply Hσ.
  -rewrite distributivity_beta_up.
   autorewrite with basic_equations.
   econstructor. 2:now eauto.
   now apply IHpstep1,compatibility_pstep_up.
  -autorewrite with basic_equations.
   auto using pstep.
  -autorewrite with basic_equations.
   econstructor.
   now apply IHpstep, compatibility_pstep_up.
Qed.

Corollary compat_beta_pstep:
  compatible β.
Proof.
  repeat intro. rewrite !beta_def. apply strong_substitutivity_pstep.
  1:assumption.
  intros [|n]. all:cbn. all:eauto using pstep_refl.
Qed.

Corollary confluent_lambda_calculus :
  confluent (step β) /\ red_fun (step β) (rho β).
Proof.
  apply ALB. apply compat_beta_pstep.
Qed.
