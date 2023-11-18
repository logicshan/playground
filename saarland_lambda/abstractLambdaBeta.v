(** * Confluence of Abstract Lambda Beta *)

Require Import confluence.

Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lambda (s : term).

Coercion app : term >-> Funclass. 

Implicit Types s t u v : term.
Implicit Types n k : nat.

Section ALB.
  Variable beta : term -> term -> term. 
  
  Reserved Notation "s ≻ t" (at level 70).
  Inductive step : term -> term -> Prop :=
  | stepBeta  s t     : (lambda s) t ≻ beta s t
  | stepAppL s s' t  : s ≻ s' -> s t ≻ s' t
  | stepAppR s t  t' : t ≻ t' -> s t ≻ s t'
  | stepLam s s'     : s ≻ s' -> lambda s ≻ lambda s'
  where "s ≻ t" := (step s t).

  Notation "x ≻* y"  := (star step x y)(at level 70).

  Reserved Notation "s >> t" (at level 70).
  Inductive pstep : term -> term -> Prop :=
  | pstepVar n          : var n >> var n
  | pstepBeta s s' t t' : s >> s' -> t >> t' -> (lambda s) t >> beta s' t'
  | pstepApp  s s' t t' : s >> s' -> t >> t' -> s t >> s' t'
  | pstepLam s s'       : s >> s' -> lambda s >> lambda s'
  where "s >> t" := (pstep s t).
 
  Fixpoint rho s : term := 
    match s with
    | var n => var n
    | app (lambda s) t => beta (rho s) (rho t)
    | app s t => (rho s) (rho t)
    | lambda s => lambda (rho s)
    end.

  Definition compatible := 
    forall s s' t t', s >> s' -> t >> t' -> beta s t >> beta s' t'.

  Hint Constructors step pstep.

  Fact star_app_comp s s' t t':
    s ≻* s' -> t ≻* t' -> s t ≻* s' t'.
  Proof.
    intros H1 H2.
    induction H1 as [s|s s'' s' H _ IH]; intros.
    - induction H2; eauto. 
    - clear H2. eauto.
  Qed.

  Fact star_lam_comp s s':
    s ≻* s' -> lambda s ≻* lambda s'.
  Proof.
    intros H. induction H; eauto. 
  Qed.

  Fact pstep_refl s :
    s >> s. 
  Proof.
    induction s; eauto.
  Qed.
 
  Fact step_pstep :
    step <<= pstep. 
  Proof.
    intros s t.
    induction 1; eauto using pstep_refl.
  Qed.

  Fact pstep_star_step :
    pstep <<= star step.
  Proof.
    intros s t.
    induction 1; eauto using star_app_comp, star_lam_comp. 
  Qed.

  Fact takahashi : 
    compatible -> tak_fun pstep rho. 
  Proof. 
    intros H s t.
    induction 1 as
        [n| s s' t t' _ IH1 _ IH2| s s' t t' H1 IH1 _ IH2| s s' _ IH1].
    - cbn. constructor.
    - cbn. apply H; assumption.
    - destruct s.
      + cbn. auto.
      + change (rho ((s1 s2) t)) with ((rho (s1 s2)) (rho t)). auto.
      + cbn.
        assert (exists s1, s' = lambda s1 /\ s1 >> rho s) as (s1&->&H3).
        { inv H1; inv IH1; eauto. }
        auto.
    - cbn. auto.
  Qed.

  Theorem ALB :
    compatible -> confluent step /\ red_fun step rho.
  Proof.
    intros H.
    apply TMT with (S:= pstep).
    - apply step_pstep.
    - apply pstep_star_step.
    - hnf. apply pstep_refl.
    - apply takahashi, H.
  Qed.

End ALB.
