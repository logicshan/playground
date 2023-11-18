(** * Confluence *)

Set Implicit Arguments.
Unset Strict Implicit.
From Coq Require Import Lia Morphisms.
Ltac inv H := inversion H; subst; clear H.

Notation "R <<= S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).
Implicit Types m n k l: nat.

Section Sec1.
  Variables (X: Type) (R: X -> X -> Prop).
  Implicit Types x y z : X.

  Definition functional := forall x y z, R x y -> R x z -> y = z.

  Inductive star : X -> X -> Prop :=
  | starRefl x     : star x x
  | starStep x x' y : R x x' -> star x' y -> star x y.

  Fact star_trans x y z :
    star x y -> star y z -> star x z.
  Proof.
    intros H1 H2.
    induction H1 as [x|x x' y H _ IH].
    + exact H2.
    + econstructor 2; [exact H|]. auto.
  Qed.
 
  Fact star_exp :
    R <<= star.
  Proof.
    intros x y H.
    econstructor 2; [exact H|]. constructor.
  Qed.  
    
  (** Register reflexivty, transitivity, and expansion of star 
     with setoid rewriting *)

  Global Instance star_preorder :
    PreOrder star.
  Proof.
    constructor; hnf.
    - constructor.
    - exact star_trans.
  Qed.

  Global Instance star_expansive :
    subrelation R star.
  Proof.
    exact star_exp.
  Qed.

End Sec1.

Hint Constructors star.
Hint Resolve star_exp star_trans.

Section Sec2.
  Variable X: Type.
  Implicit Types (x y z : X) (R S : X -> X -> Prop).
  
  Fact star_mono R S :
    R <<= S -> star R <<= star S.
  Proof.
    intros H x y.
    induction 1 as [x|x x' y H1 _ IH].
    - constructor.
    - econstructor; [|exact IH]. apply H, H1.
  Qed.

  Fact star_closure R S :
    PreOrder S -> R <<= S -> star R <<= S.
  Proof.
    intros H1 H2 x y.
    induction 1 as [x|x x' y H4 _ IH].
    - reflexivity.
    - transitivity x'; auto.
  Qed.

  Fact star_idem R :
    star (star R) === star R.
  Proof.
    split.
    - apply star_closure. apply star_preorder. auto.
    - apply star_mono, star_expansive.
  Qed.

  Definition joinable R x y := exists z, R x z /\ R y z.
  Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.
  Definition confluent R := diamond (star R).
  Definition semi_confluent R :=
    forall x y z, R x y -> star R x z -> joinable (star R) y z.

  Fact diamond_semi_confluent R :
    diamond R -> semi_confluent R.
  Proof.
    intros H x y1 y2 H1 H2. revert y1 H1.
    induction H2 as [x|x x' y2 H2 _ IH]; intros y1 H1.
    - exists y1. auto.
    - assert (joinable R y1 x') as (z&H3&H4).
      { eapply H; eauto. }
      assert (joinable (star R) z y2) as (u&H5&H6).
      { apply IH; auto. }
      exists u. eauto.
  Qed.

  Fact confluent_semi R :
    confluent R <-> semi_confluent R.
  Proof.
    split.
    - intros H x y1 y2 H1 H2.
      eapply H; [|exact H2]. auto.
    - intros H x y1 y2 H1 H2. revert y2 H2.
      induction H1 as [x|x x' y1 H1 _ IH]; intros y2 H2.
      + exists y2. auto.
      + assert (joinable (star R) x' y2) as (z&H3&H4).
        { eapply H; eauto. }
        assert (joinable (star R) y1 z) as (u&H5&H6).
        { apply IH; auto. }
        exists u. eauto.
  Qed.
  
  Fact diamond_confluent R :
    diamond R -> confluent R.
  Proof.
    intros H.
    apply confluent_semi, diamond_semi_confluent, H.
  Qed.

  Definition prediamond R :=
    forall x y z, R x y -> R x z -> y=z \/ R y z \/ R z y \/ joinable R y z.

  Fact prediamond_confluent R:
    prediamond R -> confluent R.
  Proof.
    intros H.
    apply confluent_semi.
    intros x y1 y2 H1 H2. revert y1 H1.
    induction H2 as [x|x x' y2 H2 H3 IH]; intros y1 H1.
    - exists y1. auto.
    - destruct (H _ _ _ H1 H2) as [->|[H4|[H4|H4]]].
      + exists y2. auto.
      + exists y2. eauto.
      + apply IH, H4.
      + destruct H4 as (z&H5&H6).
        specialize (IH _ H6).
        destruct IH as (u&H7&H8).
        exists u. eauto.
  Qed.
  
  Fact joinable_ext R S x y:
    R === S -> joinable R x y -> joinable S x y.
  Proof.
    firstorder.
  Qed.

  Fact diamond_ext R S:
    R === S -> diamond S -> diamond R.
  Proof.
    intros H1 H2 x y z H3 H4.
    assert (joinable S y z); firstorder.
  Qed.

End Sec2.

(** Evaluation *)

Section Iter.
  Variables (X: Type) (f: X -> X).

  Fixpoint it n x : X :=
    match n with
    | 0 => x
    | S n'=> f (it n' x)
    end.

  Fact it_shift n x :
    f (it n x) = it n (f x).
  Proof.
    induction n; cbn; congruence.
  Qed.

End Iter.

Section Eval.
  Variables (X: Type)  (R: X -> X -> Prop).
  Implicit Types x y z : X.
  Notation "x ≻ y" := (R x y) (at level 70).
  Notation "x ≻* y" := (star R x y) (at level 70).
  Definition normal x := ~ exists y, x ≻ y.
  Definition eval x y := x ≻* y /\ normal y.
  Notation "x ⊳ y" := (eval x y) (at level 70).

  Fact star_normal x y:
    x ≻* y -> normal x -> x = y.
  Proof.
    intros H1 H2.
    destruct H1 as [x|x y z H1 _].
    - reflexivity.
    - exfalso. apply H2. eauto.
  Qed.

  Fact eval_functional:
    confluent R -> functional eval.
  Proof.
    intros H x y z [H1 H2] [H3 H4].
    assert (joinable (star R) y z) as (u&H5&H6).
    { eapply H; eauto. }
    apply star_normal in H5; [|exact H2].
    apply star_normal in H6; [|exact H4].
    congruence.
  Qed.

  Definition red_fun rho :=
    (forall x, x ≻* rho x) /\
    (forall x y, x ⊳ y -> exists n, it rho n x = y).

  Section Evaluator.
    Variables (rho: X -> X) (red: red_fun rho).

    Fact red_fun_fp x :
      normal x -> rho x = x.
    Proof.
      intros H. symmetry. apply star_normal.
      - apply red.
      - exact H.
    Qed.

    Fact red_fun_fp_it x n :
      normal x -> it rho n x = x.
    Proof.
      intros H.
      induction n as [|n IH]; cbn.
      - reflexivity.
      - rewrite IH. apply red_fun_fp, H.
    Qed.
    
    Fact red_fun_normal x y :
      x ⊳ y <-> normal y /\ exists n, it rho n x = y.
    Proof.
      destruct red as [H1 H2]. split.
      - intros [H3 H4]. split. exact H4.
        apply H2. hnf. auto.
      - intros [H3 [n <-]]. split; [|exact H3].
        clear H2 H3. induction n as [|n IH]; cbn.
        + reflexivity.
        + rewrite IH at 1. apply H1.
    Qed.
    
    Variable (delta: forall x, normal x + ~ normal x).

    Fixpoint E n x : option X :=
      match n with
      | 0 => None
      | S n' => if delta x then Some x else E n' (rho x)
      end.

    Fact E_S n x :
      E (S n) x = if delta x then Some x else E n (rho x).
    Proof.
      reflexivity.
    Qed.

    Fact E_it x n :
      normal (it rho n x) -> E (S n) x = Some (it rho n x).
    Proof.
      revert x.
      induction n as [|n IH]; intros x.
      - cbn. destruct (delta x) as [H|H]; tauto.
      - cbn [it]. rewrite it_shift. intros H1 % IH.
        rewrite E_S.
        destruct (delta x) as [H|H]; [|exact H1].
        rewrite red_fun_fp; [|exact H].
        rewrite red_fun_fp_it; [|exact H].
        reflexivity.
    Qed.

    Fact E_correct x y :
      x ⊳ y <-> exists n, E n x = Some y.
    Proof.
      split.
      - intros H. generalize H. intros [n <-] % red.
        exists (S n). apply E_it, H.
      - intros [n H]; revert x H.
        induction n as [|n IH]; cbn; intros x.
        + discriminate.
        + destruct (delta x) as [H|H]; intros H1.
          * assert (x=y) as <- by congruence.
            split; auto.
          * apply IH in H1 as [H1 H2].
            split; [|exact H2].
            rewrite <- H1. apply red.
    Qed.

  End Evaluator.
End Eval.

(** Strong normalisation *)

Section SN1.
  Variables (X: Type) (R: X -> X -> Prop).
  
  Inductive SN : X -> Prop :=
  | SNC x : (forall y, R x y -> SN y) -> SN x.

  Fact SN_unfold x :
    SN x <-> forall y, R x y -> SN y.
  Proof.
    split.
    - destruct 1 as [x H]. exact H.
    - intros H. constructor. exact H.
  Qed.
  
End SN1.

Section SN2.
  Variables (X: Type).
  Implicit Types (x y z : X) (R: X -> X -> Prop).
 
  Fact normal_SN x R :
    normal R x -> SN R x.
  Proof.
    intros H. constructor. intros y H1.
    exfalso. eapply H; eauto.
  Qed.
 
  Definition tc R x y := exists x', R x x' /\ star R x' y.
  
  Fact SN_tc R x :
    SN R x <-> SN (tc R) x.
  Proof.
    split.
    - induction 1 as [x _ IH].
      constructor. intros y H1.
      assert (R x y \/ exists x', R x x' /\ tc R x' y) as [H2|(x'&H2&H3)].
      { destruct H1 as (x'&H1&H2).
        destruct H2 as [y| x' x'' y H3 H4];
          unfold tc; eauto 6. }
      + apply IH, H2.
      + apply IH in H2.
        revert H3. apply SN_unfold, H2.
    - induction 1 as [x _ IH].
      constructor. intros y H1. apply IH.
      exists y. auto.
  Qed.
  
End SN2.

Section Newman.
  Variable (X: Type).
  Implicit Types (x y z : X) (R: X -> X -> Prop).

  Definition terminating R := forall x, SN R x.

  Definition locally_confluent R :=
    forall x y z, R x y -> R x z -> joinable (star R) y z.

  Fact Newman R :
    terminating R -> locally_confluent R -> confluent R.
  Proof.
    intros H1 H2 x.
    generalize (H1 x).
    induction 1 as [x _ IH].
    intros y z H3 H4.
    destruct H3 as [x|x x1 y H5 H6].
    { exists z. auto. }
    destruct H4 as [x|x x2 z H7 H8].
    { exists y. eauto. }
    assert (joinable (star R) x1 x2) as (u&H9&H10).
    { eapply H2; eassumption. }
    assert (joinable (star R) u z) as (v&H11&H12).
    { eapply (IH x2); eauto. }
    assert (joinable (star R) y v) as (w&H13&H14).
    { eapply (IH x1); eauto. }
    exists w. eauto.
  Qed.
End Newman.

Section MorphismLemma.
  Variables (X A: Type) (R: X -> X -> Prop) (S: A -> A -> Prop).

  Definition morphism (f: X -> A) := forall x y, R x  y -> S (f x) (f y).
  
  Fact SN_morphism f x :
    morphism f -> SN S (f x) -> SN R x.
  Proof.
    intros H H1.
    remember (f x) as a eqn:H2. revert x H2.
    induction H1 as [a _ IH]. intros x ->.
    constructor. intros y H1 % H.
    apply (IH _ H1). reflexivity.
  Qed.
End MorphismLemma.

Section Exercise.
  Variables (X: Type) (R: X -> X -> Prop).
  Implicit Types (x y z : X).
  Notation "x ≻ y" := (R x y) (at level 70).

  Variables (app: X -> X -> X)
            (comp: forall x x' y, x ≻ x' -> app x y ≻ app x' y).

  Goal forall x y, SN R (app x y) -> SN R x.
  Proof.
    intros x y.
    pose (f z := app z y).
    change (app x y) with (f x).
    apply SN_morphism. intros a b. apply comp.
  Qed.
End Exercise.

(** TMT Method *)

Section Takahashi.
  Variables (X: Type)  (R: X -> X -> Prop).
  Implicit Types (x y z : X).
  Notation "x ≻ y" := (R x y) (at level 70).
  Notation "x ≻* y" := (star R x y) (at level 70).

  Definition tak_fun rho := forall x y, x ≻ y -> y ≻ rho x.

  Variables (rho: X -> X) (tak: tak_fun rho).

  Fact tak_diamond :
    diamond R.
  Proof.
    intros x y z H1 % tak H2 % tak. exists (rho x). auto.
  Qed.

  Fact tak_sound x :
    Reflexive R -> x ≻ rho x.
  Proof.
    intros H. apply tak, H.
  Qed.

  Fact tak_mono x y :
    x ≻ y -> rho x ≻ rho y.
  Proof.
    intros H % tak % tak. exact H.
  Qed.

  Fact tak_mono_n x y n :
    x ≻ y -> it rho n x ≻ it rho n y.
  Proof.
    intros H.
    induction n as [|n IH]; cbn.
    - exact H.
    - apply tak_mono, IH.
  Qed.

  Fact tak_cofinal x y :
    x ≻* y -> exists n, y ≻* it rho n x.
  Proof.
    induction 1 as [x |x x' y H _ (n&IH)].
    - exists 0. cbn. constructor.
    - exists (S n). rewrite IH. cbn.
      apply star_exp. apply tak, tak_mono_n, H.
  Qed.

End Takahashi.

Section TMT.
  Variables (X: Type) (R S: X -> X -> Prop)
            (H1: R <<= S) (H2: S <<= star R).

  Fact sandwich_equiv :
    star R === star S.
  Proof.
    split.
    - apply star_mono, H1.
    - intros x y H3. apply star_idem. revert x y H3.
      apply star_mono, H2.                            
  Qed.

  Fact sandwich_confluent :
    diamond S -> confluent R.
  Proof.
    intros H3 % diamond_confluent.
    revert H3. apply diamond_ext, sandwich_equiv; auto.
  Qed.

  Theorem TMT rho :
    Reflexive S -> tak_fun S rho -> confluent R /\ red_fun R rho.
  Proof.
    intros H3 H4. split.
    - eapply sandwich_confluent, tak_diamond, H4.
    - split.
      + intros x. apply H2, H4, H3.
      + intros x y [H5 H6].
        apply sandwich_equiv in H5.
        apply (tak_cofinal H4) in H5 as [n H5].
        apply sandwich_equiv in H5.
        exists n. symmetry. eapply star_normal; eassumption.
  Qed.
   
End TMT.

(** Uniform confluence *)

Section UniformConfluence.
  Variables (X: Type)  (R: X -> X -> Prop).
  Implicit Types (x y z : X).
  Notation "x ≻ y" := (R x y) (at level 70).
  Notation "x ≻* y" := (star R x y) (at level 70).

  Definition uniform_confluent :=
    forall x y z, x ≻ y -> x ≻ z -> y = z \/ joinable R y z.

  Fact uni_confl_confl :
    uniform_confluent -> confluent R.
  Proof.
    intros H.
    apply prediamond_confluent.
    intros x y1 y2 H1 H2.
    unfold uniform_confluent in H.
    specialize (H _ _ _ H1 H2). intuition.
  Qed.
  
  Inductive stari : nat -> X -> X -> Prop :=
  | stariRefl x        : stari 0 x x
  | stariStep x x' y n : R x x' -> stari n x' y -> stari (S n) x y.

  Notation "x '≻^' n y" := (stari n x y) (at level 70, n at level 5).

  Fact stari0 x y :
    x ≻^0 y -> x = y.
  Proof.
    intros H. inv H. reflexivity.
  Qed.

  Fact stari1 x y :
    x ≻^1 y <-> x ≻ y.
  Proof.
    split; intros H.
    - inv H. inv H2. assumption.
    - econstructor. exact H. constructor.
  Qed.

  Fact stariS x n y :
    x ≻^(S n) y -> exists x', x ≻ x' /\ x' ≻^n y.
  Proof.
    intros H. inv H. eauto.
  Qed.

  Fact stari_star x n y :
    x ≻^n y -> x ≻* y.
  Proof.
    induction 1 as [x| x x' y n H _ IH]; eauto.
  Qed.

  Fact star_stari x y :
    x ≻* y -> exists n, x ≻^n y.
  Proof.
    induction 1 as [x| x x' y H _ [n IH]].
    - exists 0. constructor.
    - exists (S n). econstructor; eassumption.
  Qed.

  Fact stari_trans x m y n z :
    x ≻^m y -> y ≻^n z -> x ≻^(m+n) z.
  Proof.
    induction 1 as [x| x x' y m H1 _ IH]; cbn; intros H2.
    - auto.
    - econstructor. exact H1. apply IH, H2.
  Qed.

  Hint Constructors stari.
  Hint Resolve stari_trans.

  Definition uni_joinable x y m n :=
    exists k l z, k <= n /\ l <= m /\ x ≻^k z /\ y ≻^l z /\ m + k = n + l.

  Definition uni_semi :=
    forall x y1 n y2, x ≻ y1 -> x ≻^n y2 -> uni_joinable y1 y2 1 n.
  
  Definition uni_full :=
    forall x y1 y2 m n, x ≻^m y1 -> x ≻^n y2 -> uni_joinable y1 y2 m n.
  
  Fact uni2semi :
    uniform_confluent -> uni_semi.
  Proof.
    intros H x y n z H1 H2. revert y H1.
    induction H2 as [x|x x' z n H2 H3 IH]; intros y H1.
    - exists 0, 1, y. intuition. eauto. 
    - assert (y = x' \/ joinable R y x') as [->|(v&H4&H5)].
      { eapply H; eauto. } 
      + exists n, 0, z. cbn. intuition. 
      + assert (uni_joinable v z 1 n) as (k'&l'&u&H6&H7&H8&H9&H10).
        { apply IH; auto. }
        exists (S k'), l', u. intuition. eauto.
        rewrite (plus_Sn_m n l').
        rewrite (PeanoNat.Nat.add_succ_r 1 k').
        rewrite H10. reflexivity.
  Qed.
 
  Fact uni_semi2full :
    uni_semi -> uni_full.
  Proof.
    intros H x y z m n H1 H2. revert n z H2.
    induction H1 as [x|x x' y m H1 H3 IH]; intros n z H2.
    - exists n, 0, z. intuition. 
    - assert (uni_joinable x' z 1 n) as (k'&l'&v&H4&H5&H6&H7&H8).
      { eapply H; eauto. }
      assert (uni_joinable y v m k') as (k''&l''&u&H9&H10&H11&H12&H13).
      { apply IH; auto. }
      exists k'', (l'+l''), u. intuition. eauto.
      exact (PeanoNat.Nat.le_trans k'' k' n H9 H4).
      exact (PeanoNat.Nat.add_le_mono l' 1 l'' m H5 H10). eauto.
      rewrite (plus_Sn_m m k'').
      rewrite H13. rewrite <- (plus_Sn_m k' l'').
      rewrite <- (PeanoNat.Nat.add_1_l k'). rewrite H8. intuition.
  Qed.

  Fact uni_full_uni1 :
    uni_full -> uniform_confluent.
  Proof.
    intros H x y z.
    do 2 rewrite <- stari1. intros H1 H2.
    generalize (H _ _ _ _ _ H1 H2).
    intros (k&l&u&H3&H4&H5&H6&H7).
    assert (k = l /\ (k=0 \/ k=1)) as (<-&[->| ->]) by lia.
    - left.
      apply stari0 in H5 as <-.
      apply stari0 in H6 as <-.
      reflexivity.
    - right. exists u. split; apply stari1; assumption.
  Qed.

  Fact stari_normal x n y:
    x ≻^n y -> normal R x -> n = 0 /\ x = y .
  Proof.
    intros H1 H2.
    destruct H1 as [x|x y z n H1 _].
    - auto.
    - exfalso. apply H2. eauto.
  Qed.

  Fact uni_norm x m y n z :
    uniform_confluent ->
    x ≻^m y -> x ≻^n z -> normal R z ->
    m <= n /\ y ≻^(n-m) z.
  Proof.
    intros H % uni2semi % uni_semi2full H1 H2 H3.
    specialize (H _ _ _ _ _ H1 H2).
    destruct H as (k&l&u&H4&H5&H6&H7&H8).
    assert (l = 0 /\ z = u) as [-> <-]
        by apply (stari_normal H7 H3).
    split. lia.
    assert (n-m = k) as -> by lia.
    exact H6.
  Qed.

  Notation "x ⊳ y" := (eval R x y) (at level 70).
    
  Fact uni_SN x y :
    uniform_confluent -> x ⊳ y -> SN R x.
  Proof.
    intros H1 [[n H2] % star_stari H3].
    revert x H2.
    induction n as [|n IH].
    - intros x H4. inv H4. apply normal_SN, H3.
    - intros x H4.
      constructor. intros z H6 % stari1.
      apply IH.
      replace n with (S n -1) by lia.
      eapply uni_norm; eassumption.
  Qed.
    
End UniformConfluence.

(** Equivalence Closure *)

Section EquivalenceClosure.
  Variable X: Type.
  Implicit Types (x y z: X) (R S: X -> X -> Prop).

  Definition sym R x y := R x y \/ R y x.
  Notation starsym R := (star (sym R)).
  Definition CR R := forall x y, starsym R x y -> joinable (star R) x y.
  Hint Unfold sym.
  
  Instance sym_sym R:
    Symmetric (sym R).
  Proof.
    hnf. unfold sym. intuition.
   Qed.

  Instance sym_exp R :
    subrelation R (sym R).
  Proof.
    hnf. auto.
  Qed.

  Instance star_starsym R :
    subrelation (star R) (starsym R).
  Proof.
    hnf. apply star_mono, sym_exp.
  Qed.

  Instance star_sym R:
    Symmetric R -> Symmetric (star R).
  Proof.
    intros H x y H1.
    induction H1 as [x|x x' z H1 _ IH].
    - reflexivity.
    - apply H in H1. eauto.
  Qed.

  Instance starsym_equivalence R:
    Equivalence (starsym R).
  Proof.
    split.
    - intros x. reflexivity.
    - apply star_sym, sym_sym.
    - hnf. apply star_trans.
  Qed.

  Fact starsym_closure R S:
    Equivalence S -> R <<= S -> starsym R <<= S.
  Proof.
    intros H1 H2.
    apply star_closure.
    - split; apply H1.
    - intros x y [H3|H3].
      + auto.
      + symmetry. auto.
  Qed.

  Fact CR_confluence R :
    CR R <-> confluent R.
  Proof.
    split.
    - intros H x y z H1 H2. apply H.
      rewrite <- H1, H2. reflexivity.
    - intros H x y H1.
      induction H1 as [x|x x' y H1 _ (u&IH1&IH2)].
      + exists x. auto.
      + destruct H1 as [H1|H1].
        * exists u. eauto.
        * assert (joinable (star R) x u) as (v&H3&H4).
          { eauto. }
          exists v. eauto.
  Qed.

  Fact CR_eval R x y:
    confluent R -> starsym R x y -> normal R y -> eval R x y.
  Proof.
    intros H % CR_confluence H1 H2.
    apply H in H1 as (z&H1&H3).
    destruct (star_normal H3 H2).
    hnf. auto.
  Qed.

End EquivalenceClosure.


