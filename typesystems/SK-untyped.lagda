\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module SK-untyped where

open import Lib

module I where
  infixl 5 _$_

  postulate
    Tm  : Set
    _$_ : Tm → Tm → Tm
    K   : Tm
    S   : Tm
    Kβ  : ∀{t u} → K $ t $ u ≡ t
    Sβ  : ∀{t u v} → S $ t $ u $ v ≡ t $ v $ (u $ v)

record DepModel {i : Level} : Set (lsuc i) where
  infixl 5 _$∙_

  field
    Tm∙  : I.Tm → Set i
    _$∙_ : ∀{t u} → Tm∙ t → Tm∙ u → Tm∙ (t I.$ u)
    K∙   : Tm∙ I.K
    S∙   : Tm∙ I.S
    Kβ∙  : ∀{t u}{t∙ : Tm∙ t}{u∙ : Tm∙ u} → (Tm∙ ~) I.Kβ (K∙ $∙ t∙ $∙ u∙) t∙
    Sβ∙  : ∀{t u v}{t∙ : Tm∙ t}{u∙ : Tm∙ u}{v∙ : Tm∙ v} →
          (Tm∙ ~) I.Sβ (S∙ $∙ t∙ $∙ u∙ $∙ v∙) ((t∙ $∙ v∙) $∙ (u∙ $∙ v∙))
  
  postulate
    ⟦_⟧t : (t : I.Tm) → Tm∙ t
    ⟦$⟧t : ∀{t u} → ⟦ t I.$ u ⟧t ≈ ⟦ t ⟧t $∙ ⟦ u ⟧t
    ⟦K⟧t : ⟦ I.K ⟧t ≈ K∙
    ⟦S⟧t : ⟦ I.S ⟧t ≈ S∙
    {-# REWRITE ⟦$⟧t ⟦K⟧t ⟦S⟧t #-}

record Model {i} : Set (lsuc i) where
  infixl 5 _$_

  field
    Tm  : Set i
    _$_ : Tm → Tm → Tm
    K   : Tm
    S   : Tm
    Kβ  : ∀{t u} → K $ t $ u ≡ t
    Sβ  : ∀{t u v} → S $ t $ u $ v ≡ t $ v $ (u $ v)
    
  ⟦_⟧t  : I.Tm → Tm
  ⟦_⟧t = D.⟦_⟧t
    where
      D : DepModel
      D = record { Tm∙ = λ _ → Tm ; _$∙_ = _$_ ; K∙ = K ; S∙ = S ; Kβ∙ = Kβ ; Sβ∙ = Sβ }
      module D = DepModel D

record DepModelP {i : Level} : Set (lsuc i) where
  infixl 5 _$∙_

  field
    Tm∙  : I.Tm → Prop i
    _$∙_ : ∀{t u} → Tm∙ t → Tm∙ u → Tm∙ (t I.$ u)
    K∙   : Tm∙ I.K
    S∙   : Tm∙ I.S
  
  ⟦_⟧t : (t : I.Tm) → Tm∙ t
  ⟦ t ⟧t = un D.⟦ t ⟧t
    where
      D : DepModel
      D = record { Tm∙ = λ t → Lift (Tm∙ t) ; _$∙_ = λ t∙ u∙ → mk (un t∙ $∙ un u∙) ; K∙ = mk K∙ ; S∙ = mk S∙ ; Kβ∙ = refl ; Sβ∙ = refl }
      module D = DepModel D

module _ where
  open I

  I' : Tm
  I' = S $ K $ K

  Iβ : ∀{u} → I' $ u ≡ u
  Iβ {u} =
    I' $ u
                                  ≡⟨ refl ⟩
    S $ K $ K $ u
                                  ≡⟨ Sβ ⟩
    K $ u $ (K $ u)
                                  ≡⟨ Kβ ⟩
    u
                                  ∎
                                  
  B : Tm
  B = S $ (K $ S) $ K

  Bβ : ∀{t u v} → B $ t $ u $ v ≡ t $ (u $ v)
  Bβ {t = t}{u = u}{v = v} =
    B $ t $ u $ v
                                  ≡⟨ refl ⟩
    S $ (K $ S) $ K $ t $ u $ v
                                  ≡⟨ cong {A = Tm} (λ x → x $ u $ v) Sβ ⟩
    K $ S $ t $ (K $ t) $ u $ v
                                  ≡⟨ cong {A = Tm} (λ x → x $ (K $ t) $ u $ v) Kβ ⟩
    S $ (K $ t) $ u $ v
                                  ≡⟨ Sβ ⟩
    K $ t $ v $ (u $ v)
                                  ≡⟨ cong {A = Tm} (λ x → x $ (u $ v)) Kβ ⟩
    t $ (u $ v)
                                  ∎


module S≠K where
  infixl 5 _∙R_ _∙_
  infix  4 _↦_ _↦*_

  data RTm : Set where
    SR KR : RTm
    _∙R_ : RTm → RTm → RTm

  data _↦_ : RTm → RTm → Prop where
    idR  : {u : RTm} → u ↦ u
    KβR  : {u v : RTm} → KR ∙R u ∙R v ↦ u
    SβR  : {u v w : RTm} → SR ∙R u ∙R v ∙R w ↦ u ∙R w ∙R (v ∙R w)
    _∙R_ : {t₀ t₁ u₀ u₁ : RTm} → t₀ ↦ t₁ → u₀ ↦ u₁ → t₀ ∙R u₀ ↦ t₁ ∙R u₁

  data _↦*_ : RTm → RTm → Prop where
    refl : {u : RTm} → u ↦* u
    step : {u₀ u₁ u₂ : RTm} → u₀ ↦ u₁ → u₁ ↦* u₂ → u₀ ↦* u₂

  data _~_ (t₀ t₁ : RTm) : Prop where
    mk~ : (t   : RTm) → t₀ ↦* t → t₁ ↦* t → t₀ ~ t₁

  ref~ : {t : RTm} → t ~ t
  ref~ {t} = mk~ t refl refl

  sym~ : ∀{t₀ t₁} → t₀ ~ t₁ → t₁ ~ t₀
  sym~ = {!!}

  trans~ : ∀{t₀ t₁ t₂} → t₀ ~ t₁ → t₁ ~ t₂ → t₀ ~ t₂
  trans~ = {!!}

  -- TODO: we should add general quotients in the library and use those
  postulate
    Tm   : Set
    η    : RTm → Tm
    eq   : {t₀ t₁ : RTm} → t₀ ~ t₁ → η t₀ ≡ η t₁
    ite  : ∀{ℓ}(A : Set ℓ)(f : RTm → A)(e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁) → Tm → A
    iteβ : ∀{ℓ}(A : Set ℓ)(f : RTm → A)(e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁)(b : RTm) → ite A f e (η b) ≈ f b
    ind  : ∀{ℓ}(A : Tm → Set ℓ)(f : (t : RTm) → A (η t))
           (e : {t₀ t₁ : RTm}(t₀~t₁ : t₀ ~ t₁) → transp A (eq t₀~t₁) (f t₀) ≡ f t₁) → (b : Tm) → A b
    indβ : ∀{ℓ}(A : Tm → Set ℓ)(f : (t : RTm) → A (η t))
           (e : {t₀ t₁ : RTm}(t₀~t₁ : t₀ ~ t₁) → transp A (eq t₀~t₁) (f t₀) ≡ f t₁)(b : RTm) →
           ind A f e (η b) ≈ f b
    indp : ∀{ℓ}(A : Tm → Prop ℓ)(f : (t : RTm) → A (η t)) → (b : Tm) → A b
  {-# REWRITE iteβ indβ #-}

  postulate
    propext : ∀{ℓ}{A B : Prop ℓ} → (A → B) → (B → A) → A ≡ B

  module _ (t₀ : RTm) where
    _~'_ : Tm → Prop
    _~'_ = ite Prop (λ t₁ → t₀ ~ t₁) λ { t₁ t₂ t₁~t₂ → propext (λ t₀~t₁ → trans~ t₀~t₁ t₁~t₂) (λ t₀~t₂ → trans~ t₀~t₂ (sym~ t₁~t₂)) }

  coep : ∀{ℓ}{A B : Prop ℓ} → A ≡ B → A → B
  coep refl a = a

  eff : ∀{t₀ t₁} → η t₀ ≡ η t₁ → t₀ ~ t₁
  eff {t₀} e = coep (cong (t₀ ~'_) e) ref~

  ite= : ∀{ℓ}{A : Set ℓ}{f f' : RTm → A} → 
    {e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁}
    {e' : (t₀ t₁ : RTm) → t₀ ~ t₁ → f' t₀ ≡ f' t₁}
    {b : Tm} → (f= : f ≡ f') → ite A f e b ≡ ite A f' e' b
  ite= {ℓ}{A}{f}{f'}{e}{e'}{b} refl = refl

  S K : Tm
  S = η SR
  K = η KR

  ∙R-right : {t u₀ u₁ : RTm} → u₀ ↦* u₁ → t ∙R u₀ ↦* t ∙R u₁
  ∙R-right refl = refl
  ∙R-right (step u₀u₁ u₁u₂) = step (idR ∙R u₀u₁) (∙R-right u₁u₂)

  ∙R-left : {t₀ t₁ u : RTm} → t₀ ↦* t₁ → t₀ ∙R u ↦* t₁ ∙R u
  ∙R-left refl = refl
  ∙R-left (step t₀t₁ t₁t₂) = step (t₀t₁ ∙R idR) (∙R-left t₁t₂)

  _∙_ : Tm → Tm → Tm
  a ∙ b = ite Tm
    (λ t → ite Tm (λ u → η (t ∙R u)) (λ { u₀ u₁ (mk~ u u₀u u₁u) → eq (mk~ (t ∙R u) (∙R-right {t} u₀u) (∙R-right {t} u₁u)) }) b)
    (λ { t₀ t₁ (mk~ t t₀t t₁t) → ite= {_}{Tm}{λ u → η (t₀ ∙R u)}{λ u → η (t₁ ∙R u)}{λ { u₀ u₁ (mk~ u u₀u u₁u) → eq (mk~ (t₀ ∙R u) (∙R-right u₀u) (∙R-right u₁u))}}{λ { u₀ u₁ (mk~ u u₀u u₁u) → eq (mk~ (t₁ ∙R u) (∙R-right u₀u) (∙R-right u₁u))}}{b} (funext (λ (u : RTm) → eq (mk~ (t ∙R u) (∙R-left t₀t) (∙R-left t₁t))))}) a

  Kβ : (a b : Tm) → K ∙ a ∙ b ≡ a
  Kβ a b = indp (λ a → ((K ∙ a) ∙ b) ≡ a)
    (λ t → indp (λ b → ((K ∙ η t) ∙ b) ≡ η t)
      (λ u → eq (mk~ t (step KβR refl) (step idR refl)))
      b)
    a

  Sβ : (a b c : Tm) → S ∙ a ∙ b ∙ c ≡ a ∙ c ∙ (b ∙ c)
  Sβ a b c = indp (λ a → S ∙ a ∙ b ∙ c ≡ a ∙ c ∙ (b ∙ c))
    (λ t → indp (λ b → S ∙ η t ∙ b ∙ c ≡ η t ∙ c ∙ (b ∙ c))
      (λ u → indp (λ c → S ∙ η t ∙ η u ∙ c ≡ η t ∙ c ∙ (η u ∙ c))
        (λ v → eq (mk~ (t ∙R v ∙R (u ∙R v)) (step SβR refl) (step idR refl)))
        c)
      b)
    a

  Sval : ∀{t} → SR ↦* t → t ≡ SR
  Sval refl = refl
  Sval (step idR St) = Sval St

  Kval : ∀{t} → KR ↦* t → t ≡ KR
  Kval refl = refl
  Kval (step idR Kt) = Kval Kt

  KKval : ∀{t} → KR ∙R KR ↦* t → t ≡ KR ∙R KR
  KKval refl = refl
  KKval (step idR t↦*t') = KKval t↦*t'
  KKval (step (idR ∙R idR) t↦*t') = KKval t↦*t'

  SKKval : ∀{t} → SR ∙R KR ∙R KR ↦* t → t ≡ SR ∙R KR ∙R KR
  SKKval refl = refl
  SKKval (step idR e) = SKKval e
  SKKval (step (idR ∙R idR) e) = SKKval e
  SKKval (step (idR ∙R idR ∙R idR) e) = SKKval e

  SKSval : ∀{t} → SR ∙R KR ∙R SR ↦* t → t ≡ SR ∙R KR ∙R SR
  SKSval refl = refl
  SKSval (step idR e) = SKSval e
  SKSval (step (idR ∙R idR) e) = SKSval e
  SKSval (step (idR ∙R idR ∙R idR) e) = SKSval e

  S≁K : SR ~ KR → ⊥
  S≁K (mk~ t St Kt) with Sval St ⁻¹ ◾ Kval Kt
  ... | ()

  S≠K : S ≡ K → ⊥
  S≠K e = S≁K (eff e)

  SKK≁SKS : (SR ∙R KR ∙R KR) ~ (SR ∙R KR ∙R SR) → ⊥
  SKK≁SKS (mk~ t SKKt SKSt) with SKKval SKKt ⁻¹ ◾ SKSval SKSt
  ... | ()

  SKK≠SKS : S ∙ K ∙ K ≡ S ∙ K ∙ S → ⊥
  SKK≠SKS e = SKK≁SKS (eff e)

  -- TODO: show that the inductively defined normal forms below are
  -- all normal in the sense that they don't reduce to anything; and
  -- thus they are not equal in the syntax

module normalisationTry where
  open I
  data Nf : I.Tm → Set where
    K₀ : Nf K
    K₁ : ∀{t} → Nf t → Nf (K $ t)
    S₀ : Nf S
    S₁ : ∀{t} → Nf t → Nf (S $ t)
    S₂ : ∀{t u} → Nf t → Nf u → Nf (S $ t $ u)

  data MaybeP {ℓ}(A : Set ℓ) : Prop ℓ where
    nothing : MaybeP A
    just    : A → MaybeP A

  app : ∀{t u} → ℕ → Nf t → Nf u → MaybeP (Nf (t $ u))
  app f K₀  n = just (K₁ n)
  app f (K₁ n) n' = just (transp Nf (Kβ ⁻¹) n)
  app f S₀ n = just (S₁ n)
  app f (S₁ n) n' = just (S₂ n n')
  app zero    (S₂ n n') n'' = nothing
  app (suc f) (S₂ n n') n'' with app f n n'' | app f n' n''
  ... | nothing | _ = nothing
  ... | just _ | nothing = nothing
  ... | just n''' | just n'''' = transpP (λ z → MaybeP (Nf z)) (Sβ ⁻¹) (app f n''' n'''')

  _>>=_ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → MaybeP A → (A → MaybeP B) → MaybeP B
  nothing >>= _       = nothing
  just a  >>= f       = f a

  D : DepModelP
  D = record
    { Tm∙ = λ t → ℕ → MaybeP (Nf t)
    ; _$∙_ = λ t∙ u∙ f → t∙ f >>= λ nt → u∙ f >>= λ nu → app f nt nu
    ; K∙ = λ _ → just K₀
    ; S∙ = λ _ → just S₀ }
  module D = DepModelP D

  norm norm' : (t : Tm) → ℕ → MaybeP (Nf t)
  norm = D.⟦_⟧t -- this is completely trivial because it always returns nothing!
  norm' _ _ = nothing
  -- norm = norm' definitionally!

  -- hope: if we only propositionally truncate, then this has some
  -- (definitional) content, and maybe it can be used for proving some
  -- propositions, e.g. K ≠ S

  infixr 1 _+p_
  data _+p_ {ℓ}{ℓ'}(A : Prop ℓ)(B : Prop ℓ') : Set (ℓ ⊔ ℓ') where
    ι₁ : A → A +p B
    ι₂ : B → A +p B
  Decp : ∀{ℓ} → Prop ℓ → Set ℓ
  Decp A = A +p (A → ⊥)

  _≟_    : ∀{t₀ t₁}(v₀ : Nf t₀)(v₁ : Nf t₁) →
    Decp (_≡_ {A = Σ Tm Nf} (t₀ , v₀) (t₁ , v₁))
  K₀ ≟ K₀ = ι₁ refl
  K₀ ≟ K₁ v₁ = ι₂ λ ()
  K₀ ≟ S₀ = {!!}
  K₀ ≟ S₁ v₁ = {!!}
  K₀ ≟ S₂ v₁ v₂ = {!!}
  K₁ v₀ ≟ K₀ = {!!}
  K₁ v₀ ≟ K₁ v₁ = {!!}
  K₁ v₀ ≟ S₀ = {!!}
  K₁ v₀ ≟ S₁ v₁ = {!!}
  K₁ v₀ ≟ S₂ v₁ v₂ = {!!}
  S₀ ≟ K₀ = {!!}
  S₀ ≟ K₁ v₁ = {!!}
  S₀ ≟ S₀ = {!!}
  S₀ ≟ S₁ v₁ = {!!}
  S₀ ≟ S₂ v₁ v₂ = {!!}
  S₁ v₀ ≟ K₀ = {!!}
  S₁ v₀ ≟ K₁ v₁ = {!!}
  S₁ v₀ ≟ S₀ = {!!}
  S₁ v₀ ≟ S₁ v₁ = {!!}
  S₁ v₀ ≟ S₂ v₁ v₂ = {!!}
  S₂ v₀ v₁ ≟ K₀ = {!!}
  S₂ v₀ v₁ ≟ K₁ v₂ = {!!}
  S₂ v₀ v₁ ≟ S₀ = {!!}
  S₂ v₀ v₁ ≟ S₁ v₂ = {!!}
  S₂ v₀ v₁ ≟ S₂ v₂ v₃ = {!!}

  Iβ' : ∀{u} → I' $ u ≡ u
  Iβ' {u} = {!norm (I' $ u) 10!}
\end{code}
