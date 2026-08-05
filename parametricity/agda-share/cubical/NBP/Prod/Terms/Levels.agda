
module NBP.Prod.Terms.Levels where

open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

open import NBP.Facts
open import NBP.Prod.Types
open import NBP.Prod.Terms.Core

private variable
  Γ₀ Γ₁ : Cx
  A₀ A₁ B₀ B₁ : Ty

left : Ty → Ty
left (A * _) = A
left (A ⇒ _) = A
left _       = ⊤

right : Ty → Ty
right (_ * B) = B
right (_ ⇒ B) = B
right _       = ⊤

left-right-*
  : (A*B : A₀ * B₀ ≡ A₁ * B₁)
  → (let A'*B' = λ i → left (A*B i) * right (A*B i))
  → A'*B' ≡ A*B
left-right-* A*B = isSet-Ty _ _ A'*B' A*B
  where A'*B' = λ i → left (A*B i) * right (A*B i)

left-right-⇒
  : (A⇒B : A₀ ⇒ B₀ ≡ A₁ ⇒ B₁)
  → (let A'⇒B' = λ i → left (A⇒B i) ⇒ right (A⇒B i))
  → A'⇒B' ≡ A⇒B
left-right-⇒ A⇒B = isSet-Ty _ _ A'⇒B' A⇒B
  where A'⇒B' = λ i → left (A⇒B i) ⇒ right (A⇒B i)

module isSetStx where
  open Stx
  Co : (Γ : Γ₀ ≡ Γ₁) (A : A₀ ≡ A₁) (l : Tm Γ₀ A₀) (r : Tm Γ₁ A₁) → Type

  Co Γ A (va u) (va v) = PathP (λ i → A i ∈ Γ i) u v
  Co Γ A tt tt = Unit
  Co Γ A (w , y) (x , z) =
    Co Γ (cong left A) w x × Co Γ (cong right A) y z
  Co Γ A (π₁ {B = B₀} x) (π₁ {B = B₁} y) =
    Σ[ B ∈ B₀ ≡ B₁ ] Co Γ (λ i → A i * B i) x y
  Co Γ B (π₂ {A = A₀} x) (π₂ {A = A₁} y) =
    Σ[ A ∈ A₀ ≡ A₁ ] Co Γ (λ i → A i * B i) x y
  Co Γ A (la x) (la y) =
    Co (cong₂ _∷_ Γ (cong left A)) (cong right A) x y
  Co Γ B (f $ x) (g $ y) =
    Σ[ A ∈ _ ≡ _ ] Co Γ (λ i → A i ⇒ B i) f g × Co Γ A x y
  Co _ _ _ _ = ⊥

  isProp-Co : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r → isProp (Co Γ A l r)
  isProp-Co (va u) (va v) = isOfHLevelPathP' 1 (isSet-∈ _ _) u v
  isProp-Co tt tt = isPropUnit
  isProp-Co (w , y) (x , z) = isProp× (isProp-Co w x) (isProp-Co y z)
  isProp-Co (π₁ l) (π₁ r) = isPropΣ (isSet-Ty _ _) λ _ → isProp-Co l r
  isProp-Co (π₂ l) (π₂ r) = isPropΣ (isSet-Ty _ _) λ _ → isProp-Co l r
  isProp-Co (la l) (la r) = isProp-Co l r
  isProp-Co (f $ x) (g $ y) =
    isPropΣ (isSet-Ty _ _) λ _ → isProp× (isProp-Co f g) (isProp-Co x y)

  -- off diagonal
  isProp-Co (va _) tt = isProp⊥
  isProp-Co (va _) (_ , _) = isProp⊥
  isProp-Co (va _) (π₁ _) = isProp⊥
  isProp-Co (va _) (π₂ _) = isProp⊥
  isProp-Co (va _) (la _) = isProp⊥
  isProp-Co (va _) (_ $ _) = isProp⊥

  isProp-Co tt (va _) = isProp⊥
  isProp-Co tt (_ , _) = isProp⊥
  isProp-Co tt (π₁ _) = isProp⊥
  isProp-Co tt (π₂ _) = isProp⊥
  isProp-Co tt (la _) = isProp⊥
  isProp-Co tt (_ $ _) = isProp⊥

  isProp-Co (_ , _) (va _) = isProp⊥
  isProp-Co (_ , _) tt = isProp⊥
  isProp-Co (_ , _) (π₁ _) = isProp⊥
  isProp-Co (_ , _) (π₂ _) = isProp⊥
  isProp-Co (_ , _) (la _) = isProp⊥
  isProp-Co (_ , _) (_ $ _) = isProp⊥

  isProp-Co (π₁ _) (va _) = isProp⊥
  isProp-Co (π₁ _) tt = isProp⊥
  isProp-Co (π₁ _) (_ , _) = isProp⊥
  isProp-Co (π₁ _) (π₂ _) = isProp⊥
  isProp-Co (π₁ _) (la _) = isProp⊥
  isProp-Co (π₁ _) (_ $ _) = isProp⊥

  isProp-Co (π₂ _) (va _) = isProp⊥
  isProp-Co (π₂ _) tt = isProp⊥
  isProp-Co (π₂ _) (_ , _) = isProp⊥
  isProp-Co (π₂ _) (π₁ _) = isProp⊥
  isProp-Co (π₂ _) (la _) = isProp⊥
  isProp-Co (π₂ _) (_ $ _) = isProp⊥

  isProp-Co (la _) (va _) = isProp⊥
  isProp-Co (la _) tt = isProp⊥
  isProp-Co (la _) (_ , _) = isProp⊥
  isProp-Co (la _) (π₁ _) = isProp⊥
  isProp-Co (la _) (π₂ _) = isProp⊥
  isProp-Co (la _) (_ $ _) = isProp⊥

  isProp-Co (_ $ _) (va _) = isProp⊥
  isProp-Co (_ $ _) tt = isProp⊥
  isProp-Co (_ $ _) (_ , _) = isProp⊥
  isProp-Co (_ $ _) (π₁ _) = isProp⊥
  isProp-Co (_ $ _) (π₂ _) = isProp⊥
  isProp-Co (_ $ _) (la _) = isProp⊥

  dec : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r
      → Co Γ A l r → PathP (λ i → Tm (Γ i) (A i)) l r
  dec (va u) (va v) p i = va (p i)
  dec {Γ₀} {Γ = Γ} {A = T} tt tt c = transp P i0 (λ _ → tt)
    where
    ⊤-T : refl ≡ T
    ⊤-T = isSet-Ty ⊤ ⊤ refl T
    P : I → Type
    P k = PathP (λ i → Tm (Γ i) (⊤-T k i)) tt tt
  dec {Γ = Γ} {A = A*B} (w , y) (x , z) (c , d) =
    transp P i0 (congP₂ (λ _ → Tm._,_) (dec w x c) (dec y z d))
    where
    P : I → Type
    P k = PathP (λ i → Tm (Γ i) (left-right-* A*B k i)) (w , y) (x , z)
  dec (π₁ p) (π₁ q) (_ , c) i = π₁ (dec p q c i)
  dec (π₂ p) (π₂ q) (_ , c) i = π₂ (dec p q c i)
  dec {Γ = Γ} {A = A⇒B} (la x) (la y) c =
    transp P i0 (congP (λ _ → Tm.la) (dec x y c))
    where
    P : I → Type
    P k = PathP (λ i → Tm (Γ i) (left-right-⇒ A⇒B k i)) (la x) (la y)
  dec (f $ x) (g $ y) (_ , h , z) i =
    dec f g h i $ dec x y z i

  Co-refl : ∀(e : Tm Γ A) → Co refl refl e e
  Co-refl (va v) = refl
  Co-refl tt = _
  Co-refl (l , r) = Co-refl l , Co-refl r
  Co-refl (π₁ p) = refl , Co-refl p
  Co-refl (π₂ p) = refl , Co-refl p
  Co-refl (la e) = Co-refl e
  Co-refl (f $ e) = refl , Co-refl f , Co-refl e

instance
  IdentityCode-Tm : IdentityCode (Stx.Tm Γ A) ℓ-zero
  IdentityCode-Tm .Code = isSetStx.Co refl refl
  IdentityCode-Tm .isProp-Code = isSetStx.isProp-Co
  IdentityCode-Tm .reflexive = isSetStx.Co-refl
  IdentityCode-Tm .decode = isSetStx.dec

isSet-Tm : ∀ Γ A → isSet (Stx.Tm Γ A)
isSet-Tm _ _ = IdentityCode→isSet

module isSetSem where
  open Sem
  CoNe : (Γ : Γ₀ ≡ Γ₁) (A : A₀ ≡ A₁) (l : Ne Γ₀ A₀) (r : Ne Γ₁ A₁) → Type
  CoNo : (Γ : Γ₀ ≡ Γ₁) (A : A₀ ≡ A₁) (l : No Γ₀ A₀) (r : No Γ₁ A₁) → Type

  CoNe Γ A (va u) (va v) = PathP (λ i → A i ∈ Γ i) u v

  CoNe Γ A (π₁ {B = B₀} l) (π₁ {B = B₁} r) =
    Σ[ B ∈ B₀ ≡ B₁ ] CoNe Γ (λ i → A i * B i) l r

  CoNe Γ B (π₂ {A = A₀} l) (π₂ {A = A₁} r) =
    Σ[ A ∈ A₀ ≡ A₁ ] CoNe Γ (λ i → A i * B i) l r

  CoNe Γ B (f $ x) (g $ y) =
    Σ[ A ∈ _ ≡ _ ] CoNe Γ (λ i → A i ⇒ B i) f g × CoNo Γ A x y
  CoNe _ _ _ _ = ⊥

  CoNo Γ A tt tt = Unit
  CoNo Γ A*B (w , y) (x , z) =
    CoNo Γ (cong left A*B) w x × CoNo Γ (cong right A*B) y z
  CoNo Γ A⇒B (la x) (la y) =
    CoNo (cong₂ _∷_ Γ (cong left A⇒B)) (cong right A⇒B) x y
  CoNo Γ A (ne x) (ne y) = CoNe Γ A x y
  CoNo _ _ _ _ = ⊥

  isProp-CoNe : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r → isProp (CoNe Γ A l r)
  isProp-CoNo : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r → isProp (CoNo Γ A l r)

  isProp-CoNe (va u) (va v) = isOfHLevelPathP' 1 (isSet-∈ _ _) u v
  isProp-CoNe (π₁ l) (π₁ r) =
    isPropΣ (isSet-Ty _ _) λ B → isProp-CoNe l r
  isProp-CoNe (π₂ l) (π₂ r) =
    isPropΣ (isSet-Ty _ _) λ A → isProp-CoNe l r
  isProp-CoNe (f $ x) (g $ y) =
    isPropΣ (isSet-Ty _ _) λ A → isProp× (isProp-CoNe f g) (isProp-CoNo x y)

  isProp-CoNe (va _) (π₁ _) = isProp⊥
  isProp-CoNe (va _) (π₂ _) = isProp⊥
  isProp-CoNe (va _) (_ $ _) = isProp⊥
  isProp-CoNe (π₁ l) (va _) = isProp⊥
  isProp-CoNe (π₁ l) (π₂ r) = isProp⊥
  isProp-CoNe (π₁ l) (r $ x) = isProp⊥
  isProp-CoNe (π₂ l) (va x) = isProp⊥
  isProp-CoNe (π₂ l) (π₁ r) = isProp⊥
  isProp-CoNe (π₂ l) (r $ x) = isProp⊥
  isProp-CoNe (l $ x) (va x₁) = isProp⊥
  isProp-CoNe (l $ x) (π₁ r) = isProp⊥
  isProp-CoNe (l $ x) (π₂ r) = isProp⊥

  isProp-CoNo tt tt = isPropUnit
  isProp-CoNo (w , y) (x , z) =
    isProp× (isProp-CoNo w x) (isProp-CoNo y z)
  isProp-CoNo (la l) (la r) = isProp-CoNo l r
  isProp-CoNo (ne x) (ne y) = isProp-CoNe x y

  isProp-CoNo tt (r , r₁) = isProp⊥
  isProp-CoNo tt (la r) = isProp⊥
  isProp-CoNo tt (ne x) = isProp⊥
  isProp-CoNo (l , l₁) tt = isProp⊥
  isProp-CoNo (l , l₁) (la r) = isProp⊥
  isProp-CoNo (l , l₁) (ne x) = isProp⊥
  isProp-CoNo (la l) tt = isProp⊥
  isProp-CoNo (la l) (r , r₁) = isProp⊥
  isProp-CoNo (la l) (ne x) = isProp⊥
  isProp-CoNo (ne x) tt = isProp⊥
  isProp-CoNo (ne x) (r , r₁) = isProp⊥
  isProp-CoNo (ne x) (la r) = isProp⊥

  dec-ne : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r
         → CoNe Γ A l r → PathP (λ i → Ne (Γ i) (A i)) l r
  dec-no : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r
         → CoNo Γ A l r → PathP (λ i → No (Γ i) (A i)) l r

  dec-ne (va v) (va u) c i = va (c i)
  dec-ne (π₁ l) (π₁ r) (_ , c) i = π₁ (dec-ne l r c i)
  dec-ne (π₂ l) (π₂ r) (_ , c) i = π₂ (dec-ne l r c i)
  dec-ne (f $ x) (g $ y) (_ , h , z) i =
    dec-ne f g h i $ dec-no x y z i

  dec-no {Γ₀} {Γ = Γ} {A = T} tt tt _ =
    transp P i0 (λ _ → tt)
    where
    ⊤-T : refl ≡ T
    ⊤-T = isSet-Ty ⊤ ⊤ refl T
    P : I → Type
    P k = PathP (λ i → No (Γ i) (⊤-T k i)) tt tt
  dec-no {Γ = Γ} {A = A*B} (w , y) (x , z) (c , d) =
    transp P i0 (congP₂ (λ _ → No._,_) (dec-no w x c) (dec-no y z d))
    where
    P : I → Type
    P k = PathP (λ i → No (Γ i) (left-right-* A*B k i)) (w , y) (x , z)
  dec-no {Γ = Γ} {A = A⇒B} (la l) (la r) c =
    transp P i0 (congP (λ _ → No.la) (dec-no l r c))
    where
    P : I → Type
    P k = PathP (λ i → No (Γ i) (left-right-⇒ A⇒B k i)) (la l) (la r)
  dec-no (ne x) (ne y) c i = ne (dec-ne x y c i)

  CoNo-refl : ∀(e : No Γ A) → CoNo refl refl e e
  CoNe-refl : ∀(e : Ne Γ A) → CoNe refl refl e e

  CoNo-refl tt = _
  CoNo-refl (l , r) = CoNo-refl l , CoNo-refl r
  CoNo-refl (la e) = CoNo-refl e
  CoNo-refl (ne x) = CoNe-refl x

  CoNe-refl (va x) = refl
  CoNe-refl (π₁ e) = refl , CoNe-refl e
  CoNe-refl (π₂ e) = refl , CoNe-refl e
  CoNe-refl (f $ x) = refl , CoNe-refl f , CoNo-refl x

  enc-ne : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r
         → PathP (λ i → Ne (Γ i) (A i)) l r
         → CoNe Γ A l r
  enc-ne {Γ = Γ} {A = A} l r p =
    transport (λ i → CoNe (λ j → Γ (j ∧ i)) (λ j → A (j ∧ i)) l (p i)) (CoNe-refl l)

  enc-no : ∀{Γ : Γ₀ ≡ Γ₁} {A : A₀ ≡ A₁} l r
         → PathP (λ i → No (Γ i) (A i)) l r
         → CoNo Γ A l r
  enc-no {Γ = Γ} {A = A} l r p =
    transport (λ i → CoNo (λ j → Γ (j ∧ i)) (λ j → A (j ∧ i)) l (p i)) (CoNo-refl l)

instance
  IdentityCode-Ne : IdentityCode (Sem.Ne Γ A) ℓ-zero
  IdentityCode-Ne .Code = isSetSem.CoNe refl refl
  IdentityCode-Ne .isProp-Code = isSetSem.isProp-CoNe
  IdentityCode-Ne .reflexive = isSetSem.CoNe-refl
  IdentityCode-Ne .decode = isSetSem.dec-ne

  IdentityCode-No : IdentityCode (Sem.No Γ A) ℓ-zero
  IdentityCode-No .Code = isSetSem.CoNo refl refl
  IdentityCode-No .isProp-Code = isSetSem.isProp-CoNo
  IdentityCode-No .reflexive = isSetSem.CoNo-refl
  IdentityCode-No .decode = isSetSem.dec-no

isSet-Ne : ∀ Γ A → isSet (Sem.Ne Γ A)
isSet-Ne Γ A = IdentityCode→isSet

isSet-No : ∀ Γ A → isSet (Sem.No Γ A)
isSet-No Γ A = IdentityCode→isSet

