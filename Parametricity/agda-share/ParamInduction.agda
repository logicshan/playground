
-- Proving induction principles via free theorems from parametricity.
-- The universe check is overridden in some places so that
-- Church-encoded types are still Sets. That may not be necessary, but
-- it avoids things like needing equality and whatnot at multiple
-- levels, and lets one eliminate over the encoded types (which seems
-- handy for the less trivial types).

module ParamInduction where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality

variable a b c : Level

const : ∀{A : Set a} {B : Set b} → A → B → A
const x _ = x

_∘_ : ∀{A : Set a} {B : Set b} {C : Set c} → (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

_⇔_ : Set → Set → Set₁
A ⇔ B = A → B → Set

id : (A : Set a) → A -> A
id A x = x

infixl 0 _$_
_$_ : ∀{A : Set a} {B : A → Set b} → ((x : A) → B x) → (x : A) → B x
f $ x = f x

-- Extensionality of functions is something we'll also be needing.
postulate
  ext : {A : Set a} {B : A → Set b} (f g : (x : A) → B x)
      → (∀ x → f x ≡ g x) → f ≡ g


module Empty where
  -- The empty type is the set that entails any other set.
  {-# NO_UNIVERSE_CHECK #-}
  record ⊥ : Set where
    field absurd : (R : Set) → R
  open ⊥

  postulate
    -- ∀ f. f b = b, total functions must be strict
    free-⊥ : {R S : Set} (bot : ⊥) (f : R → S) → f (bot .absurd R) ≡ bot .absurd S

    pm-⊥ : (A B : Set) (R : A ⇔ B) (b : ⊥) → R (b .absurd A) (b .absurd B)

  -- We don't even need parametricity for the induction principle!
  ⊥-induction : {P : ⊥ → Set} → (b : ⊥) → P b
  ⊥-induction {P} b = b .absurd (P b)


module Unit where
  -- The unit type is the type of the identity function, as it is
  -- the only function with that type.
  {-# NO_UNIVERSE_CHECK #-}
  record ⊤ : Set where
    constructor wrap
    field apply : (R : Set) → R → R
  open ⊤

  postulate
    pm-⊤ : (A B : Set) (R : A ⇔ B) (u : ⊤) (x : A) (y : B)
        → R x y → R (apply u A x) (apply u B y)

  -- ∀ f. f ∘ id = id ∘ f
  free-⊤ : {R S : Set} (u : ⊤) (f : R → S) → ∀ x → f (apply u R x) ≡ apply u S (f x)
  free-⊤ {R} {S} u f x = pm-⊤ R S (λ x y → f x ≡ y) u x (f x) refl

  tt : ⊤
  tt .apply R x = x

  lemma₀ : (u : ⊤) → tt ≡ u
  lemma₀ u = cong wrap
          $ ext (id) (apply u) λ R
          → ext (id R) (apply u R) λ x
          → free-⊤ u (const x) x

  lemma₁ : (u : ⊤) → tt ≡ u
  lemma₁ u = cong wrap
          $ ext (id) (apply u) λ R
          → ext (id R) (apply u R) λ x
          → pm-⊤ R R (λ _ y → x ≡ y) u x x refl

  ⊤-induction : {P : ⊤ → Set} → P tt → ∀ u → P u
  ⊤-induction {P} Pid u rewrite lemma₀ u = Pid

module Product where
  -- Standard representation of pairs
  {-# NO_UNIVERSE_CHECK #-}
  record _×_ (A B : Set) : Set where
    constructor wrap
    field apply : (R : Set) → (A → B → R) → R
  open _×_

  ×-ext : ∀{A B} (l r : A × B) → (∀ R f → l .apply R f ≡ r .apply R f) -> l ≡ r
  ×-ext l r e = cong wrap
              $ ext (apply l) (apply r) λ R
              → ext (apply l R) (apply r R) (e R)

  postulate
    pm-× : ∀{A B} C D
        → (R : C ⇔ D)
        → (p : A × B)
        → (k₀ : A → B → C) (k₁ : A → B → D)
        → (∀ x y → R (k₀ x y) (k₁ x y))
        → R (apply p C k₀) (apply p D k₁)

  free-× : ∀{A B R S}
         → (k₀ : A → B → R) (k₁ : A → B → S)
         → (h : R → S)
         → (p : A × B)
         → (∀ x y → h (k₀ x y) ≡ k₁ x y)
         → h (apply p R k₀) ≡ apply p S k₁
  free-× {A} {B} {R} {S} k₀ k₁ h p pf =
    pm-× R S (λ x y → h x ≡ y) p k₀ k₁ pf

  _,_ : {A B : Set} → A → B → A × B
  (x , y) .apply R k = k x y

  fst : ∀{A B} → A × B → A
  fst {A} pair = pair .apply A (λ x _ → x)

  snd : ∀{A B} → A × B → B
  snd {B = B} pair = pair .apply B (λ _ y → y)

  ×-lemma₀ : ∀{A B} → (p : A × B) → p .apply (A × B) _,_ ≡ p
  ×-lemma₀ {A} {B} p
    = ×-ext q p λ R k → free-× _,_ k (λ q → apply q R k) p (λ _ _ → refl)
    where
    q : A × B
    q = p .apply (A × B) _,_


  ×-lemma₁ : ∀{A B R} → (p : A × B) (k : A → B → R)
          → k (fst p) (snd p) ≡ p .apply R k
  ×-lemma₁ {A} {B} {R} p k =
    subst (λ q → k (fst q) (snd q) ≡ apply p R k) (×-lemma₀ p)
          (free-× _,_ k (λ q → k (fst q) (snd q)) p (λ x y → refl))


  ×-η : ∀{A B} → (p : A × B) → (fst p , snd p) ≡ p
  ×-η {A} {B} p = ×-ext (fst p , snd p) p (λ R k → ×-lemma₁ p k)


  ×-induction : ∀{A B} {P : A × B → Set}
              → ((x : A) → (y : B) → P (x , y))
              → (p : A × B) → P p
  ×-induction {A} {B} {P} f p rewrite sym (×-η p) = f (fst p) (snd p)


module Sigma where
  open Unit

  {-# NO_UNIVERSE_CHECK #-}
  record Σ (A : Set) (P : A -> Set) : Set where
    constructor wrap
    field apply : (R : Set) → ((x : A) → P x → R) → R
  open Σ

  infixr 3 Σ
  syntax Σ A (λ x → P) = Σ[ x ∈ A ] P

  Σ-ext : ∀{A P} (p q : Σ A P)
        → (∀ R (f : (x : A) -> P x -> R) → apply p R f ≡ apply q R f)
        → p ≡ q
  Σ-ext p q f = cong wrap
              $ ext (apply p) (apply q) λ R
              → ext (apply p R) (apply q R) (f R)

  infixr 5 _,_
  _,_ : ∀{A P} → (x : A) → P x → Σ A P
  (x , w) .apply R k = k x w

  postulate
    pm-Σ : ∀{A P} C D (R : C ⇔ D) (p : Σ A P)
         → (k₀ : (x : A) → P x -> C) (k₁ : (x : A) → P x -> D)
         → (∀ x y → R (k₀ x y) (k₁ x y))
         → R (p .apply C k₀) (p .apply D k₁)

    pm-Σ-β : ∀{A P C D} R x y k₀ k₁ Rk
           → pm-Σ {A} {P} C D R (x , y) k₀ k₁ Rk ≡ Rk x y

  Σ-lemma₀ : ∀{A P} → (p : Σ A P) → apply p (Σ A P) _,_ ≡ p
  Σ-lemma₀ {A} {P} p
    = Σ-ext q p λ R f
    → pm-Σ (Σ A P) R (λ q r → q .apply R f ≡ r) p _,_ f (λ _ _ → refl)
    where
    q : Σ A P
    q = apply p (Σ A P) _,_

  Σ-lemma₁ : ∀{A P} → (p : Σ A P) → Σ[ x ∈ A ] Σ[ y ∈ P x ] (x , y) ≡ p
  Σ-lemma₁ {A} {P} p
    = subst Q (Σ-lemma₀ p) (pm-Σ ⊤ (Σ A P) R p (λ _ _ → tt) _,_ Rid)
    where
    Q : Σ A P -> Set
    Q q = Σ[ x ∈ A ] Σ[ y ∈ P x ] (x , y) ≡ q

    R : ⊤ ⇔ Σ A P
    R _ q = Q q

    Rid : ∀ x y → R tt (x , y)
    Rid x y = x , y , refl

  -- If we try to make fst use uncurry, then the P (fst (x , w)) result
  -- type of the lambda expression in snd will be a mess, and we'll need
  -- to *prove* that it's equal to P x (substitution with equality
  -- postulates is the main culprit, I think). The standard Church-encoding
  -- definition normalizes π₀ (x , w) to x, which is much easier.
  fst : ∀{A P} → Σ A P → A
  fst {A} p = p .apply A (λ x _ → x)

  private
    L : ∀{A} (P : A -> Set) → A -> Set
    L {A} P w = Σ[ x ∈ A ] Σ[ y ∈ P x ] x ≡ w

    l : ∀{A P} {x : A} → L P x -> P x
    l {A} {P} {x} p = p .apply (P x) λ w q → q .apply (P x) λ y e → subst P e y

  Σ-lemma₂ : ∀{A P} → (p : Σ A P) → L P (fst p)
  Σ-lemma₂ {A} {P} p = pm-Σ _ _ R p (λ x _ → x) _,_ Rid
    where
    R : A ⇔ Σ A P
    R w _ = L P w

    Rid : ∀ x y → R x (x , y)
    Rid x y = x , y , refl

  snd : ∀{A P} → (p : Σ A P) → P (fst p)
  snd {A} {P} p = l (Σ-lemma₂ p)

  snd-β : ∀{A P} (x : A) y → snd {A} {P} (x , y) ≡ y
  snd-β {A} {P} x y = cong l (pm-Σ-β R x y (λ x _ → x) _,_ Rid)
    where
    R : A ⇔ Σ A P
    R w q = Σ[ x ∈ A ] Σ[ y ∈ P x ] x ≡ w

    Rid : ∀ x y → R x (x , y)
    Rid x y = x , y , refl

  Σ-η : ∀{A P} (p : Σ A P) → (fst p , snd p) ≡ p
  Σ-η {A} {P} p = Σ-ext (fst p , snd p) p λ Z k
        → let R : Σ A P ⇔ Z
              R q y = k (fst q) (snd q) ≡ y
              Q : Σ A P -> Set
              Q q = k (fst q) (snd q) ≡ p .apply Z k
           in subst Q (Σ-lemma₀ p) (pm-Σ _ _ R p _,_ k λ x y → cong (k x) (snd-β x y))

  uncurry : ∀{A P} {C : Σ A P → Set}
          → (f : (x : A) (y : P x) → C (x , y))
          → ∀ p → C p
  uncurry {A} {P} {C} f p = subst C (Σ-η p) (f (fst p) (snd p))


module Boolean where
  open Sigma

  -- A simpler disjunction first
  {-# NO_UNIVERSE_CHECK #-}
  record Bool : Set where
    constructor wrap
    field apply : (R : Set) → R → R → R
  open Bool

  true : Bool
  true .apply _ t _ = t

  false : Bool
  false .apply _ _ f = f

  Bool-ext : ∀(b c : Bool)
          → (∀ R t f → apply b R t f ≡ apply c R t f)
          → b ≡ c
  Bool-ext b c f = cong wrap
                $ ext (apply b)     (apply c)   λ R
                → ext (apply b R)   (apply c R) λ t
                → ext (apply b R t) (apply c R t) (f R t)

  postulate
    pm-B : ∀ A B → (R : A ⇔ B) → (b : Bool)
                → (x₀ y₀ : A) (x₁ y₁ : B)
                → R x₀ x₁ → R y₀ y₁
                → R (b .apply A x₀ y₀) (b .apply B x₁ y₁)

  free-B : ∀{R S} → (f : R → S) → (x y : R)
        → (b : Bool) → f (b .apply R x y) ≡ b .apply S (f x) (f y)
  free-B {R} {S} f x y b =
    pm-B R S (λ x y → f x ≡ y) b x y (f x) (f y) refl refl

  B-lemma₀ : (b : Bool) → apply b Bool true false ≡ b
  B-lemma₀ b = Bool-ext ab b λ R t f
            → free-B (λ d → apply d R t f) true false b
    where
    ab : Bool
    ab = apply b Bool true false

  B-lemma₁ : ∀{A} → (x : A) → (b : Bool) → x ≡ apply b A x x
  B-lemma₁ {A} x b = free-B (const x) x x b

  B-induction : ∀{P : Bool → Set} → P true → P false → ∀ b → P b
  B-induction {P} Pt Pf b
    = subst P (trans fact (B-lemma₀ b)) (snd (b .apply _ t f))
    where
    t f : Σ Bool P
    t = true , Pt
    f = false , Pf

    R : Bool ⇔ Σ Bool P
    R b p = fst p ≡ b

    fact : fst (b .apply _ t f) ≡ b .apply Bool true false
    fact = free-B fst t f b


module Sum where
  open Sigma
  open Σ

  {-# NO_UNIVERSE_CHECK #-}
  record _⊎_ (A B : Set) : Set where
    constructor wrap
    field apply : (R : Set) → (A → R) → (B → R) → R
  open _⊎_

  ⊎-ext : ∀{A B} (s t : A ⊎ B)
        → (∀ R l r → s .apply R l r ≡ t .apply R l r)
        → s ≡ t
  ⊎-ext s t f = cong wrap
              $ ext (apply s) (apply t) λ R
              → ext (apply s R) (apply t R) λ l
              → ext (apply s R l) (apply t R l) (f R l)

  postulate
    pm-⊎ : ∀{A B} C D
        → (R : C ⇔ D)
        → (s : A ⊎ B)
        → (l₀ : A → C) (r₀ : B → C)
        → (l₁ : A → D) (r₁ : B → D)
        → (∀ x → R (l₀ x) (l₁ x))
        → (∀ y → R (r₀ y) (r₁ y))
        → R (s .apply C l₀ r₀) (s .apply D l₁ r₁)

  free-⊎ : {A B R S : Set}
        → (h : R → S)
        → (l₀ : A → R) → (r₀ : B → R)
        → (l₁ : A → S) → (r₁ : B → S)
        → (s : A ⊎ B)
        → (∀ x → h (l₀ x) ≡ l₁ x)
        → (∀ y → h (r₀ y) ≡ r₁ y)
        → h (s .apply R l₀ r₀) ≡ s .apply S l₁ r₁
  free-⊎ {A} {B} {R} {S} h l₀ r₀ l₁ r₁ s pfl pfr =
    pm-⊎ R S
         (λ x y → h x ≡ y)
         s l₀ r₀ l₁ r₁ pfl pfr

  inl : ∀{A B} → A → A ⊎ B
  inl x .apply R f _ = f x

  inr : ∀{A B} → B → A ⊎ B
  inr y .apply R _ g = g y

  ⊎-lemma₀ : ∀{A B} → (s : A ⊎ B) → s .apply (A ⊎ B) inl inr ≡ s
  ⊎-lemma₀ {A} {B} s = ⊎-ext t s λ R l r
                    → free-⊎ (λ v → v .apply R l r)
                             inl inr l r s
                             (λ x → refl) (λ y → refl)
    where
    t : A ⊎ B
    t = s .apply (A ⊎ B) inl inr

  ⊎-lemma₁ : ∀{A B C : Set} → (f : A → C) (g : B → C) → (s : A ⊎ B)
          → (Σ A λ x → s .apply C f g ≡ f x)
          ⊎ (Σ B λ y → s .apply C f g ≡ g y)
  ⊎-lemma₁ {A} {B} {C} f g s
    = pm-⊎ C C R s f g f g
        (λ x → inl (x , refl))
        (λ y → inr (y , refl))
    where
    R : C → C → Set
    R _ e = (Σ A λ x → e ≡ f x) ⊎ (Σ B λ y → e ≡ g y)

  ⊎-lemma₂ : ∀{A B} → (s : A ⊎ B)
          → (Σ A λ x → s ≡ inl x) ⊎ (Σ B λ y → s ≡ inr y)
  ⊎-lemma₂ {A} {B} s rewrite sym (⊎-lemma₀ s) = ⊎-lemma₁ inl inr s


  ⊎-induction : ∀{A B} {P : A ⊎ B → Set}
              → (∀ x → P (inl x)) → (∀ y → P (inr y))
              → (s : A ⊎ B) → P s
  ⊎-induction {A} {B} {P} pfl pfr s =
    ⊎-lemma₂ s .apply (P s)
      (λ sg → sg .apply (P s) (λ x s≡inlx → subst P (sym s≡inlx) (pfl x)))
      (λ sg → sg .apply (P s) (λ y s≡inry → subst P (sym s≡inry) (pfr y)))



module Nat where
  open Sigma

  {-# NO_UNIVERSE_CHECK #-}
  record ℕ : Set where
    constructor wrap
    field apply : (R : Set) → R → (R → R) → R
  open ℕ

  zero : ℕ
  zero .apply R z s = z

  suc : ℕ → ℕ
  suc n .apply R z s = s (n .apply R z s)

  ℕ-ext : (m n : ℕ)
        → (∀ R z s → m .apply R z s ≡ n .apply R z s)
        → m ≡ n
  ℕ-ext m n f = cong wrap
              $ ext (apply m)     (apply n)   λ R
              → ext (apply m R)   (apply n R) λ z
              → ext (apply m R z) (apply n R z) (f R z)

  postulate
    pm-ℕ : (A B : Set) (R : A ⇔ B) (s₀ : A → A) (s₁ : B → B) (z₀ : A) (z₁ : B) (n : ℕ)
        → (∀ x₀ x₁ → R x₀ x₁ → R (s₀ x₀) (s₁ x₁))
        → R z₀ z₁ → R (apply n A z₀ s₀) (apply n B z₁ s₁)

  free-ℕ : {R S : Set} (x : R) (f : R → S) (g : R → R) (h : S → S) (n : ℕ)
        → (∀ x → f (g x) ≡ h (f x))
        → f (apply n R x g) ≡ apply n S (f x) h
  free-ℕ x f g h n pre = pm-ℕ _ _
    (λ x y → f x ≡ y) g h x (f x) n
    (λ x y pf → subst (λ z → f (g x) ≡ h z) pf (pre x)) refl

  ℕ-lemma₀ : (n : ℕ) → n .apply ℕ zero suc ≡ n
  ℕ-lemma₀ n = ℕ-ext (n .apply ℕ zero suc) n λ R z s
            → free-ℕ zero (λ m → m .apply R z s) suc s n (λ m → refl)

  induction : {P : ℕ → Set}
            → P zero
            → (∀ n → P n → P (suc n))
            → ∀ n → P n
  induction {P} Pz Ps n
    = subst P (trans fact (ℕ-lemma₀ n)) (snd out)
    where
    Z = Σ ℕ P

    R : ℕ ⇔ Z
    R n p = n ≡ fst p

    z : Z
    z = zero , Pz

    s : Z -> Z
    s p = let n = fst p in (suc n , Ps n (snd p))

    Rs : ∀ m x → R m x -> R (suc m) (s x)
    Rs m x Rmx = cong suc Rmx

    out : Z
    out = n .apply Z z s

    fact : fst out ≡ n .apply ℕ zero suc
    fact = free-ℕ z fst s suc n λ _ → refl
