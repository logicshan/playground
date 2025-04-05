
-- A simple inductive-recursive universe ala Martin-Löf, together
-- with an embedding of some set theory as well-founded trees over
-- the universe.

module IRSetTheory where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Data.Sum

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data W (A : Set) (T : A → Set) : Set where
  _◂_ : (x : A) (f : T x → W A T) → W A T

ann : ∀{A T} → W A T → A
ann (x ◂ _) = x

fun : ∀{A T} → (t : W A T) → T (ann t) → W A T
fun (_ ◂ f) = f

naughty : {A : Set} → Fin 0 → A
naughty ()

-- A simple propositional universe.
data P : Set where
  ⊥ ⊤ : P
  _∧_ _∨_ _⇒_ : P → P → P

Prf : P → Set
Prf ⊥       = Fin 0
Prf ⊤       = Fin 1
Prf (p ∧ q) = Prf p × Prf q
Prf (p ∨ q) = Prf p ⊎ Prf q
Prf (p ⇒ q) = Prf p → Prf q

-- Oops
lem : ∀ p → Prf (p ∨ (p ⇒ ⊥))
lem ⊥       = inj₂ (λ f → f)
lem ⊤       = inj₁ zero
lem (p ∧ q) with lem p
... | inj₂ ¬p = inj₂ (¬p ∘ proj₁)
... | inj₁ p! with lem q
... | inj₂ ¬q = inj₂ (¬q ∘ proj₂)
... | inj₁ q! = inj₁ (p! , q!)
lem (p ∨ q) with lem p
... | inj₁ p! = inj₁ (inj₁ p!)
... | inj₂ ¬p with lem q
... | inj₁ q! = inj₁ (inj₂ q!)
... | inj₂ ¬q = inj₂ [ ¬p , ¬q ]
lem (p ⇒ q) with lem q
... | inj₁ q! = inj₁ (const q!)
... | inj₂ ¬q with lem p
... | inj₂ ¬p = inj₁ (naughty ∘ ¬p)
... | inj₁ p! = inj₂ (λ f → ¬q (f p!))

mutual
  -- The universe is closed under pi, sigma, w, coproduct,
  -- equality, naturals and finite sets, although that produces
  -- some redundancy. It also includes the above propositional
  -- universe.
  data U : Set where
    π σ w : (s : U) (f : T s → U) → U
    _⊕_   : (s t : U) → U
    i     : (s : U) → (x y : T s) → U
    nat   : U
    fin   : ℕ → U
    p     : U
    prf   : P → U

  T : U → Set
  T (π s f)   = (x : T s) → T (f x)
  T (σ s f)   = Σ (T s) \x → T (f x)
  T (w s f)   = W (T s) \x → T (f x)
  T (s ⊕ t)   = T s ⊎ T t
  T (i s x y) = x ≡ y
  T nat       = ℕ
  T (fin k)   = Fin k
  T p         = P
  T (prf q)   = Prf q

-- V is the universe of sets.
V : Set
V = W U T

-- Two sets are equal if for every index in one, there is an index in
-- the other that produces equal sets.
_≃_ : V → V → Set
(j ◂ f) ≃ (k ◂ g) = (∀ e₁ → ∃ \e₂ → f e₁ ≃ g e₂) × (∀ e₂ → ∃ \e₁ → f e₁ ≃ g e₂)

-- Set equality is reflexive...
≃-refl : ∀ x → x ≃ x
≃-refl (j ◂ f) = (\e → (e , ≃-refl (f e))) , (\e → (e , ≃-refl (f e)))

-- ... symmetric ...
≃-sym : ∀ x y → x ≃ y → y ≃ x
≃-sym (j ◂ f) (k ◂ g) x≃y =
    (\e₁ → let pf = proj₂ x≃y e₁ in proj₁ pf , ≃-sym _ (g e₁) (proj₂ pf))
  , (\e₂ → let pf = proj₁ x≃y e₂ in proj₁ pf , ≃-sym (f e₂) _ (proj₂ pf))

-- ... and transitive.
≃-trans : ∀ x y z → x ≃ y → y ≃ z → x ≃ z
≃-trans (j ◂ f) (k ◂ g) (l ◂ h) (x→y , x←y) (y→z , y←z) = x→z , x←z
 where
 x→z : ∀ e₁ → ∃ \e₃ → f e₁ ≃ h e₃
 x→z e₁ with x→y e₁
 ... | (e₂ , fe₁≃ge₂) with y→z e₂
 ...   | (e₃ , ge₂≃he₃) = (e₃ , ≃-trans (f e₁) (g e₂) (h e₃) fe₁≃ge₂ ge₂≃he₃)

 x←z : ∀ e₃ → ∃ \e₁ → f e₁ ≃ h e₃
 x←z e₃ with y←z e₃
 ... | (e₂ , ge₂≃he₃) with x←y e₂
 ...   | (e₁ , fe₁≃ge₂) = (e₁ , ≃-trans (f e₁) (g e₂) (h e₃) fe₁≃ge₂ ge₂≃he₃)

-- A set is an element of another set if there is an index in the latter
-- that produces a set equal to the former.
_∈_ : V → V → Set
x ∈ (j ◂ f) = ∃ \e → x ≃ f e

-- A set is a subset of another if all elements of the former are elements
-- of the latter.
_⊆_ : V → V → Set
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- The subset relation is reflextive...
⊆-refl : ∀ x → x ⊆ x
⊆-refl x z z∈x = z∈x

-- ... transitive ...
⊆-trans : ∀ x y z → x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x y z x⊆y y⊆z u u∈x = y⊆z u (x⊆y u u∈x)

-- ... and anti-symmetric
⊆-antisym : ∀ x y → x ⊆ y → y ⊆ x → x ≃ y
⊆-antisym (j ◂ f) (k ◂ g) x⊆y y⊆x = x→y , x←y
 where
 x→y : ∀ e₁ → ∃ \e₂ → f e₁ ≃ g e₂
 x→y e₁ = x⊆y (f e₁) (e₁ , ≃-refl (f e₁))


 x←y : ∀ e₂ → ∃ \e₁ → f e₁ ≃ g e₂
 x←y e₂ with y⊆x (g e₂) (e₂ , ≃-refl (g e₂))
 ... | e₁ , ge₂≃fe₁ = e₁ , ≃-sym (g e₂) (f e₁) ge₂≃fe₁

-- If two sets are equal, they are members of the same sets.
≃-substˡ : ∀ x y z → x ≃ y → x ∈ z → y ∈ z
≃-substˡ x y (j ◂ f) x≃y (e , x≃fe)
  = (e , ≃-trans y x (f e) (≃-sym x y x≃y) x≃fe)

-- Equal sets are subsets of one another.
≃-⊆₁ : ∀ x y → x ≃ y → x ⊆ y
≃-⊆₁ (j ◂ f) (k ◂ g) (x→y , x←y) z (e , z≃fe) with x→y e
... | (e' , fe≃ge') = (e' , ≃-trans z (f e) (g e') z≃fe fe≃ge')

≃-⊆₂ : ∀ x y → x ≃ y → y ⊆ x
≃-⊆₂ (j ◂ f) (k ◂ g) (x→y , x←y) z (e , z≃ge) with x←y e
... | (e' , fe'≃ge)
  = (e' , ≃-trans z (g e) (f e') z≃ge (≃-sym (f e') (g e) fe'≃ge))

-- The empty set
∅ : V
∅ = fin 0 ◂ naughty

-- The empty set is empty.
∅-empty : ∀ z → ¬ z ∈ ∅
∅-empty z z∈∅ = naughty (proj₁ z∈∅)

-- The empty set is a subset of every set.
∅-subset : ∀ x → ∅ ⊆ x
∅-subset x z z∈∅ with ∅-empty z z∈∅
... | ()

pair : V → V → Fin 2 → V
pair x _ zero           = x
pair _ y (suc zero)     = y
pair _ _ (suc (suc ()))

-- Unordered pair
⟨_,_⟩ : V → V → V
⟨ x , y ⟩ = fin 2 ◂ pair x y

∈-pair₁ : ∀ x y → x ∈ ⟨ x , y ⟩
∈-pair₁ x y = zero , ≃-refl x

∈-pair₂ : ∀ x y → y ∈ ⟨ x , y ⟩
∈-pair₂ x y = suc zero , ≃-refl y

-- Pairing respects equality
≃-⟨⟩ : ∀ x y z u → x ≃ z → y ≃ u → ⟨ x , y ⟩ ≃ ⟨ z , u ⟩
≃-⟨⟩ x y z u x≃z y≃u = to , from
 where
 to : ∀ e₁ → ∃ \e₂ → pair x y e₁ ≃ pair z u e₂
 to zero       = zero , x≃z
 to (suc zero) = suc zero , y≃u
 to (suc (suc ()))

 from : ∀ e₂ → ∃ \e₁ → pair x y e₁ ≃ pair z u e₂
 from zero       = zero , x≃z
 from (suc zero) = suc zero , y≃u
 from (suc (suc ()))

-- Set union
⋃ : V → V
⋃ (j ◂ f) = σ j (ann ∘ f) ◂ uncurry (fun ∘ f)

-- Elements of x are subsets of the union of x.
∈-⋃ : ∀ x y → y ∈ x → y ⊆ ⋃ x
∈-⋃ (j ◂ f) y (e₁ , y≃fe₁) z z∈y with ≃-⊆₁ y (f e₁) y≃fe₁ z z∈y
... | z∈fe₁ = (e₁ , proj₁ s) , proj₂ s
 where
 -- This cannot be eliminated (as far as I know). We need to refine
 -- 'f e₁' together with 'z∈fe₁' after we've specified that we're creating
 -- a 'T (ann (f e₁))'. So, it needs to be an auxiliary, because you can't
 -- do matching inside an expression.
 s : Σ (T (ann (f e₁))) (λ e₂ → z ≃ fun (f e₁) e₂)
 s with f e₁ | z∈fe₁
 ... | k ◂ g | e₂ , z≃ge₂ = e₂ , z≃ge₂

{- This has the same issue as above, only it's buried under even more complex
   stuff.
≃-⋃ : ∀ x y → x ≃ y → ⋃ x ≃ ⋃ y
≃-⋃ (j ◂ f) (k ◂ g) (x→y , x←y) = to , {!!}
 where
 to : ∀(e₁ : Σ (T j) (T ∘ ann ∘ f)) 
    → Σ (Σ (T k) (T ∘ ann ∘ g)) \e₂
    → uncurry {C = const V} (fun ∘ f) e₁ ≃ uncurry {C = const V} (fun ∘ g) e₂
 to (e₁₁ , e₁₂) with x→y e₁₁
 ... | e₂₁ , fe₁₁≃ge₂₁ with f e₁₁ | g e₂₁ 
 ...  | j' ◂ f' | k' ◂ g' with proj₁ fe₁₁≃ge₂₁ e₁₂
 ...   | e₂₂ , f'e≃g'e = {!e₂₁ , e₂₂!} , {!!}
-}

mutual
  fin-enum : (k : ℕ) → Fin k → V
  fin-enum zero    ()
  fin-enum (suc k) zero     = Fn k
  fin-enum (suc k) (suc fn) = fin-enum k fn

  -- Finite ordinals
  Fn : ℕ → V
  Fn k = fin k ◂ fin-enum k

-- Each finite ordinal is a subset of its successor ordinal.
fn-⊆ : ∀ k → Fn k ⊆ Fn (suc k)
fn-⊆ k x (e , x≃fe) = suc e , x≃fe

-- Each finite ordinal is a subset of all higher finite ordinals.
fn-⊆⁺ : ∀ k l → Fn k ⊆ Fn (l + k)
fn-⊆⁺ k zero    = ⊆-refl (Fn k)
fn-⊆⁺ k (suc l) = ⊆-trans (Fn k) (Fn (l + k)) (Fn (suc l + k)) 
                          (fn-⊆⁺ k l) (fn-⊆ (l + k))

-- Each finite ordinal is a member of its successor ordinal.
fn-∈-fn : ∀ k → Fn k ∈ Fn (suc k)
fn-∈-fn k = zero , ≃-refl (Fn k)

lemma : ∀ k l → suc l + k ≡ l + suc k
lemma k 0                         = refl
lemma k (suc l) rewrite lemma k l = refl

-- Each finite ordinal is a member of all higher finite ordinals.
fn-∈-fn⁺ : ∀ k l → Fn k ∈ Fn (suc l + k)
fn-∈-fn⁺ k l rewrite lemma k l = fn-⊆⁺ (suc k) l (Fn k) (fn-∈-fn k)

-- The natural numbers
ω : V
ω = nat ◂ Fn

-- The natural numbers contain every finite ordinal.
fn-∈-ω : ∀ k → Fn k ∈ ω
fn-∈-ω k = k , ≃-refl (Fn k)

-- Every finite ordinal is a subset of the natural numbers.
fn-⊆-ω : ∀ k → Fn k ⊆ ω
fn-⊆-ω .(suc k) z (zero {k}  , z≃fe) = k , z≃fe
fn-⊆-ω .(suc k) z (suc {k} e , z≃fe) = fn-⊆-ω k z (e , z≃fe)

-- Singleton set
^ : V → V
^ x = fin 1 ◂ const x

-- Singleton sets are equal to the unordered pair of a set and itself.
single : ∀ x → ^ x ≃ ⟨ x , x ⟩
single x = (λ _ → zero , ≃-refl x) , back
 where
 back : ∀ e₂ → ∃ \e₁ → const x e₁ ≃ pair x x e₂
 back zero       = zero , ≃-refl x
 back (suc zero) = zero , ≃-refl x
 back (suc (suc ()))

-- Singleton sets respect equality.
≃-^ : ∀ x y → x ≃ y → ^ x ≃ ^ y
≃-^ x y x≃y = (λ _ → zero , x≃y) , (λ _ → zero , x≃y)

-- Ordered pairs
⟪_,_⟫ : V → V → V
⟪ x , y ⟫ = ⟨ ^ x , ⟨ x , y ⟩ ⟩

-- Ordered pairs respect equality
≃-⟪⟫ : ∀ x y z u → x ≃ z → y ≃ u → ⟪ x , y ⟫ ≃ ⟪ z , u ⟫
≃-⟪⟫ x y z u x≃z y≃u = ≃-⟨⟩ (^ x) (⟨ x , y ⟩) (^ z) (⟨ z , u ⟩)
                            (≃-^ x z x≃z) (≃-⟨⟩ x y z u x≃z y≃u)

-- Cartesian product
_⊗_ : V → V → V
(j ◂ f) ⊗ (k ◂ g) = σ j (const k) ◂ uncurry λ e₁ e₂ → ⟪ f e₁ , g e₂ ⟫

-- The Cartesian product contains as elements ordered pairs of elements
-- of its component sets.
⊗-∈ : ∀ x y z u → z ∈ x → u ∈ y → ⟪ z , u ⟫ ∈ (x ⊗ y)
⊗-∈ (j ◂ f) (k ◂ g) z u (e₁ , z≃fe₁) (e₂ , u≃ge₂)
  = (e₁ , e₂) , ≃-⟪⟫ z u (f e₁) (g e₂) z≃fe₁ u≃ge₂

-- Set comprehension
Comp : V → (V → P) → V
Comp (j ◂ f) pr = σ j (prf ∘ pr ∘ f) ◂ λ e → f (proj₁ e)

-- The set of all elements of another set that satisfies the false
-- predicate is empty.
∅-⊥ : ∀ x → Comp x (const ⊥) ≃ ∅
∅-⊥ (j ◂ f) = →∅ , λ ()
 where
 →∅ : ∀ (e₁ : Σ (T j) \_ → Fin 0) → ∃ \e₂ → f (proj₁ e₁) ≃ naughty e₂
 →∅ (_ , ())
