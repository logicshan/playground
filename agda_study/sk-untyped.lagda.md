The simplest programming language: 

Combinatory logic as an alternative to Turing machines

We define weak combinatory logic and show that the looping combinator Ω doesn't terminate.
```
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import iff


```

Definition of the terms
```
infixl 20 _$_

data SK : Set where
  S K : SK
  _$_ : SK → SK → SK

variable t t' u u'  : SK

```
Values and the reduction relations
```
data Val : Set where
  K₀ : Val
  K₁ : SK → Val
  S₀ : Val
  S₁ : SK → Val 
  S₂ : SK → SK → Val

variable v v' w w' : Val

⌈_⌉ : Val → SK
⌈ K₀ ⌉ = K
⌈ K₁ t ⌉ = K $ t
⌈ S₀ ⌉ = S
⌈ S₁ t ⌉ = S $ t
⌈ S₂ t u ⌉ = S $ t $ u

infix 5 _↓_ _$$_↓_

data _$$_↓_ : Val → SK → Val → Set

data _↓_ : SK → Val → Set where
  K₀ : K ↓ K₀
  S₀ : S ↓ S₀
  app : t ↓ v → v $$ u ↓ w → t $ u ↓ w
  
data _$$_↓_ where
  K₁ : K₀ $$ t ↓ (K₁ t)
  K₂ : t ↓ v → (K₁ t) $$ u ↓ v
  S₁ : S₀ $$ t ↓ (S₁ t)
  S₂ : S₁ t $$ u ↓ (S₂ t u)  
  S₃ : (t $ u) $ (t' $ u) ↓ v → (S₂ t t') $$ u ↓ v
```
Alternatively we could define values as a predicate on terms induced by the
reduction relation but we prefer the direct syntacti definition.

Next we show that evaluation is deterministic:
```
det-↓ : t ↓ v → t ↓ v' → v ≡ v'
det-↓$ : w $$ u ↓ v → w $$ u ↓ v' → v ≡ v' 

det-↓ K₀ K₀ = refl
det-↓ S₀ S₀ = refl
det-↓ (app p r) (app q s) rewrite (det-↓ p q) = det-↓$ r s

det-↓$ K₁ K₁ = refl
det-↓$ (K₂ p) (K₂ q) = det-↓ p q
det-↓$ S₁ S₁ = refl
det-↓$ S₂ S₂ = refl
det-↓$ (S₃ p) (S₃ q) = det-↓ p q
```
We can define a partial evaluator for terms:
(Note that we mark partial functions with !)
```
{-# TERMINATING #-}
!norm : (t : SK) → Σ[ v ∈ Val ] t ↓ v
!norm-^ : (v : Val)(u : SK) → Σ[ w ∈ Val ] v $$ u ↓ w

!norm S = S₀ , S₀
!norm K = K₀ , K₀
!norm (t $ u) with !norm t
... | v , r with !norm-^ v u
... | w , s = w , (app r s)

!norm-^ K₀ u = (K₁ u) , K₁
!norm-^ (K₁ t) u with !norm t
... | v , r = v , (K₂ r)
!norm-^ S₀ u = (S₁ u) , S₁
!norm-^ (S₁ t) u = S₂ t u , S₂
!norm-^ (S₂ t t') u with !norm  ((t $ u) $ (t' $ u))
... | (v , r) = v , (S₃ r)
```
As an example we define `I` (λ x → x) and `ω` (λ x → x x):
```
I : SK
I = S $ K $ K

ω : SK
ω = S $ I $ I

I-nf : Val
I-nf = S₂ K K

I-r : I ↓ I-nf
I-r = app (app S₀ S₁) S₂

ω-nf : Val
ω-nf = S₂ I I

ω-r :  ω ↓ ω-nf
ω-r = app (app S₀ S₁) S₂

```
Examples `!norm (I $ K)` and `!norm (ω $ I)`.

We define the information ordering and equivalence.
```
infix 5 _⊑_ _~_

_⊑_ : SK → SK → Set
t ⊑ u = ∀ {v} → (t ↓ v) → (u ↓ v)

refl-⊑ : t ⊑ t
refl-⊑ x = x

trans-⊑ : t ⊑ u → u ⊑ u' → t ⊑ u'
trans-⊑ f g x = g (f x)

_~_ : SK → SK → Set
t ~ u = t ⊑ u × u ⊑ t

~-setoid : Setoid _ _
~-setoid = record { Carrier = SK ; _≈_ = _~_ ;
                    isEquivalence = record {
                      refl = refl-⊑ , refl-⊑ ;
                      sym = λ (p , p') → p' , p ;
                      trans = λ (p , p') (q , q')
                                   → (trans-⊑ p q) , (trans-⊑ q' p') } }
```
We can show that a number of useful equations hold:

```
open import Relation.Binary.Reasoning.Setoid ~-setoid

K-prop : K $ t $ u ~ t
proj₁ K-prop (app (app K₀ K₁) (K₂ h)) = h
proj₂ K-prop h = app (app K₀ K₁) (K₂ h)


S-prop : S $ t $ u $ u' ~ t $ u' $ (u $ u')
proj₁ S-prop (app (app (app S₀ S₁) S₂) (S₃ h)) = h
proj₂ S-prop h = app (app (app S₀ S₁) S₂) (S₃ h)

$-lem : t ⊑ t' → t $ u ⊑ t' $ u
$-lem h (app g r) = app (h g) r

$-prop : t ~ t' → t $ u ~ t' $ u
$-prop (p , p') = ($-lem p) , ($-lem p')

I-prop : I $ t ~ t
I-prop {t} = begin I $ t
       ≈⟨ Setoid.refl ~-setoid ⟩ S $ K $ K $ t
       ≈⟨ S-prop ⟩ K $ t $ (K $ t)      
       ≈⟨ K-prop ⟩ t  ∎

ω-prop : ω $ t ~ t $ (I $ t)
ω-prop {t} =  begin ω $ t
       ≈⟨ Setoid.refl ~-setoid ⟩  (S $ I $ I) $ t
       ≈⟨ S-prop ⟩ (I $ t) $ (I $ t)
       ≈⟨ $-prop I-prop ⟩  t $ (I $ t)  ∎
```

We define `Ω` and show that it isn't terminating. This is harder than
expected because `Ω` doesn't reduce to itself but it only loops.

```
Ω : SK
Ω = ω $ ω

thm : Ω ↓ w' → ⊥
thm (app r x) rewrite det-↓ r ω-r = loop ω-r x
  where loop : t ↓ ω-nf → ω-nf $$ t ↓ v → ⊥
        loop r (S₃ (app x x₁)) with det-↓ (proj₁ I-prop x) r
        ... | refl = loop (proj₂ I-prop r) x₁

```
