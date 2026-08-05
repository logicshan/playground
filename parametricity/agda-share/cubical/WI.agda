{-# OPTIONS --cubical --safe --postfix-projections #-}

module WI where

open import Cubical.Core.Everything renaming (I to 𝕀)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (I)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Prod hiding (_×_) renaming (_×Σ_ to _×_)
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit

variable
  ℓ : Level
  I O : Type ℓ

record Roman (I O : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor _▷_/_▷_
  field
    S : Type ℓ
    P : S → Type ℓ
    q : S → O
    r : (s : S) → P s → I

data W (S : Type ℓ) (P : S → Type ℓ) : Type ℓ where
  sup : (s : S) → (P s → W S P) → W S P

con : ∀{S P} → W {ℓ} S P → S
con (sup s _) = s

pos : ∀{S P} → (x : W {ℓ} S P) → P (con x) → W S P
pos (sup _ f) = f

⟦_⟧ : Roman {ℓ} I O → (I → Type ℓ) → O → Type ℓ
⟦ S ▷ P / q ▷ r ⟧ X o = Σ[ s ∈ S ] (o ≡ q s) × ((p : P s) → X (r s p))

module Simple (C : Roman {ℓ} I O) (B : I ≡ O) where
  open Roman C

  i→o : I → O
  i→o = transport B

  well-formed : W S P → I → Type ℓ
  well-formed (sup s f) i
    = (i→o i ≡ q s) × (∀(p : P s) → well-formed (f p) (r s p))

  WI : I → Type _
  WI i = Σ[ x ∈ W S P ] well-formed x i

  embed : ∀{i} → ⟦ C ⟧ WI (i→o i) → WI i
  embed (s , p , f) .fst = sup s (fst ∘ f)
  embed (s , p , f) .snd = p , snd ∘ f

  extract : ∀ i → WI i → ⟦ C ⟧ WI (i→o i)
  extract _ (sup s f , wf) .fst = s
  extract _ (sup s f , wf) .snd .fst = fst wf
  extract _ (sup s f , wf) .snd .snd p = f p , snd wf p

  Pointwise : ∀ i → WI i ≡ ⟦ C ⟧ WI (i→o i)
  Pointwise i
    = isoToPath (iso (extract i) embed (λ _ → refl) (λ where (sup _ _ , _) → refl))

  Lambek : PathP (λ j → B j → Type _) WI (⟦ C ⟧ WI)
  Lambek j o
    = hcomp (λ k → λ where
          (j = i0) → Pointwise o (~ k)
          (j = i1) → ⟦ C ⟧ WI o)
        (⟦ C ⟧ WI (transp (λ k → B (j ∨ k)) j o))

module DependentList (T : ℕ → Type₀) where
  open Roman

  data Tag : Type₀ where
    t-nil t-cons : Tag

  DL : Roman ℕ ℕ
  DL .S = Σ[ n ∈ ℕ ] Σ Tag λ{ t-nil → Unit ; t-cons → T n }
  DL .P (n , t-nil , _) = ⊥
  DL .P (n , t-cons , _) = Unit
  DL .q (n , t , _) = n
  DL .r (n , t-cons , _) _ = suc n

  open Simple DL refl renaming (WI to DepList)

  trefl : ∀ n → transport (λ _ → ℕ) n ≡ n
  trefl n i = transp (λ _ → ℕ) i n

  private
    pre-nil : ℕ → W (DL .S) (DL .P)
    pre-nil n = sup (n , t-nil , _) ⊥-elim

    pre-nil-wf : (n : ℕ) → well-formed (pre-nil n) n
    pre-nil-wf n .fst = trefl n
 
  nil : ∀{n} → DepList n
  nil {n} = pre-nil n , pre-nil-wf n

  private
    pre-cons : (n : ℕ) → T n → W (DL .S) (DL .P) → W (DL .S) (DL .P)
    pre-cons n x xs = sup (n , t-cons , x) λ _ → xs

    pre-cons-wf
      : (n : ℕ)
      → (x : T n) (xs : W (DL .S) (DL .P))
      → well-formed xs (suc n)
      → well-formed (pre-cons n x xs) n
    pre-cons-wf n x xs wfxs .fst = trefl n
    pre-cons-wf n x xs wfxs .snd _ = wfxs

  cons : ∀{n} → T n → DepList (suc n) → DepList n
  cons {n} x xs = pre-cons n x (xs .fst) , pre-cons-wf n x (xs .fst) (xs .snd)

  prop-wf : ∀ n dl → isProp (well-formed dl n)
  prop-wf n (sup t f) (p , r) (q , s) j
    = isSetℕ _ _ p q j , propPi (λ y → prop-wf _ (f y)) r s j
  
  private
    ⊥-universal : ∀{A : Type ℓ} → (f g : ⊥ → A) → f ≡ g
    ⊥-universal f g i ()

  induct
    : (R : ∀ n → DepList n → Type ℓ)
    → (∀ n → R n nil)
    → (∀ n x xs → R (suc n) xs → R n (cons x xs))
    → ∀ n (dl : DepList n) → R n dl
  induct R pn pc n dl@(sup (m , t-nil , u) f , tn≡m , p) = subst (R n) isNil (pn n)
    where
    n≡m : n ≡ m
    n≡m j = hcomp (λ k → λ{ (j = i0) → trefl n (~ k) ; (j = i1) → m}) (tn≡m j)

    isPreNil : pre-nil n ≡ sup (m , t-nil , u) f
    isPreNil j = sup (n≡m j , t-nil , _) (⊥-universal ⊥-elim f j)

    isNil : nil ≡ dl
    isNil j .fst = isPreNil j
    isNil j .snd = isProp→PathP (prop-wf n) isPreNil (pre-nil-wf n) (tn≡m , p) j

  induct R pn pc n dl@(sup (m , t-cons , x) f , tn≡m , p)
    = transp (λ j → R (n≡m (~ j)) (isCons j)) i0
        (pc m x xs (induct R pn pc (suc m) (f _ , p _)))
    where
    n≡m : n ≡ m
    n≡m j = hcomp (λ k → λ{ (j = i0) → trefl n (~ k) ; (j = i1) → m}) (tn≡m j)

    xs : DepList (suc m)
    xs = f _ , p _

    isCons : PathP (λ j → DepList (n≡m (~ j))) (cons x xs) dl
    isCons j .fst = sup (m , t-cons , x) f
    isCons j .snd .fst j' = isSet→isSet' isSetℕ (λ _ → m) tn≡m (sym n≡m) refl j j'
    isCons j .snd .snd = p
