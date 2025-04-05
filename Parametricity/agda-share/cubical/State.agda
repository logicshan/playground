
module State where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

variable
  ℓ : Level
  A B S : Type ℓ
  C : A -> B -> Type ℓ

Δ : ((s t : S) -> C s t) -> (s : S) -> C s s
Δ f s = f s s

-- Inductive definition of the algebraic theory of state.
-- We quotient by various rules for sensible behavior of
-- the implicit state.
data STI (S A : Type) : Type where
  ret : A -> STI S A
  put : S -> STI S A -> STI S A
  get : (S -> STI S A) -> STI S A
  -- two puts in a row are the same as a single put
  pp : ∀ s t n → put s (put t n) ≡ put t n
  -- put then get gets back the put value
  pg : ∀ s f → put s (get f) ≡ put s (f s)
  -- getting then putting is a no-op
  gp : ∀ n → get (flip put n) ≡ n
  -- getting twice in a row gets the same value
  gg : ∀ f → get (get ∘ f) ≡ get (Δ f)
  -- getting and ignoring the value is a no-op
  gk : ∀ n → get (const n) ≡ n
  squash : isSet (STI S A)

elim
  : (R : STI S A -> Type ℓ)
  → isOfHLevelDep 2 R
  → (Rr : ∀ x → R (ret x))
  → (Rp : ∀ s {n} → R n -> R (put s n))
  → (Rg : ∀{f} → (∀ s → R (f s)) -> R (get f))
  → (Rpp : ∀ s t {n} Rn → PathP (λ i → R (pp s t n i)) (Rp s (Rp t Rn)) (Rp t Rn))
  → (Rpg : ∀ s {f} Rf → PathP (λ i → R (pg s f i)) (Rp s (Rg Rf)) (Rp s (Rf s)))
  → (Rgp : ∀{n} Rn → PathP (λ i → R (gp n i)) (Rg λ s → Rp s Rn) Rn)
  → (Rgg : ∀{f} Rf → PathP (λ i → R (gg f i)) (Rg (Rg ∘ Rf)) (Rg (Δ Rf)))
  → (Rgk : ∀{n} Rn → PathP (λ i → R (gk n i)) (Rg (const Rn)) Rn)
  → ∀ n → R n
elim R Rs Rr Rp Rg Rpp Rpg Rgp Rgg Rgk = go where
  go : _
  go (ret x) = Rr x
  go (put s n) = Rp s (go n)
  go (get f) = Rg (go ∘ f)
  go (pp s t n i) = Rpp s t (go n) i
  go (pg s f i) = Rpg s (go ∘ f) i
  go (gp n i) = Rgp (go n) i
  go (gg f i) = Rgg (λ s t → go (f s t)) i
  go (gk n i) = Rgk (go n) i
  go (squash m n p q i j) =
    Rs (go m) (go n) (cong go p) (cong go q) (squash m n p q) i j

elim→Prop
  : (P : STI S A -> Type ℓ)
  → isPropDep P
  → (∀ x → P (ret x))
  → (∀ s {n} → P n -> P (put s n))
  → (∀{f} → (∀ s → P (f s)) -> P (get f))
  → ∀ n → P n
elim→Prop P Pp r p g =
  elim (λ s → P s) (isPropDep→isSetDep Pp)
    r p g
    (λ s t Pn → Pp (p s (p t Pn)) (p t Pn) (pp s t _))
    (λ s Pf → Pp (p s (g _)) (p s (Pf s)) (pg s _))
    (λ Pn → Pp (g λ s → p s Pn) Pn (gp _))
    (λ Pf → Pp (g (g ∘ Pf)) (g (Δ Pf)) (gg _))
    (λ Pn → Pp (g λ _ → Pn) Pn (gk _))

ST : Type -> Type -> Type
ST S A = S -> S × A

module _ {S A} (Ss : isSet S) (As : isSet A) where
  to-I : ST S A -> STI S A
  to-I f = get (λ s → let (t , x) = f s in put t (ret x))

  from-I : STI S A -> ST S A
  from-I (ret x) s = s , x
  from-I (put t n) s = from-I n t
  from-I (get f) s = from-I (f s) s
  from-I (pp t u x i) s = from-I x u
  from-I (pg t f i) s = from-I (f t) t
  from-I (gp n i) s = from-I n s
  from-I (gg f i) s = from-I (f s s) s
  from-I (gk n i) s = from-I n s
  from-I (squash m n p q i j) =
    isSet→ (isSet× Ss As)
      (from-I m) (from-I n)
      (cong from-I p) (cong from-I q)
      i j

  to-from : ∀(m : STI S A) → to-I (from-I m) ≡ m
  to-from =
    elim→Prop (λ m → to-I (from-I m) ≡ m)
      (isOfHLevel→isOfHLevelDep 1 (λ m → squash (to-I (from-I m)) m))
      (gp ∘ ret) ep eg
    where
    eg : ∀{f} → ((s : S) → to-I (from-I (f s)) ≡ f s)
              → to-I (λ s → from-I (f s) s) ≡ get f
    eg {f} sub =
      get (λ s → g s s)           ≡⟨ sym (gg g) ⟩
      get (λ s → get λ t → g s t) ≡⟨ cong get (funExt sub) ⟩
      get f ∎
      where
      g : S -> S -> _
      g s t = let (u , x) = from-I (f s) t in put u (ret x)

    ep : ∀ s {n} → to-I (from-I n) ≡ n -> to-I (λ _ → from-I n s) ≡ put s n
    ep s {n} sub =
      get (λ _ → nn s) ≡⟨ gk (nn s) ⟩
      nn s ≡⟨ sym (pp s (fst p) (ret (snd p))) ⟩
      put s (nn s) ≡⟨ sym (pg s nn)  ⟩
      put s (get nn) ≡⟨ cong (put s) sub ⟩
      put s n ∎
      where
      p = from-I n s
      nn : S -> _
      nn s = let (u , x) = from-I n s in put u (ret x)

  from-to : ∀(m : ST S A) -> from-I (to-I m) ≡ m
  from-to m = funExt (λ s → refl)

  same : STI S A ≡ ST S A
  same = isoToPath (iso from-I to-I from-to to-from)
