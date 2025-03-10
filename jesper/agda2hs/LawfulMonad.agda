{-# OPTIONS --erasure #-}

open import Haskell.Prelude

record LawfulMonad (m : Set → Set)
                   ⦃ iMonad : Monad m ⦄ : Set₁ where
  field
    left-id : ∀ {a b} (x : a) (f : a → m b)
            → (return x >>= f) ≡ f x
    right-id : ∀ {a} (k : m a)
             → (k >>= return) ≡ k
    assoc : ∀ {a b c} (k : m a)
          → (f : a → m b) (g : b → m c)
          → ((k >>= f) >>= g) ≡ (k >>= (λ x → f x >>= g))
open LawfulMonad

instance
  _ : LawfulMonad Maybe
  _ = λ where
    .left-id  x        f   → refl
    .right-id Nothing      → refl
    .right-id (Just x)     → refl
    .assoc    Nothing  f g → refl
    .assoc    (Just x) f g → refl

instance
  _ : {r : Set} → LawfulMonad (λ a → (r → a))
  _ = λ where
    .left-id   x f   → refl
    .right-id  k     → refl
    .assoc     k f g → refl
