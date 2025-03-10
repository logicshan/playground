{-# OPTIONS --sized-types --erasure #-}

open import Agda.Primitive
open import Haskell.Prelude
open import Haskell.Prim.Thunk

data Stream (a : Set) (@0 i : Size) : Set where
  _:>_ : a → Thunk (Stream a) i → Stream a i
{-# COMPILE AGDA2HS Stream #-}

variable
  i : Size
  ℓ : Level

headS : Stream a ∞ → a
headS (x :> _) = x
{-# COMPILE AGDA2HS headS #-}

tailS : Stream a ∞ → Stream a ∞
tailS (_ :> xs) = xs .force
{-# COMPILE AGDA2HS tailS #-}

repeat : a → Stream a i
repeat x = x :> λ where .force → repeat x
{-# COMPILE AGDA2HS repeat #-}

mapS  : (a → b) → Stream a i → Stream b i
mapS  f (x :> xs) =
  (f x) :> λ where .force → mapS f (xs .force)
{-# COMPILE AGDA2HS mapS #-}

nats : Stream Int i
nats = 0 :> λ where .force → mapS (λ x → 1 + x) nats
{-# COMPILE AGDA2HS nats #-}

open import Agda.Primitive.Cubical using (PathP)

_=P_ : {a : Set ℓ} → (x y : a) → Set ℓ
_=P_ {a = a} = PathP (λ _ → a)

mapS-fusion  : (f : a → b) (g : b → c) (s : Stream a i)
             →  mapS {i = i} g (mapS {i = i} f s)
             =P mapS {i = i} (λ x → g (f x)) s
mapS-fusion  f g (hd :> tl) i =
  (g (f hd)) :> λ where .force → mapS-fusion f g (tl .force) i
