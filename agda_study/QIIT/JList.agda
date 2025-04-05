{-# OPTIONS --cubical #-}  -- 使用 Cubical Agda 来处理等式

module JList where

-- open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude

data JList (A : Set) : Set where
  [] : JList A
  [_] : A → JList A
  _++_ : JList A → JList A → JList A

  -- 等式规则
  idr : ∀ (ℓ : JList A) → ℓ ++ [] ≡ ℓ
  idl : ∀ (ℓ : JList A) → [] ++ ℓ ≡ ℓ
  assoc : ∀ (ℓ₁ ℓ₂ ℓ₃ : JList A) → (ℓ₁ ++ ℓ₂) ++ ℓ₃ ≡ ℓ₁ ++ (ℓ₂ ++ ℓ₃)

infixr 10 _++_

-- 示例用法
example : JList ℕ
example = [ 1 ] ++ [ 2 ] ++ [ 3 ]

-- 使用等式规则
example-idr : (example ++ []) ≡ example
example-idr = idr example

example-idl : ([] ++ example) ≡ example
example-idl = idl example

example-assoc : ((example ++ [ 4 ]) ++ [ 5 ]) ≡ (example ++ ([ 4 ] ++ [ 5 ]))
example-assoc = assoc example [ 4 ] [ 5 ]
