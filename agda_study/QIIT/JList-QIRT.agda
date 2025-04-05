{-# OPTIONS --cubical #-}

module JList-QIRT where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_]) renaming (_++_ to _⧺_)
open import Cubical.Data.Nat

-- 定义 JList 和 flatten 函数
data JList (A : Set) : Set
flatten : {A : Set} → JList A → List A

data JList A where
  [] : JList A
  [_] : A → JList A
  _++_ : JList A → JList A → JList A  -- 现在可以使用 _++_
  nf : ∀ (ℓ ℓ' : JList A) → flatten ℓ ≡ flatten ℓ' → ℓ ≡ ℓ'

infixr 10 _++_

-- 定义 flatten 函数
flatten [] = []
flatten [ x ] = x ∷ []
flatten (ℓ ++ ℓ') = flatten ℓ ⧺ flatten ℓ'
flatten (nf ℓ ℓ' p i) = p i

-- 示例用法
example : JList ℕ
example = [ 1 ] ++ [ 2 ] ++ [ 3 ]

-- 使用 nf 构造函数
example-nf : (example ++ []) ≡ example
example-nf = nf (example ++ []) example refl

-- 验证 flatten 函数
example-flatten : flatten example ≡ 1 ∷ 2 ∷ 3 ∷ []
example-flatten = refl
