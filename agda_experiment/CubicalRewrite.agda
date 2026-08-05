{-# OPTIONS --cubical --guardedness #-}

module CubicalRewrite where

open import Cubical.Data.Nat
open import Cubical.Data.Equality

+zero : ∀ n → n + 0 ≡ n
+zero zero    = refl
+zero (suc n) = ap suc (+zero n)

example : ∀ n → n + 0 ≡ n
example n rewrite +zero n = refl

-- 3. 定义长度受 Nat 约束的依赖向量 Vec
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- 4. 使用 rewrite 特性
-- 函数目标：将 Vec A (n + 0) 转化为 Vec A n
-- 如果不使用 rewrite，xs 的类型是 Vec A (n + 0)，无法直接作为 Vec A n 返回
castVec : {A : Set} (n : ℕ) → Vec A (n + 0) → Vec A n
--castVec n xs rewrite +zero n = xs
castVec n xs rewrite +zero n = xs
