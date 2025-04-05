module HereditarySubstitution where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import Agda.Builtin.Equality

-- 使用 de Bruijn 索引表示变量，避免命名问题
data Term : Set where
  Var : ℕ → Term           -- 变量，用自然数表示索引
  App : Term → Term → Term -- 应用
  Lam : Term → Term        -- λ 抽象（绑定一个变量）

-- 示例：(λx. x 0) 1，使用 de Bruijn 索引
-- 表示为：Lam (App (Var 0) (Var 1)) 表示 λx. x 0
-- 替换 Var 1 表示外部变量
example : Term
example = App (Lam (App (Var 0) (Var 1))) (Var 0)

-- 判断一个项是否是归一化的（没有未规约的 β-红项）
data IsNormal : Term → Set where
  N-Var : ∀ {n} → IsNormal (Var n)
  N-App : ∀ {t1 t2} → IsNormal t1 → IsNormal t2 → 
          (∀ {u} → t1 ≢ Lam u) → IsNormal (App t1 t2)
  N-Lam : ∀ {t} → IsNormal t → IsNormal (Lam t)

-- 提升索引（用于在 λ 下调整变量）
shift : ℕ → Term → Term
shift k (Var n) with n < k
... | true  = Var n
... | false = Var (suc n)
shift k (App t1 t2) = App (shift k t1) (shift k t2)
shift k (Lam t) = Lam (shift (suc k) t)

-- 普通替换（不保证归一化）
subst : ℕ → Term → Term → Term
subst n s (Var m) with n ≟ m
... | yes _ = s
... | no  _ = Var m
subst n s (App t1 t2) = App (subst n s t1) (subst n s t2)
subst n s (Lam t) = Lam (subst (suc n) (shift 0 s) t)

-- 归一化函数，结合遗传替换
mutual
  normalize : Term → Term
  normalize (Var n) = Var n
  normalize (App (Lam t1) t2) = hsubst 0 t2 t1
  normalize (App t1 t2) = App (normalize t1) (normalize t2)
  normalize (Lam t) = Lam (normalize t)

  -- 遗传替换：确保替换后结果归一化
  hsubst : ℕ → Term → Term → Term
  hsubst n s t with subst n s t
  ... | Var m     = Var m
  ... | App t1 t2 = App (normalize t1) (normalize t2)
  ... | Lam t'    = Lam (normalize t')

-- 示例的归一化
result : Term
result = normalize example

-- 验证结果是 App (Var 0) (Var 0)
_ : result ≡ App (Var 0) (Var 0)
_ = refl
