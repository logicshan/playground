open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- 定义 if_then_else_ 函数
if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

-- 定义一个依赖类型的函数
dependentIf : (b : Bool) → if b then Nat else Bool → Set
dependentIf true  x = x ≡ 42  -- 如果 b 为 true，x 是 Nat，检查是否等于 42
dependentIf false x = x ≡ true  -- 如果 b 为 false，x 是 Bool，检查是否等于 true


/home/sn/playground/augustss/test7.agda:11.28-46: error: [UnequalSorts]
Set₁ != Set
when checking that the solution Set of metavariable _A_6 has the
expected type Set
