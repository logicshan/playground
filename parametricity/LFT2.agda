module LFT2 where

-- 现代 Agda 推荐直接使用内置的 Primitive 模块处理 Level
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

Π : {l m : Level} (A : Set l) (B : A → Set m) → Set (l ⊔ m)
Π A B = (a : A) → B a

-- 旧版的 suc 替换为 lsuc，∀ l 显式标注类型以增强可读性
[Set_] : (l : Level) → Set l → Set l → Set (lsuc l)
[Set l ] A1 A2 = A1 → A2 → Set l

-- 现代 Agda 使用 lzero 和 lsuc
[Set₂] = [Set lsuc (lsuc lzero) ]

-- 旧代码的 Set1 和 Set2 改为 Unicode 的 Set₁ 和 Set₂
[Set₁] : [Set₂] Set₁ Set₁
[Set₁] = [Set lsuc lzero ]

[Set] : [Set₁] Set Set
[Set] = [Set lzero ]

-- 统一使用标准的 Unicode 箭头 `→` 代替 `->`
[Π] : {l m : Level} {A1 A2 : Set l} {B1 : A1 → Set m} {B2 : A2 → Set m} →
            ([A] : [Set l ] A1 A2) →
            ([B] : ∀ {a1 a2} →
            (aR : [A] a1 a2) →
            [Set m ] (B1 a1) (B2 a2) ) →
            [Set (l ⊔ m) ] (Π A1 B1) (Π A2 B2)
([Π] [A] [B]) f1 f2 = ∀ {a1 a2} → (aR : [A] a1 a2) → [B] {a1} {a2} aR (f1 a1) (f2 a2)

_[→]_ : {l m : Level} {A1 A2 : Set l} {B1 B2 : Set m} →
            ([A] : [Set l ] A1 A2) →
            ([B] : [Set m ] B1 B2) →
            [Set (l ⊔ m) ] (A1 → B1) (A2 → B2)
[A] [→] [B] = [Π] [A] (λ _ → [B])

-- 保留兼容旧代码的 [->] 别名
_[->]_ : {l m : Level} {A1 A2 : Set l} {B1 B2 : Set m} →
            ([A] : [Set l ] A1 A2) →
            ([B] : [Set m ] B1 B2) →
            [Set (l ⊔ m) ] (A1 → B1) (A2 → B2)
_[->]_ = _[→]_

infixr 0 _[->]_ _[→]_


module Examples where

  data Bool : Set where
    true  : Bool
    false : Bool

  data [Bool] : [Set] Bool Bool where
    [true]  : [Bool] true true
    [false] : [Bool] false false

  -- Note that [Bool] is just the identity relation.

  data List (A : Set) : Set where
    nil  : List A
    cons : A → List A → List A

  data [List] {A1 A2 : Set} ([A] : [Set] A1 A2) : [Set] (List A1) (List A2) where
    [nil]  : [List] [A] nil nil
    [cons] : ([A]  [→]  [List] [A]  [→]  [List] [A]) cons cons
  -- [List] [A] xs1 xs2 means that elements of xs1 are related to
  -- elements of xs2, index-wise.

  -- Set1 变更为 Set₁
  Filter : Set₁
  --         (A : Set)      →  (A   →   Bool)    →    List  A    →    List  A
  Filter   =  Π   Set   λ A  →  (A   →   Bool)    →    List  A    →    List  A

  [Filter] : [Set₁] Filter Filter
  [Filter] = [Π] [Set]  λ [A] →  ([A] [→] [Bool])  [→]  [List] [A]  [→]  [List] [A]

  Free-Theorem-Filter = (f : Filter) → [Filter] f f

  -- Set2 和 Set1 变更为 Unicode 的 Set₂ 和 Set₁
  data _==_ {A : Set₂} (a : A) : (b : A) → Set₁ where
    refl : a == a

  check : (∀ f → [Filter] f f) == (
      -- for any function of the Filter type,
    (f : Filter)
      -- for any relation A1 ↔ A2,
    {A1 : Set} {A2 : Set} ([A] : A1 → A2 → Set)
      -- if p1, p2 take related values to equal booleans
    {p1 : A1 → Bool} {p2 : A2 → Bool} →
      (pR : ∀ {a1 a2} → [A] a1 a2 → [Bool] (p1 a1) (p2 a2))
      -- if xs1, xs2 are related by [A] indexwise,
    {xs1 : List A1} {xs2 : List A2} (xsR : [List] [A] xs1 xs2) →
      -- then the results are related by [A] indexwise
    [List] [A] (f A1 p1 xs1) (f A2 p2 xs2) )
  check = refl

  -- 原代码的 Set0 并不是标准 Agda，直接替换为 Set 即可
  If = (A : Set) → Bool → A → A → A

  at_if_then_else_ : If
  at A if true  then a else b = a
  at A if false then a else b = b

  [If] : [Set₁] If If
  [If] = [Π] [Set] (λ A → [Bool] [→] A [→] A [→] A)

  [at_if_then_else_] : [If] at_if_then_else_ at_if_then_else_
  [at A if [true]  then a else b ] = a
  [at A if [false] then a else b ] = b

  filter : Filter
  filter A p nil = nil
  filter A p (cons x xs) = at List A 
                           if p x then cons x (filter A p xs) else filter A p xs

  [filter] : [Filter] filter filter
  [filter] A p [nil] = [nil]
  [filter] A p ([cons] x xs) = [at [List] A
                               if p x then [cons] x ([filter] A p xs) else [filter] A p xs ]

  postulate free-theorem-Filter : Free-Theorem-Filter
