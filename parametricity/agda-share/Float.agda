
module Float where

open import Data.Empty
open import Data.Product hiding (map)
open import Data.List
open import Data.String

data Var (A : Set) : Set where
  top : Var A
  pop : A → Var A

map-var : ∀{A B} → (A → B) → Var A → Var B
map-var f top     = top
map-var f (pop v) = pop (f v)

data Expr (A : Set) : Set where
  var  : A → Expr A
  _$_  : Expr A → Expr A → Expr A
  let* : Expr A → Expr (Var A) → Expr A
  free : String → Expr A

map-expr : ∀{A B} → (A → B) → Expr A → Expr B
map-expr _ (free s)   = free s
map-expr f (var v)    = var (f v)
map-expr f (g $ x)    = map-expr f g $ map-expr f x
map-expr f (let* e b) = let* (map-expr f e) (map-expr (map-var f) b)

{-# NO_TERMINATION_CHECK #-}
float  : ∀{A} → List (Expr A) → Expr A → Expr A
pull-$ : ∀{A} → List (Expr A) → Expr A → Expr A → Expr A

float stk (f $ x)    = pull-$ stk f (float [] x)
float stk (let* e b) = let* (float [] e) (float (map (map-expr pop) stk) b)
float stk e          = foldl _$_ e stk

pull-$ stk f (let* e b) =
  let* (float [] e) (pull-$ (map (map-expr pop) stk) (map-expr pop f) b)
pull-$ stk f e          = float (e ∷ stk) f

test₁ : Expr ⊥
test₁ = let* (let* (free "a") (var top) $ free "b") (var top)
      $ let* (free "who") (var top)
