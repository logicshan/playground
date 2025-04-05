
module ZigZag where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infix 90 ∞_
infix 90 ♯_
codata ∞_ (A : Set) : Set where
  ♯_ : A → ∞ A

♭ : ∀{A} → ∞ A → A
♭ (♯ x) = x

infix 30 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infixr 50 _,_
data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (x : A) (w : P x) → Σ A P

infixr 40 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 50 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 60 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : (x : A) → (xs : List A) → List A

infix 30 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  now   : ∀{xs}            → x ∈ x :: xs
  later : ∀{y ys} → x ∈ ys → x ∈ y :: ys

data Colist (A : Set) : Set where
  []   : Colist A
  _::_ : (x : A) → (xs : ∞ Colist A) → Colist A

infix 30 _∈-∞_
data _∈-∞_ {A : Set} (x : A) : Colist A → Set where
  now   : ∀{xs}                → x ∈-∞ x :: xs
  later : ∀{y ys} → x ∈-∞ ♭ ys → x ∈-∞ y :: ys

Colist⁺ : Set → Set
Colist⁺ A = A × Colist A

forget : ∀{A} → Colist⁺ A → Colist A
forget (x , xs) = x :: ♯ xs

infix 30 _∈⁺_
_∈⁺_ : ∀{A} → A → Colist⁺ A → Set
x ∈⁺ (y , ys) = (x ≡ y) ⊎ (x ∈-∞ ys)

square : Colist (Colist⁺ ℕ)
square = unfold₁ 1
 where
 unfold₂ : ℕ → Colist ℕ
 unfold₂ n = n :: ♯ unfold₂ (suc n)

 unfold₁ : ℕ → Colist (Colist⁺ ℕ)
 unfold₁ n = (n , unfold₂ (suc n)) :: ♯ unfold₁ (suc n)

take : ∀{A} → ℕ → Colist A → List A
take zero    _         = []
take (suc n) []        = []
take (suc n) (x :: xs) = x :: take n (♭ xs)

zig-zag-aux₀ : ∀{A} → List (Colist A) → List (Colist A) → Colist A
zig-zag-aux₀ ([] :: ls)        ls'               = zig-zag-aux₀ ls ls'
zig-zag-aux₀ ((x :: xs) :: ls) ls'
    = x :: (♯ zig-zag-aux₀ ls (♭ xs :: ls'))
zig-zag-aux₀ []                []                = []
zig-zag-aux₀ []                ([] :: ls)        = zig-zag-aux₀ [] ls
zig-zag-aux₀ []                ((x :: xs) :: ls)
    = x :: (♯ zig-zag-aux₀ ls (♭ xs :: []))

zig-zag-aux₁ : ∀{A} → List (Colist A) → List (Colist A) → Colist (Colist⁺ A)
             → Colist A
zig-zag-aux₁ ([] :: ls)        ls' cl = zig-zag-aux₁ ls ls' cl
zig-zag-aux₁ ((x :: xs) :: ls) ls' cl
    = x :: ♯ zig-zag-aux₁ ls (♭ xs :: ls') cl
zig-zag-aux₁ []                ls' [] = zig-zag-aux₀ ls' []
zig-zag-aux₁ []                ls' ((x , xs) :: cs)
    = x :: (♯ zig-zag-aux₁ (xs :: ls') [] (♭ cs))

zig-zag : ∀{A} → Colist (Colist⁺ A) → Colist A
zig-zag cl = zig-zag-aux₁ [] [] cl

mutual
  ∈-zz₀₀ : ∀{A} (x : A) (xs : Colist A) (xss ls : List (Colist A))
         → x ∈-∞ xs → xs ∈ xss → x ∈-∞ zig-zag-aux₀ xss ls
  ∈-zz₀₀ x .(x :: _) (.(x :: _)  :: _)   _  now          now = now
  ∈-zz₀₀ x (y :: ys) (.(y :: ys) :: xss) ls (later x∈ys) now
    = later (∈-zz₀₁ x (♭ ys) (♭ ys :: ls) xss x∈ys now)
  ∈-zz₀₀ x xs .((y :: ys) :: yss) ls x∈xs (later {y :: ys}{yss} xs∈yss)
    = later (∈-zz₀₀ x xs yss (♭ ys :: ls) x∈xs xs∈yss)
  ∈-zz₀₀ x xs .([]        :: yss) ls x∈xs (later {[]}     {yss} xs∈yss)
    = ∈-zz₀₀ x xs yss ls x∈xs xs∈yss

  ∈-zz₀₁ : ∀{A} (x : A) (xs : Colist A) (xss ls : List (Colist A))
         → x ∈-∞ xs → xs ∈ xss → x ∈-∞ zig-zag-aux₀ ls xss
  ∈-zz₀₁ x .(x :: _)  .((x :: _) :: _)    [] now                   now = now
  ∈-zz₀₁ x .(y :: ys) .((y :: ys) :: xss) [] (later {y} {ys} x∈ys) (now {xss})
    = later (∈-zz₀₁ x (♭ ys) (♭ ys :: []) xss x∈ys now)
  ∈-zz₀₁ x xs .([] :: yss) [] x∈xs (later {[]} {yss} xs∈yss)
    = ∈-zz₀₁ x xs yss [] x∈xs xs∈yss
  ∈-zz₀₁ x xs .((y :: ys) :: yss) [] x∈xs (later {y :: ys} {yss} xs∈yss)
    = later (∈-zz₀₀ x xs yss (♭ ys :: []) x∈xs xs∈yss)
  ∈-zz₀₁ x xs xss ([]        :: yss) x∈xs xs∈xss
    = ∈-zz₀₁ x xs xss yss x∈xs xs∈xss
  ∈-zz₀₁ x xs xss ((y :: ys) :: yss) x∈xs xs∈xss
    = later (∈-zz₀₁ x xs (♭ ys :: xss) yss x∈xs (later xs∈xss))

mutual
  ∈-zz₁₀ : ∀{A} (x : A) (xs : Colist⁺ A)
                (ls rs : List (Colist A)) (cl : Colist (Colist⁺ A))
         → x ∈⁺ xs → xs ∈-∞ cl → x ∈-∞ zig-zag-aux₁ ls rs cl
  ∈-zz₁₀ x (.x , _) [] rs (.(x , _)  :: xss) (inj₁ refl) now = now
  ∈-zz₁₀ x (y , ys) [] rs (.(y , ys) :: xss) (inj₂ x∈ys) now
    = later (∈-zz₁₁ x ys (ys :: rs) [] (♭ xss) x∈ys now)
  ∈-zz₁₀ x xs [] rs .((y , ys) :: yss) x∈xs (later {y , ys} {yss} xs∈yss)
    = later (∈-zz₁₀ x xs (ys :: rs) [] (♭ yss) x∈xs xs∈yss)
  ∈-zz₁₀ x xs ([] :: yss) rs cl x∈xs xs∈cl = ∈-zz₁₀ x xs yss rs cl x∈xs xs∈cl
  ∈-zz₁₀ x xs ((y :: ys) :: yss) rs cl x∈xs xs∈cl
    = later (∈-zz₁₀ x xs yss (♭ ys :: rs) cl x∈xs xs∈cl)

  ∈-zz₁₁ : ∀{A} (x : A) (xs : Colist A)
                (ls rs : List (Colist A)) (cl : Colist (Colist⁺ A))
         → x ∈-∞ xs → xs ∈ ls → x ∈-∞ zig-zag-aux₁ ls rs cl
  ∈-zz₁₁ x (.x :: _) (.(x :: _) :: _) rs cl now now = now
  ∈-zz₁₁ x .(y :: ys) (.(y :: ys) :: xss) rs cl (later {y} {ys} x∈ys) now
    = later (∈-zz₁₂ x (♭ ys) xss (♭ ys :: rs) cl x∈ys now)
  ∈-zz₁₁ x xs .([] :: yss) rs cl x∈xs (later {[]} {yss} xs∈yss)
    = ∈-zz₁₁ x xs yss rs cl x∈xs xs∈yss
  ∈-zz₁₁ x xs .((y :: ys) :: yss) rs cl x∈xs (later {y :: ys} {yss} xs∈yss)
    = later (∈-zz₁₁ x xs yss (♭ ys :: rs) cl x∈xs xs∈yss)

  ∈-zz₁₂ : ∀{A} (x : A) (xs : Colist A)
                (ls rs : List (Colist A)) (cl : Colist (Colist⁺ A))
         → x ∈-∞ xs → xs ∈ rs → x ∈-∞ zig-zag-aux₁ ls rs cl
  ∈-zz₁₂ x xs [] rs []          x∈xs xs∈rs = ∈-zz₀₀ x xs rs [] x∈xs xs∈rs
  ∈-zz₁₂ x xs [] rs ((y , ys) :: yss) x∈xs xs∈rs
    = later (∈-zz₁₁ x xs (ys :: rs) [] (♭ yss) x∈xs (later xs∈rs))
  ∈-zz₁₂ x xs ([] :: yss) rs cl x∈xs xs∈rs = ∈-zz₁₂ x xs yss rs cl x∈xs xs∈rs
  ∈-zz₁₂ x xs ((y :: ys) :: yss) rs cl x∈xs xs∈rs
    = later (∈-zz₁₂ x xs yss (♭ ys :: rs) cl x∈xs (later xs∈rs))

∈-zz : ∀{A} {x : A} {xs : Colist⁺ A} {xss : Colist (Colist⁺ A)}
     → x ∈⁺ xs → xs ∈-∞ xss → x ∈-∞ zig-zag xss
∈-zz {A} {x} {xs} {xss} x∈xs xs∈xss = ∈-zz₁₀ x xs [] [] xss x∈xs xs∈xss

data Stream (A : Set) : Set where
  _::_ : (x : A) (xs : ∞ Stream A) → Stream A

head : ∀{A} → Stream A → A
head (x :: _) = x

tail : ∀{A} → Stream A → Stream A
tail (_ :: xs) = ♭ xs

infixl 70 _!_
_!_ : ∀{A} → Stream A → ℕ → A
(x :: _ ) ! 0     = x
(_ :: xs) ! suc n = ♭ xs ! n

data _∈ˢ_ {A : Set} (x : A) : Stream A → Set where
  now   : ∀{xs}               → x ∈ˢ x :: xs
  later : ∀{y ys} → x ∈ˢ ♭ ys → x ∈ˢ y :: ys

zig-zag-auxˢ : ∀{A} → List (Stream A) → List (Stream A) → Stream (Stream A)
             → Stream A
zig-zag-auxˢ [] rs ((x :: xs) :: xss)
  = x :: ♯ zig-zag-auxˢ (♭ xs :: rs) [] (♭ xss)
zig-zag-auxˢ ((x :: xs) :: ls) rs ss
  = x :: ♯ zig-zag-auxˢ ls (♭ xs :: rs) ss

zig-zagˢ : ∀{A} → Stream (Stream A) → Stream A
zig-zagˢ ss = zig-zag-auxˢ [] [] ss

mutual
  ∈-zzˢ₀ : ∀{A} (x : A) (xs : Stream A)
                (ls rs : List (Stream A)) (ss : Stream (Stream A))
         → x ∈ˢ xs → xs ∈ˢ ss → x ∈ˢ zig-zag-auxˢ ls rs ss
  ∈-zzˢ₀ x .(x :: _) [] rs (.(x :: _) :: _)   now          now = now
  ∈-zzˢ₀ x (y :: ys) [] rs (.(y :: ys) :: ss) (later x∈ys) now
    = later (∈-zzˢ₁ x (♭ ys) (♭ ys :: rs) [] (♭ ss) x∈ys now)
  ∈-zzˢ₀ x xs [] rs ((y :: ys) :: ss) x∈xs (later xs∈ss)
    = later (∈-zzˢ₀ x xs (♭ ys :: rs) [] (♭ ss) x∈xs xs∈ss)
  ∈-zzˢ₀ x xs ((y :: ys) :: ls) rs ss x∈xs xs∈ss
    = later (∈-zzˢ₀ x xs ls (♭ ys :: rs) ss x∈xs xs∈ss)

  ∈-zzˢ₁ : ∀{A} (x : A) (xs : Stream A)
                (ls rs : List (Stream A)) (ss : Stream (Stream A))
         → x ∈ˢ xs → xs ∈ ls → x ∈ˢ zig-zag-auxˢ ls rs ss
  ∈-zzˢ₁ x .(x :: _) .((x :: _) :: _) rs ss now now = now
  ∈-zzˢ₁ x (y :: ys) (.(y :: ys) :: ls) rs ss (later x∈ys) now
    = later (∈-zzˢ₂ x (♭ ys) ls (♭ ys :: rs) ss x∈ys now)
  ∈-zzˢ₁ x xs .((y :: ys) :: ls) rs ss x∈xs (later {y :: ys} {ls} xs∈ls)
    = later (∈-zzˢ₁ x xs ls (♭ ys :: rs) ss x∈xs xs∈ls)

  ∈-zzˢ₂ : ∀{A} (x : A) (xs : Stream A)
                (ls rs : List (Stream A)) (ss : Stream (Stream A))
         → x ∈ˢ xs → xs ∈ rs → x ∈ˢ zig-zag-auxˢ ls rs ss
  ∈-zzˢ₂ x xs []                rs ((y :: ys) :: ss) x∈xs xs∈rs
    = later (∈-zzˢ₁ x xs (♭ ys :: rs) [] (♭ ss) x∈xs (later xs∈rs))
  ∈-zzˢ₂ x xs ((y :: ys) :: ls) rs ss x∈xs xs∈rs
    = later (∈-zzˢ₂ x xs ls (♭ ys :: rs) ss x∈xs (later xs∈rs))

∈-zzˢ : ∀{A} {x : A} {xs : Stream A} {ss : Stream (Stream A)}
      → x ∈ˢ xs → xs ∈ˢ ss → x ∈ˢ zig-zagˢ ss
∈-zzˢ {A} {x} {xs} {ss} x∈xs xs∈ss = ∈-zzˢ₀ x xs [] [] ss x∈xs xs∈ss

tabulate : ∀{A} → (f : ℕ → A) → Stream A
tabulate f = f 0 :: ♯ tabulate (λ n → f (suc n))

∈-tab : ∀{A} → (f : ℕ → A) → ∀ n → f n ∈ˢ tabulate f
∈-tab f zero    = now
∈-tab f (suc n) = later (∈-tab (λ m → f (suc m)) n)

ps-aux : ℕ → Stream (ℕ × ℕ)
ps-aux m = tabulate (_,_ m)

pair-squareˢ : Stream (Stream (ℕ × ℕ))
pair-squareˢ = tabulate ps-aux

∈-ps-aux : ∀ m n → (m , n) ∈ˢ ps-aux m
∈-ps-aux m n = ∈-tab (_,_ m) n

∈-ps : ∀ m → ps-aux m ∈ˢ pair-squareˢ
∈-ps m = ∈-tab ps-aux m

pairsˢ : Stream (ℕ × ℕ)
pairsˢ = zig-zagˢ pair-squareˢ

∈-pairsˢ : ∀ m n → (m , n) ∈ˢ pairsˢ
∈-pairsˢ m n = ∈-zzˢ (∈-ps-aux m n) (∈-ps m)

∈-! : ∀{A} → (x : A) (xs : Stream A) → x ∈ˢ xs → Σ ℕ (λ n → x ≡ xs ! n)
∈-! x .(x ::  _) now                   = 0 , refl
∈-! x .(y :: ys) (later {y} {ys} x∈ys) with ∈-! x (♭ ys) x∈ys
... | (n , eq) = suc n , eq

∈-pairs! : ∀ m n → Σ ℕ (λ k → (m , n) ≡ pairsˢ ! k)
∈-pairs! m n = ∈-! (m , n) pairsˢ (∈-pairsˢ m n)
