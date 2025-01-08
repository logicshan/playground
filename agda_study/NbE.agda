import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open Eq using (refl; trans; sym; _≡_; cong; cong₂; cong-app)
open Eq.≡-Reasoning

module NbE where

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g


data Type : Set where
  -- unit
  𝟙   : Type

  -- functions
  _⇒_ : ∀ (S T : Type) → Type

infixr 7 _⇒_

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

infixl 5 _,_

data _∋_ : Ctx → Type → Set where
  𝑍 : ∀ {Γ : Ctx} {T : Type}
        ---------
      → Γ , T ∋ T

  𝑆_ : ∀ {Γ : Ctx} {S T : Type}
      → Γ ∋ T
        ---------
      → Γ , S ∋ T

infix 4 _∋_
infix 9 𝑆_

module Example (S T : Type) where
  ∅,x:S,y:T = ∅ , S , T

  x : ∅,x:S,y:T ∋ S
  x = 𝑆 𝑍

  y : ∅,x:S,y:T ∋ T
  y = 𝑍

data _⊢_ (Γ : Ctx) : Type → Set where
  -- unit term
  unit : Γ ⊢ 𝟙

  -- variable
  #_ : ∀ {S : Type}
     → Γ ∋ S
       -----
     → Γ ⊢ S

  -- abstraction
  ƛ_ : ∀ {S T : Type}
     → Γ , S ⊢ T
       ---------
     → Γ ⊢ S ⇒ T

  -- application
  _·_ : ∀ {S T : Type}
      → Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 #_

module SamplePrograms where
  -- Γ ⊢ λx. x : T → T
  ex0 : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T ⇒ T
  ex0 = ƛ # 𝑍

  -- ∅ ⊢ (λx. x) unit : 𝟙
  ex1 : ∅ ⊢ 𝟙
  ex1 = ex0 · unit

data _≤_ : Ctx → Ctx → Set where
  ≤-id : ∀ {Γ : Ctx} → Γ ≤ Γ

  ≤-ext : ∀ {Γ Γ′ : Ctx} {T : Type}
        → Γ′ ≤ Γ
          ----------
        → Γ′ , T ≤ Γ

infix 4 _≤_

invert-≤ : ∀ {Γ Γ′ : Ctx} {T : Type}
         → Γ′ ≤ Γ , T
           ----------
         → Γ′ ≤ Γ
invert-≤ ≤-id = ≤-ext ≤-id
invert-≤ (≤-ext ext) = ≤-ext (invert-≤ ext)

≤-antisym : ∀ {Γ Γ′ : Ctx}
          → Γ ≤ Γ′
          → Γ′ ≤ Γ
            ------
          → Γ ≡ Γ′

Γ≰Γ,T : ∀ {Γ : Ctx} {T : Type} → ¬ (Γ ≤ Γ , T)

≤-ext-uniq-T : ∀ {Γ Γ′ : Ctx} {S T : Type}
           → Γ′ ≤ Γ , T
           → Γ′ ≤ Γ , S
             ----------
           → T ≡ S

≤-ext-uniq-T ≤-id ≤-id = refl
≤-ext-uniq-T ≤-id (≤-ext c) = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext c) ≤-id = ⊥-elim (Γ≰Γ,T c)
≤-ext-uniq-T (≤-ext p₁) (≤-ext p₂)
  rewrite ≤-ext-uniq-T p₁ p₂ = refl

≤-antisym ≤-id Γ′≤Γ = refl
≤-antisym (≤-ext Γ≤Γ′) ≤-id = refl
≤-antisym (≤-ext {T = T₁} p₁) (≤-ext {T = T₂} p₂)
  with invert-≤ p₁ | invert-≤ p₂
...  | ≤→         | ≤←
  with ≤-antisym ≤→ ≤←
...  | refl
  rewrite ≤-ext-uniq-T p₁ p₂     = refl

Γ≰Γ,T {Γ} {T} Γ≤Γ,T
  with ≤-ext {T = T} (≤-id {Γ})
...  | Γ,T≤Γ
  with ≤-antisym Γ≤Γ,T Γ,T≤Γ
...  | ()

≤-trans : ∀ {Γ″ Γ′ Γ : Ctx}
         → Γ″ ≤ Γ′
         → Γ′ ≤ Γ
           -------
         → Γ″ ≤ Γ
≤-trans ≤-id ≤-id               = ≤-id
≤-trans ≤-id (≤-ext pf)         = ≤-ext pf
≤-trans (≤-ext pf) ≤-id         = ≤-ext pf
≤-trans (≤-ext pf₁) (≤-ext pf₂) = ≤-ext (≤-trans pf₁ (≤-ext pf₂))

_≟Tp_ : ∀ (S T : Type) → Dec (S ≡ T)
𝟙         ≟Tp 𝟙                                    = yes refl
𝟙         ≟Tp (S ⇒ T)                              = no λ()
(S₁ ⇒ T₁) ≟Tp 𝟙                                    = no λ()
(S₁ ⇒ T₁) ≟Tp (S₂ ⇒ T₂) with S₁ ≟Tp S₂ | T₁ ≟Tp T₂
...                        | no ¬pf    | no _      = no λ{refl → ¬pf refl}
...                        | no ¬pf    | yes _     = no λ{refl → ¬pf refl}
...                        | yes _     | no ¬pf    = no λ{refl → ¬pf refl}
...                        | yes refl  | yes refl  = yes refl

_≟Ctx_ : (Γ Γ′ : Ctx) → Dec (Γ ≡ Γ′)

∅       ≟Ctx ∅                                  = yes refl
∅       ≟Ctx (_ , _)                            = no λ()
(_ , _) ≟Ctx ∅                                  = no λ()
(Γ′ , S) ≟Ctx (Γ , T) with Γ′ ≟Ctx Γ | S ≟Tp T
...                      | no ¬pf    | no _     = no λ{refl → ¬pf refl}
...                      | no ¬pf    | yes _    = no λ{refl → ¬pf refl}
...                      | yes _     | no ¬pf   = no λ{refl → ¬pf refl}
...                      | yes refl  | yes refl = yes refl

_≤?_ : ∀ (Γ′ Γ : Ctx) → Dec (Γ′ ≤ Γ)
∅        ≤? ∅          = yes ≤-id
∅        ≤? (_ , _)    = no λ()
(_ , _)  ≤? ∅          = yes Γ≤∅ where
  Γ≤∅ : ∀ {Γ : Ctx} → Γ ≤ ∅
  Γ≤∅ {∅}     = ≤-id
  Γ≤∅ {Γ , _} = ≤-ext Γ≤∅
(Γ′ , T) ≤? Γ@(_ , _)
  with (Γ′ , T) ≟Ctx Γ
...  | yes refl        = yes ≤-id
...  | no Γ′≢Γ
  with Γ′ ≤? Γ
...  | yes pf          = yes (≤-ext pf)
...  | no ¬pf          = no λ where
                           ≤-id       → Γ′≢Γ refl
                           (≤-ext pf) → ¬pf pf

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {T : Type} → Δ ∋ T → Γ ⊢ T

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {T : Type} → Δ ∋ T → Γ ∋ T

ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
ren ρ x = # ρ x

idʳ : ∀ {Γ : Ctx} → Ren Γ Γ
idʳ x = x

↥ʳ : ∀ {Γ : Ctx} {T : Type} → Ren (Γ , T) Γ
↥ʳ x = 𝑆 x

_∘ʳ_ : ∀ {Γ Δ Σ : Ctx} → Ren Δ Γ → Ren Σ Δ → Ren Σ Γ
ρ ∘ʳ ω = λ x → ω (ρ x)

infixr 9 _∘ʳ_

ρ-≤ : ∀ {Γ′ Γ : Ctx} → Γ′ ≤ Γ → Ren Γ′ Γ
ρ-≤ ≤-id       = idʳ
ρ-≤ (≤-ext pf) = ρ-≤ pf ∘ʳ ↥ʳ

ext : ∀ {Γ Δ : Ctx} → Ren Γ Δ → ∀ {T : Type} → Ren (Γ , T) (Δ , T)
ext ρ 𝑍     = 𝑍
ext ρ (𝑆 x) = 𝑆 ρ x

_[_]ʳ : ∀ {Γ Δ : Ctx} {T : Type}
      → Δ ⊢ T
      → Ren Γ Δ
        -------
      → Γ ⊢ T
unit [ _ ]ʳ    = unit
# x [ ρ ]ʳ     = # ρ x
(ƛ t) [ ρ ]ʳ   = ƛ t [ ext ρ ]ʳ
(r · s) [ ρ ]ʳ = r [ ρ ]ʳ · s [ ρ ]ʳ

infix 8 _[_]ʳ

exts : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ∀ {T : Type} → Sub (Γ , T) (Δ , T)
exts σ 𝑍     = # 𝑍
exts σ (𝑆 x) = (σ x) [ ↥ʳ ]ʳ

_[_] : ∀ {Γ Δ : Ctx} {T : Type}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
unit [ _ ]    = unit
# x [ σ ]     = σ x
(ƛ t) [ σ ]   = ƛ t [ exts σ ]
(r · s) [ σ ] = r [ σ ] · s [ σ ]

infix 8 _[_]

id : ∀ {Γ : Ctx} → Sub Γ Γ
id x = # x

↥ : ∀ {Γ : Ctx} {T : Type} → Sub (Γ , T) Γ
↥ x = # 𝑆 x

_∘_ : ∀ {Γ Δ Σ : Ctx} → Sub Δ Γ → Sub Σ Δ → Sub Σ Γ
(σ ∘ τ) x = (σ x) [ τ ]

_∷_ : ∀ {Γ Δ : Ctx} {S : Type} → Sub Γ Δ → Γ ⊢ S → Sub Γ (Δ , S)
(_ ∷ s) 𝑍     = s
(σ ∷ _) (𝑆 x) = σ x

infix 8 _∷_
infixr 9 _∘_

weaken : ∀ {Γ′ Γ : Ctx}
       → Γ′ ≤ Γ
         --------
       → Sub Γ′ Γ
weaken pf x = # ρ-≤ pf x

_≤⊢_ : ∀ {Γ′ Γ : Ctx} {T : Type} → Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

_↥⊢_ : ∀ {Γ : Ctx} {T : Type} → (S : Type) → Γ ⊢ T → Γ , S ⊢ T
_ ↥⊢ t = t [ ↥ ]

infixr 5 _↥⊢_
infixr 5 _≤⊢_

sub-tail : ∀ {Γ Δ : Ctx} {S T : Type} {s : Γ ⊢ S} {σ : Sub Γ Δ}
         → (↥ ∘ (σ ∷ s)) {T = T} ≡ σ
sub-tail = refl

sub-dist : ∀ {Γ Δ Σ : Ctx} {S T : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {s : Δ ⊢ S}
         → (σ ∷ s) ∘ τ ≡ (σ ∘ τ ∷ (s [ τ ])) {T}
sub-dist {Σ = Σ} {S} {T} {τ} {σ} {s} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → ((σ ∷ s) ∘ τ) x ≡ ((σ ∘ τ) ∷ (s [ τ ])) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

cong-ext : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type}
         → (∀ {S : Type} → ρ ≡ ρ′ {S})
         → ∀ {S : Type} → ext ρ {T} {S} ≡ ext ρ′
cong-ext {Δ = Δ} {ρ} {ρ′} {T} ρ≡ρ′ {S} = extensionality lemma where
  lemma : ∀ (x : Δ , T ∋ S) → ext ρ x ≡ ext ρ′ x
  lemma 𝑍                      = refl
  lemma (𝑆 x) rewrite ρ≡ρ′ {S} = refl

cong-rename : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Type} {t : Δ ⊢ T}
            → (∀ {S : Type} → ρ ≡ ρ′ {S})
            → t [ ρ ]ʳ ≡ t [ ρ′ ]ʳ
cong-rename {t = unit} _                                                = refl
cong-rename {T = T} {# x} ρ≡ρ′ rewrite ρ≡ρ′ {T}                         = refl
cong-rename {ρ = ρ} {ρ′} {t = ƛ t} ρ≡ρ′
  rewrite cong-rename {ρ = ext ρ} {ρ′ = ext ρ′} {t = t} (cong-ext ρ≡ρ′) = refl
cong-rename {t = r · s} ρ≡ρ′
  rewrite cong-rename {t = r} ρ≡ρ′ | cong-rename {t = s} ρ≡ρ′           = refl

cong-exts : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type}
          → (∀ {S : Type} → σ ≡ σ′ {S})
          → (∀ {S : Type} → exts σ {T} {S} ≡ exts σ′)
cong-exts {Δ = Δ} {σ} {σ′} {T} σ≡σ′ {S} = extensionality lemma where
  lemma : ∀ (x : Δ , T ∋ S) → exts σ x ≡ exts σ′ x
  lemma 𝑍                      = refl
  lemma (𝑆 x) rewrite σ≡σ′ {S} = refl

cong-sub : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Type} {t t′ : Δ ⊢ T}
         → (∀ {S : Type} → σ ≡ σ′ {S})
         → t ≡ t′
         → t [ σ ] ≡ t′ [ σ′ ]
cong-sub {t = unit} {unit} _ _                                          = refl
cong-sub {T = T} {t = # x} σ≡σ′ refl rewrite σ≡σ′ {T}                   = refl
cong-sub {σ = σ} {σ′} {t = ƛ t} σ≡σ′ refl
  rewrite cong-sub {σ = exts σ} {exts σ′} {t = t} (cong-exts σ≡σ′) refl = refl
cong-sub {σ = σ} {σ′} {t = r · s} σ≡σ′ refl
  rewrite cong-sub {σ = σ} {σ′} {t = r} σ≡σ′ refl
        | cong-sub {σ = σ} {σ′} {t = s} σ≡σ′ refl                       = refl

cong-cons : ∀ {Γ Δ : Ctx} {S : Type} {s s′ : Γ ⊢ S} {σ τ : Sub Γ Δ}
          → s ≡ s′
          → (∀ {T : Type} → σ {T} ≡ τ {T})
          → ∀ {T : Type} → σ ∷ s ≡ (τ ∷ s′) {T}
cong-cons {Δ = Δ} {S} {s} {s′} {σ} {τ} refl σ≡τ {T} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → (σ ∷ s) x ≡ (τ ∷ s′) x
  lemma 𝑍                     = refl
  lemma (𝑆 x) rewrite σ≡τ {T} = refl

cong-seq : ∀ {Γ Δ Σ : Ctx} {τ τ′ : Sub Γ Δ} {σ σ′ : Sub Δ Σ}
         → (∀ {T : Type} → σ {T} ≡ σ′)
         → (∀ {T : Type} → τ {T} ≡ τ′)
         → (∀ {T : Type} → (σ ∘ τ) {T} ≡ σ′ ∘ τ′)
cong-seq {Σ = Σ} {τ} {τ′} {σ} {σ′} σ≡σ′ τ≡τ′ {T} = extensionality lemma where
  lemma : ∀ (x : Σ ∋ T) → (σ ∘ τ) x ≡ (σ′ ∘ τ′) x
  lemma x rewrite σ≡σ′ {T} | cong-sub {t = σ′ x} τ≡τ′ refl = refl

ren-ext : ∀ {Γ Δ : Ctx} {S T : Type} {ρ : Ren Γ Δ}
        → ren (ext ρ) ≡ exts (ren ρ) {S} {T}
ren-ext {Δ = Δ} {S} {T} {ρ} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

rename-subst-ren : ∀ {Γ Δ : Ctx} {T : Type} {ρ : Ren Γ Δ} {t : Δ ⊢ T}
                 → t [ ρ ]ʳ ≡ t [ ren ρ ]
rename-subst-ren {t = unit}                                           = refl
rename-subst-ren {t = # x}                                            = refl
rename-subst-ren {ρ = ρ} {ƛ t}
  rewrite rename-subst-ren {ρ = ext ρ} {t}
        | cong-sub {t = t} (ren-ext {ρ = ρ}) refl                     = refl
rename-subst-ren {ρ = ρ} {r · s}
  rewrite rename-subst-ren {ρ = ρ} {r} | rename-subst-ren {ρ = ρ} {s} = refl

ren-shift : ∀ {Γ : Ctx} {S T : Type}
          → ren ↥ʳ ≡ ↥ {Γ} {S} {T}
ren-shift {Γ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Γ ∋ T) → ren ↥ʳ x ≡ ↥ x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

rename-shift : ∀ {Γ : Ctx} {S T : Type} {s : Γ ⊢ S}
             → s [ ↥ʳ {T = T} ]ʳ ≡ s [ ↥ ]
rename-shift {Γ} {S} {T} {s}
  rewrite rename-subst-ren {ρ = ↥ʳ {T = T}} {s}
        | ren-shift {Γ} {T} {S}                = refl

exts-cons-shift : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ Δ}
                → exts σ {S} {T} ≡ (σ ∘ ↥) ∷ # 𝑍
exts-cons-shift {Δ = Δ} {S} {T} {σ} = extensionality lemma where
  lemma : ∀ (x : Δ , S ∋ T) → exts σ x ≡ ((σ ∘ ↥) ∷ # 𝑍) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = rename-subst-ren

exts-ids : ∀ {Γ : Ctx} {S T : Type}
         → exts id ≡ id {Γ , S} {T}
exts-ids {Γ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Γ , S ∋ T) → exts id x ≡ id x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

[id]-identity : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
              → t [ id ] ≡ t
[id]-identity {t = unit}                                = refl
[id]-identity {t = # x}                                 = refl
[id]-identity {T = S ⇒ T} {ƛ t}
  rewrite cong-sub {t = t} exts-ids refl
        | [id]-identity {t = t}                         = refl
[id]-identity {t = r · s}
  rewrite [id]-identity {t = r} | [id]-identity {t = s} = refl

sub-idR : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {T : Type}
        → (σ ∘ id) ≡ σ {T}
sub-idR = extensionality (λ _ → [id]-identity)

compose-ext : ∀ {Γ Δ Σ : Ctx} {ρ : Ren Δ Σ} {ω : Ren Γ Δ} {S T : Type}
            → (ext ρ) ∘ʳ (ext ω) ≡ ext (ρ ∘ʳ ω) {S} {T}
compose-ext {Σ = Σ} {ρ} {ω} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → ((ext ρ) ∘ʳ (ext ω)) x ≡ ext (ρ ∘ʳ ω) x
  lemma 𝑍     = refl
  lemma (𝑆 x) = refl

compose-rename : ∀ {Γ Δ Σ : Ctx} {T : Type} {t : Σ ⊢ T} {ω : Ren Γ Δ}
                   {ρ : Ren Δ Σ}
               → t [ ρ ]ʳ [ ω ]ʳ ≡ t [ ρ ∘ʳ ω ]ʳ
compose-rename {t = unit}                               = refl
compose-rename {t = # x}                                = refl
compose-rename {T = S ⇒ T} {ƛ t} {ω} {ρ}
  rewrite compose-rename {t = t} {ext ω} {ext ρ}
        | cong-rename {t = t} (compose-ext {ρ = ρ} {ω}) = refl
compose-rename {t = r · s} {ω} {ρ}
  rewrite compose-rename {t = r} {ω} {ρ}
        | compose-rename {t = s} {ω} {ρ}                = refl

commute-subst-rename : ∀ {Γ Δ Σ Φ : Ctx} {T : Type} {t : Σ ⊢ T}
                         {σ : Sub Γ Δ} {ρ : Ren Δ Σ}
                         {ρ′ : Ren Γ Φ } {σ′ : Sub Φ Σ}
                     → (∀ {S : Type} {x : Σ ∋ S} → σ (ρ x) ≡ σ′ x [ ρ′ ]ʳ)
                     → t [ ρ ]ʳ [ σ ] ≡ t [ σ′ ] [ ρ′ ]ʳ
commute-subst-rename {t = unit} pf = refl
commute-subst-rename {t = # x} pf = pf
commute-subst-rename {Σ = Σ} {T = S ⇒ T} {ƛ t} {σ} {ρ} {ρ′} {σ′} pf =
  cong ƛ_ (commute-subst-rename {t = t} (λ {_} {x} → H x))
  where
    H : ∀ {U : Type} (x : Σ , S ∋ U) → exts σ (ext ρ x) ≡ exts σ′ x [ ext ρ′ ]ʳ
    H 𝑍 = refl
    H (𝑆 x) rewrite pf {x = x}
                  | compose-rename {t = σ′ x} {↥ʳ {T = S}} {ρ′}
                  | compose-rename {t = σ′ x} {ext ρ′ {S}} {↥ʳ} = refl
commute-subst-rename {t = r · s} {σ} {ρ} {ρ′} {σ′} pf
  rewrite commute-subst-rename {t = r} {σ} {ρ} {ρ′} {σ′} pf
        | commute-subst-rename {t = s} {σ} {ρ} {ρ′} {σ′} pf = refl

sub-𝑆-shift : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ (Δ , S)} {x : Δ ∋ T}
            → σ (𝑆_ {T = T} x) ≡ (↥ ∘ σ) x
sub-𝑆-shift = refl

exts-seq : ∀ {Γ Δ Σ : Ctx} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {S : Type}
         → ∀ {T : Type} → (exts σ ∘ exts τ) ≡ exts (σ ∘ τ) {S} {T}
exts-seq {Σ = Σ} {τ} {σ} {S} {T} = extensionality lemma where
  lemma : ∀ (x : Σ , S ∋ T) → (exts σ ∘ exts τ) x ≡ exts (σ ∘ τ) x
  lemma 𝑍  = refl
  lemma (𝑆 x) rewrite sub-𝑆-shift {S = S} {σ = exts σ ∘ exts τ} {x} =
    commute-subst-rename {t = σ x} refl

sub-sub : ∀ {Γ Δ Σ : Ctx} {T : Type} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {t : Σ ⊢ T}
        → t [ σ ] [ τ ] ≡ t [ σ ∘ τ ]
sub-sub {t = unit} = refl
sub-sub {t = # x} = refl
sub-sub {τ = τ} {σ} {ƛ t} =
  begin
    (ƛ t) [ σ ] [ τ ]
  ≡⟨⟩
    ƛ t [ exts σ ] [ exts τ ]
  ≡⟨ cong ƛ_ (sub-sub {τ = exts τ} {exts σ} {t}) ⟩
    ƛ t [ exts σ ∘ exts τ ]
  ≡⟨ cong ƛ_ (cong-sub {t = t} exts-seq refl) ⟩
    ƛ t [ exts (σ ∘ τ) ]
  ∎
sub-sub {τ = τ} {σ} {r · s}
  rewrite sub-sub {τ = τ} {σ} {r} | sub-sub {τ = τ} {σ} {s} = refl

sub-assoc : ∀ {Γ Δ Σ Φ : Ctx} {σ : Sub Δ Γ} {τ : Sub Σ Δ} {θ : Sub Φ Σ}
          → ∀ {T : Type} → (σ ∘ τ) ∘ θ ≡ (σ ∘ τ ∘ θ) {T}
sub-assoc {Γ} {σ = σ} {τ} {θ} {T} = extensionality lemma where
  lemma : ∀ (x : Γ ∋ T) → ((σ ∘ τ) ∘ θ) x ≡ (σ ∘ τ ∘ θ) x
  lemma x rewrite sub-sub {τ = θ} {τ} {t = σ x} = refl

subst-zero-exts-cons : ∀ {Γ Δ : Ctx} {S T : Type} {σ : Sub Γ Δ} {s : Γ ⊢ S}
                     → exts σ ∘ (id ∷ s) ≡ (σ ∷ s) {T}
subst-zero-exts-cons {S = S} {T} {σ} {s} =
  begin
    exts σ ∘ (id ∷ s)
  ≡⟨ cong-seq exts-cons-shift refl ⟩
    ((σ ∘ ↥) ∷ # 𝑍) ∘ (id ∷ s)
  ≡⟨ sub-dist ⟩
    ((σ ∘ ↥) ∘ (id ∷ s)) ∷ s
  ≡⟨ cong-cons refl (sub-assoc {σ = σ}) ⟩
    (σ ∘ ↥ ∘ (id ∷ s)) ∷ s
  ≡⟨ cong-cons refl (cong-seq {σ = σ} refl (sub-tail {s = s} {σ = id})) ⟩
    (σ ∘ id) ∷ s
  ≡⟨ cong-cons refl (sub-idR {σ = σ}) ⟩
    σ ∷ s
  ∎

_[_]₀ : ∀ {Γ : Ctx} {S T : Type}
  → Γ , S ⊢ T
  → Γ ⊢ S
    ---------
  → Γ ⊢ T
_[_]₀ {Γ} {S} t s = t [ id ∷ s ]

infix 8 _[_]₀

η-expand : ∀ {Γ : Ctx} {S T : Type}
         → Γ ⊢ S ⇒ T
         → Γ ⊢ S ⇒ T
η-expand {S = S} t = ƛ (S ↥⊢ t) · # 𝑍

data _==_ : ∀ {Γ : Ctx} {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where
  -- computation rule: beta reduction
  β : ∀ {Γ : Ctx} {S T : Type}
          {t : Γ , S ⊢ T}
          {s : Γ ⊢ S}
          ----------------------
        → (ƛ t) · s == t [ s ]₀

  -- η-expansion / function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Ctx} {S T : Type}
        {t : Γ ⊢ S ⇒ T}
        ----------------------
      → t == η-expand t

  -- compatibility rules
  abs-compatible : ∀ {Γ : Ctx} {S T : Type} {t t′ : Γ , S ⊢ T}
                   → t == t′
                     -----------
                   → ƛ t == ƛ t′

  app-compatible : ∀ {Γ : Ctx} {S T : Type}
                     {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
                   → r == r′
                   → s == s′
                     ----------------
                   → r · s == r′ · s′

  -- equivalence rules
  refl⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t : Γ ⊢ T}
           ------
         → t == t

  sym⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
        → t == t′
          -------
        → t′ == t

  trans⁼⁼ : ∀ {Γ : Ctx} {T : Type} {t₁ t₂ t₃ : Γ ⊢ T}
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃

infix 3 _==_

module ==-Reasoning where

  infix  1 begin==_
  infixr 2 _==⟨_⟩_
  infix  3 _==∎

  begin==_ : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
           → t == t′
             -------
           → t == t′
  begin== pf = pf

  _==⟨_⟩_ : ∀ {Γ : Ctx} {T : Type} {t₂ t₃ : Γ ⊢ T}
          → (t₁ : Γ ⊢ T)
          → t₁ == t₂
          → t₂ == t₃
            --------
          → t₁ == t₃
  t₁ ==⟨ t₁≡t₂ ⟩ t₂≡t₃  =  trans⁼⁼ t₁≡t₂ t₂≡t₃

  _==∎ : ∀ {Γ : Ctx} {T : Type} → (t : Γ ⊢ T)
         ------
       → t == t
  t ==∎  =  refl⁼⁼

open ==-Reasoning public

≡→== : ∀ {Γ : Ctx} {T : Type} {t t′ : Γ ⊢ T}
     → t ≡ t′
       -------
     → t == t′
≡→== pf rewrite pf = refl⁼⁼

record Interpretation (D : Set) : Set₁ where
  field
    ⟦_⟧ : D → Set

open Interpretation ⦃...⦄ public

instance
    ⟦Γ⟧ : ⦃ _ : Interpretation Type ⦄ → Interpretation Ctx
    Interpretation.⟦ ⟦Γ⟧ ⟧ ∅ = ⊤
    Interpretation.⟦ ⟦Γ⟧ ⟧ (Γ , T) = ⟦ Γ ⟧ × ⟦ T ⟧
