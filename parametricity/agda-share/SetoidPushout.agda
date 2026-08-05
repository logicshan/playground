
-- The category of setoids has all pushouts

module SetoidPushout where

Rel : Set → Set₁
Rel A = A → A → Set

record IsEquivalence {A : Set} (_≃_ : Rel A) : Set where
  field
    refl  : ∀{x}     → x ≃ x
    sym   : ∀{x y}   → x ≃ y → y ≃ x
    trans : ∀{x y z} → x ≃ y → y ≃ z → x ≃ z

-- A setoid is a set together with an equivalence relation on that set.
record Setoid : Set₁ where
  field
    Carrier : Set
    _≃_     : Rel Carrier

    isEquiv : IsEquivalence _≃_

  open IsEquivalence isEquiv public

-- Handy notation for the carrier of a setoid
[_] : Setoid → Set
[ S ] = Setoid.Carrier S

-- Propositional equality induces a setoid
module Identity where
  data _≡_ {A : Set} (x : A) : A → Set where
    ≡-refl : x ≡ x

  ≡-sym : ∀{A} {x y : A} → x ≡ y → y ≡ x
  ≡-sym ≡-refl = ≡-refl

  ≡-trans : ∀{A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≡-trans ≡-refl ≡-refl = ≡-refl

  identity : Set → Setoid
  identity A = record { Carrier = A
                      ; _≃_     = _≡_
                      ; isEquiv = record { refl  = ≡-refl
                                         ; sym   = ≡-sym
                                         ; trans = ≡-trans
                                         }
                      }

-- Extensional equality of functions induces a setoid
_→-ext_ : Set → Set → Setoid
A →-ext B = record { Carrier = A → B
                   ; _≃_     = λ f g → ∀ x → f x ≡ g x
                   ; isEquiv = record
                   { refl  = λ _ → ≡-refl
                   ; sym   = λ ex x → ≡-sym (ex x)
                   ; trans = λ ex₁ ex₂ x → ≡-trans (ex₁ x) (ex₂ x)
                   }
                   }
 where
 open Identity

-- Homomorphisms between setoids are respectful functions, that is,
-- functions between their carriers that take equivalent elements to
-- equivalent elements.
module Respectful (S T : Setoid) where
  open Setoid S renaming ( Carrier to A
                         ; _≃_     to _≃A_
                         ; isEquiv to eqvA

                         ; refl  to A-refl
                         ; sym   to A-sym
                         ; trans to A-trans
                         )
  open Setoid T renaming ( Carrier to B
                         ; _≃_     to _≃B_
                         ; isEquiv to eqvB

                         ; refl  to B-refl
                         ; sym   to B-sym
                         ; trans to B-trans
                         )

  record Arr : Set where
    field
      _∙_ : A → B

      respectful : ∀ x y → x ≃A y → _∙_ x ≃B _∙_ y

  open Arr public

  -- Respectful functions themselves naturally form a setoid, where
  -- the equivalence is extensional equality of the underlying functions.
  infixr 0 _⇒_
  _⇒_ : Setoid
  _⇒_ = record { Carrier = Arr
               ; _≃_     = λ f g → ∀ x → (f ∙ x) ≃B (g ∙ x)
               ; isEquiv = record
               { refl  = λ{f} x → B-refl
               ; sym   = λ{f} {g} ex x → B-sym (ex x)
               ; trans = λ{f} {g} {h} ex₁ ex₂ x → B-trans (ex₁ x) (ex₂ x) 
               }
               }

-- Put some useful names in the global scope.
open Respectful using (_⇒_)
open module M₁₄₂₈₅₇ {S} {T} = Respectful S T using (_∙_ ; respectful)

-- The identity function is respectful.
id : ∀{S} → [ S ⇒ S ]
id = record { _∙_        = λ x → x
            ; respectful = λ x y x≃y → x≃y
            }

-- Composition of respectful functions is respectful
_∘_ : ∀{S T U} → [ T ⇒ U ] → [ S ⇒ T ] → [ S ⇒ U ]
g ∘ f = record { _∙_        = λ x → g ∙ (f ∙ x)
               ; respectful = λ x y x≃y → respectful g (f ∙ x) (f ∙ y)
                                         (respectful f x y x≃y)
               }

-- Right and left identity laws for the above identity function.
module ID {S T : Setoid} (f : [ S ⇒ T ]) where
  open Setoid (S ⇒ T) using (_≃_ ; refl)

  left-ident : (id ∘ f) ≃ f
  left-ident = refl {f}

  right-ident : (f ∘ id) ≃ f
  right-ident = refl {f}

-- Associativity of the above composition
module ASSOC {S T U V : Setoid} (f : [ S ⇒ T ])
                                (g : [ T ⇒ U ])
                                (h : [ U ⇒ V ]) where
  open Setoid (S ⇒ V) using (_≃_)
  open Setoid S using (refl)

  assoc : ((h ∘ g) ∘ f) ≃ (h ∘ (g ∘ f))
  assoc x = respectful h (g ∙ (f ∙ x)) (g ∙ (f ∙ x))
           (respectful g (f ∙ x) (f ∙ x)
           (respectful f x x refl))

-- Yay, setoids are a category.

-- We need binary sums to be the carrier of our pushouts.
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

-- The category of setoids has all pushouts.
module HasPushout {S T U : Setoid} (f : [ S ⇒ T ]) (g : [ S ⇒ U ]) where
  record Pushout : Set₁ where
    field
      V : Setoid

      inj₁ : [ T ⇒ V ]
      inj₂ : [ U ⇒ V ]

      comm : Setoid._≃_ (S ⇒ V) (inj₁ ∘ f) (inj₂ ∘ g)

      out : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
                 → (Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
                 → [ V ⇒ Z ]

      factor₁ : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
                     → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
                     → Setoid._≃_ (T ⇒ Z) (out i₁ i₂ c ∘ inj₁) i₁

      factor₂ : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
                     → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
                     → Setoid._≃_ (U ⇒ Z) (out i₁ i₂ c ∘ inj₂) i₂

      unique : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
                    → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
                    → (o : [ V ⇒ Z ])
                    → (Setoid._≃_ (T ⇒ Z) (o ∘ inj₁) i₁)
                    → (Setoid._≃_ (U ⇒ Z) (o ∘ inj₂) i₂)
                    → Setoid._≃_ (V ⇒ Z) (out i₁ i₂ c) o

  -- Pushouts can be constructed by quotienting a sum. We quotient
  -- by the least equivalence relation induced by the underlying
  -- setoid equivalences, together with { (f s, g s) | s ∈ S }.
  data _~_ : Rel ([ T ] ⊎ [ U ]) where
    lift₁ : (x y : [ T ]) → Setoid._≃_ T x y → left  x ~ left  y
    lift₂ : (x y : [ U ]) → Setoid._≃_ U x y → right x ~ right y
    prim₁ : (s : [ S ]) → (left  (f ∙ s)) ~ (right (g ∙ s))
    prim₂ : (s : [ S ]) → (right (g ∙ s)) ~ (left  (f ∙ s))
    link  : ∀ x y z → x ~ y → y ~ z → x ~ z

  ~-refl : (x : [ T ] ⊎ [ U ]) → x ~ x
  ~-refl (left  t) = lift₁ t t (Setoid.refl T)
  ~-refl (right u) = lift₂ u u (Setoid.refl U)

  ~-sym : (x y : [ T ] ⊎ [ U ]) → x ~ y → y ~ x
  ~-sym .(left  x) .(left  y) (lift₁ x y x≃y) = lift₁ y x (Setoid.sym T x≃y)
  ~-sym .(right x) .(right y) (lift₂ x y x≃y) = lift₂ y x (Setoid.sym U x≃y)
  ~-sym .(left (Respectful._∙_ S T f s))
        .(right (Respectful._∙_ S U g s)) (prim₁ s) = prim₂ s
  ~-sym .(right (Respectful._∙_ S U g s))
        .(left (Respectful._∙_ S T f s)) (prim₂ s) = prim₁ s
  ~-sym x z (link .x y .z x~y y~z) = link z y x (~-sym y z y~z) (~-sym x y x~y)

  -- The quotient setoid
  Q : Setoid
  Q = record { Carrier = [ T ] ⊎ [ U ]
             ; _≃_     = _~_
             ; isEquiv = record
             { refl  = λ{x} → ~-refl x
             ; sym   = λ{x} {y} → ~-sym x y
             ; trans = λ{x} {y} {z} → link x y z
             }
             }

  ini₁ : [ T ⇒ Q ]
  ini₁ = record { _∙_        = left
                ; respectful = lift₁
                }

  ini₂ : [ U ⇒ Q ]
  ini₂ = record { _∙_        = right
                ; respectful = lift₂
                }

  oot : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
             → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
             → [ Q ⇒ Z ]
  oot {Z} i₁ i₂ c = record { _∙_        = k
                           ; respectful = r
                           }
   where
   k : [ Q ] → [ Z ]
   k (left  x) = i₁ ∙ x
   k (right y) = i₂ ∙ y

   r : ∀ x y → x ~ y → Setoid._≃_ Z (k x) (k y)
   r .(left  x) .(left  y) (lift₁ x y x≃y) = respectful i₁ x y x≃y
   r .(right x) .(right y) (lift₂ x y x≃y) = respectful i₂ x y x≃y
   r .(left  (f ∙ s)) .(right (g ∙ s)) (prim₁ s) = c s
   r .(right (g ∙ s)) .(left  (f ∙ s)) (prim₂ s) = Setoid.sym Z (c s)
   r .x .z (link x y z x~y y~z) = Setoid.trans Z (r x y x~y) (r y z y~z)

  fac₁ : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
              → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
              → Setoid._≃_ (T ⇒ Z) (oot i₁ i₂ c ∘ ini₁) i₁
  fac₁ {Z} i₁ i₂ c x = Setoid.refl Z

  fac₂ : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
              → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
              → Setoid._≃_ (U ⇒ Z) (oot i₁ i₂ c ∘ ini₂) i₂
  fac₂ {Z} i₁ i₂ c x = Setoid.refl Z

  uniq : ∀{Z} → (i₁ : [ T ⇒ Z ]) (i₂ : [ U ⇒ Z ])
              → (c : Setoid._≃_ (S ⇒ Z) (i₁ ∘ f) (i₂ ∘ g))
              → (o : [ Q ⇒ Z ])
              → (f₁ : Setoid._≃_ (T ⇒ Z) (o ∘ ini₁) i₁)
              → (f₂ : Setoid._≃_ (U ⇒ Z) (o ∘ ini₂) i₂)
              → Setoid._≃_ (Q ⇒ Z) (oot i₁ i₂ c) o
  uniq {Z} i₁ i₂ c o f₁ f₂ (left  x) = Setoid.sym Z (f₁ x)
  uniq {Z} i₁ i₂ c o f₁ f₂ (right y) = Setoid.sym Z (f₂ y)

  -- Success
  mkPushout : Pushout
  mkPushout = record { V       = Q
                     ; inj₁    = ini₁
                     ; inj₂    = ini₂
                     ; comm    = prim₁
                     ; out     = oot
                     ; factor₁ = fac₁
                     ; factor₂ = fac₂
                     ; unique  = uniq
                     }
