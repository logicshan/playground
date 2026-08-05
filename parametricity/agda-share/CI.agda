{-# OPTIONS --copatterns #-}

module CI where

open import Function
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- This module explores induction and coinduction in various ways, and explains
-- the connection between type theory and some category theoretic views of the
-- topic.

module Induction-1 where
  -- In type theory, induction enters in the form of data types. For instance,
  -- the natural numbers.

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  -- In category theory, these definitions correspond to the existence of initial
  -- algebras. The shape of an inductive data type is given by a functor:

  data 1+ (X : Set) : Set where
    zero : 1+ X
    suc : X -> 1+ X

  1+⟨_⟩ : ∀{A B} → (A → B) → 1+ A → 1+ B
  1+⟨ f ⟩ zero = zero
  1+⟨ f ⟩ (suc x) = suc (f x)

  -- and algebras specify how to include the functorial structure into a 'carrier'
  -- object:

  include : 1+ ℕ -> ℕ
  include zero = zero
  include (suc x) = suc x

  -- These algebras form the objects of a category, with arrows being maps between
  -- the carriers that commute with the algebras:

  -- (A, α : F A -> A) -> (B, β : F B -> B)
  --   = h : A -> B
  --
  --         F h
  --    F A ----> F B
  --     |         |
  --   α |         | β
  --     v         v
  --     A ------> B
  --          h
  
  -- An initial algebra has a unique arrow to any other algebra. The existence of
  -- this arrow corresponds to recursive definition by pattern matching on the
  -- inductive type:

  fold-ℕ : ∀{A} → (1+ A -> A) -> ℕ → A
  fold-ℕ alg zero = alg zero
  fold-ℕ alg (suc n) = alg (suc (fold-ℕ alg n))

  lemma₀ : ∀{A} → (alg : 1+ A → A) → (x : 1+ ℕ)
         → fold-ℕ alg (include x) ≡ alg (1+⟨ fold-ℕ alg ⟩ x)
  lemma₀ alg zero = refl
  lemma₀ alg (suc n) = refl
  
  -- The uniqueness of this arrow gives us a proof principle. To see the relation
  -- to type theory will require knowing a bit about how dependent types can be
  -- modeled in category theory.
  --
  -- In type theory, we often think of a family as a function into a collection
  -- of types, A -> Set, even if such functions do not have exactly the same
  -- status as ordinary functions. This view can hold in a categorical context
  -- (it enters into how one defines a 'universe object' for instance). However,
  -- there is another useful way of looking at families that goes in the opposite
  -- direction.
  --
  -- We can view any function f : T -> A as giving a way to think of T as a family
  -- of types indexed by A. f is called a 'display map', and the family at index a : A
  -- is given by the inverse image of f.

  _⁻¹_ : ∀{T A : Set} → (f : T → A) → A → Set
  _⁻¹_ {T} f a = Σ T (λ t → f t ≡ a)

  -- Similarly, we can use Σ to collect any indexed family into a whole type, and
  -- the first projection gives its display map:

  ∫ : {A : Set} → (A → Set) → Set
  ∫ T = Σ _ T

  ∫-disp : {A : Set} (T : A → Set) → ∫ T → A
  ∫-disp T (a , _) = a


  iso₀ : ∀{A : Set} {T : A → Set} {a : A} → ∫-disp T ⁻¹ a → T a
  iso₀ ((a , t) , refl) = t

  iso₁ : ∀{A : Set} {T : A → Set} {a : A} → T a → ∫-disp T ⁻¹ a
  iso₁ {a = a} t = ((a , t) , refl)

  -- These families-as-display-maps form a category, which is just the slice category
  -- over the indexing type. The fact that maps in the slice category must form
  -- commutative triangles corresponds to them being viewable as maps between families
  -- that agree on the indexing value. So a slice map:

  --        α
  --    A ----> B
  --    |       |
  --  f |       | g
  --    v       v
  --    C ===== C

  -- is α : ∀{c} → f ⁻¹ c → g ⁻¹ c. In general there is a correspondence between the
  -- slice categories over a type and a category of families indexed by the same type,
  -- where the arrows of the latter are indexed mappings between the families.

  -- (Side note: this correspondence is not perfect for e.g. Agda. Technically this all
  -- only works given enough extensionality. Without that some correspondences might not
  -- be completely right.)

  -- This machinery lets us flip between functions (algebras, homomorphisms, ...) and
  -- families, and apply properties of one to the other. For instance, if we use the
  -- identity as a display map, it corresponds to the constantly unit family, which is
  -- terminal in these categories. include : 1+ ℕ → ℕ can be seen as the family:

  data Peel-ℕ : ℕ → Set where
    zero : Peel-ℕ zero
    suc  : ∀ n → Peel-ℕ (suc n)

  -- And for any display map f : A → ℕ, we can construct a display map:
  --
  --  1+f = include ∘ 1+⟨ f ⟩ : 1+ A → ℕ
  --
  -- which, can be thought of as:

  data Inc (T : ℕ → Set) : ℕ → Set where
    zero : Inc T zero
    suc : ∀{n} → T n → Inc T (suc n)

  -- The way of giving induction in type theory looks much like recursion above:

  ℕ-induction : ∀{T : ℕ → Set} → T zero → (∀ n → T n → T (suc n)) → ∀ n → T n
  ℕ-induction Tz Ts zero = Tz
  ℕ-induction Tz Ts (suc n) = Ts n (ℕ-induction Tz Ts n)

  -- The question is: what does this have to do with the uniqueness property I mentioned?
  -- We are now in a position to understand. First, let's restructure the
  -- type of induction a bit:

  ℕ-induction' : ∀{T : ℕ → Set} → (∀ n → Inc T n → T n) → (∀ n → ⊤ → T n)
  ℕ-induction' f zero _ = f zero zero
  ℕ-induction' f (suc n) _ = f (suc n) (suc (ℕ-induction' f n _))

  -- It turns out that the proof obligation for induction corresponds to a map
  -- f : ∀ n → Inc T n → T n. If we translate this to the slice category, we get:

  --                  f
  --       1+ (∫ T) ----> ∫ T
  --          |            |
  -- 1+∫-disp |            | ∫-disp
  --          v            v
  --          ℕ ========== ℕ

  -- Note that f is an algebra. But it's not just any algebra, it's an index
  -- preserving algebra (and Inc can be seen as lifting the 1+ functor to families).
  -- This is they key.

  -- Now, because f is an algebra, there is a homomorphism:

  --       
  --         1+ ℕ ----> 1+ (∫ T)
  --          |            |
  --  include |            | f
  --          v            v
  --          ℕ --------> ∫ T
  --              fold f

  -- But, it also happens that ∫-disp is a homomorphism:

  --   1+ (∫ T) ---> 1+ ℕ
  --      |            |
  --    f |            | include
  --      v            v
  --     ∫ T --------> ℕ
  --          ∫-disp

  -- because the top-right path is the display map that corresponds to Inc T, and f
  -- is supposed to form a commutative triangle with it and ∫-disp.

  -- Finally, the uniqueness property tells us that:
  --
  --   ∫-disp ∘ fold f = id : ℕ → ℕ
  --
  -- because there can be only one homomorphism with that type. This gives us a
  -- triangle in the slice category:

  --       fold f
  --    ℕ -------> ∫-T
  --    |           |
  -- id |           | ∫-disp
  --    v           v
  --    ℕ ========= ℕ

  -- So, the uniqueness property lets us know that if we have algebras that work
  -- as slice maps, then we get a homomorphism that works as a slice map, which
  -- is justification (as far as the categorical definition is concerned) for
  -- ℕ-induction' being a more fancily-typed fold.
  
module Coinduction-1 where
  open Induction-1 using (1+; zero; suc)

  -- The hope would be that we can simply apply the above methodology to
  -- coinduction. However, even a little thought reveals some pretty serious
  -- issues. Coinduction, rather than initial algebras, is defined by final
  -- coalgebras:

  --      unfold
  --   A -------> νF
  --   |          |
  -- α |          | observe
  --   v          v
  --  F A -----> F νF

  record coℕ : Set where
    coinductive
    field
      out : 1+ coℕ
  open coℕ

  unfold : ∀{A} → (A → 1+ A) → A → coℕ
  out (unfold α a) with α a
  out (unfold α a) | zero = zero
  out (unfold α a) | suc b = suc (unfold α b)


  -- So various arrows are flipped around relative to induction. The coalgebras
  -- specify how to get an F *out* of the carrier, and the universal homomorphism
  -- goes *into* the codata type.

  -- However, the way we think about families of types is not flipped. They are
  -- still slice objects. This is the most obvious problem, because previously
  -- we used slices over the data type. However, slices over νF have id : νF → νF
  -- as the terminal object. So coinduction giving a unique way of mapping *into*
  -- νF is not actually interesting; we already have that in the slice category
  -- (at least the one we used above).

  lemma₀ : ∀{A : Set} {P : A → Set} → ∀{a} → P a → ⊤
  lemma₀ _ = _

  -- So, even if we could construct all pieces of the induction argument (which
  -- is not completely trivial itself), it would not give us a useful result for
  -- coinduction, and we need to take a different approach.

module Induction-2 where
  open Induction-1 using (ℕ; zero; suc; 1+) 
  -- One possibility for gaining more symmetry is to try working in other slice
  -- categories. An obvious one to try is over a product, which corresponds to
  -- families with two indices. An obvious way to interpret the natural numbers
  -- (or any type A fibered over A × A) is via the diagonal map:

  diag : ℕ → ℕ × ℕ
  diag n = n , n

  -- This display map corresponds to the identity type as a family. There are a
  -- couple ways of seeing this. One is that Σ (A × A) (λ p → proj₁ p ≡ proj₂ p)
  -- is clearly isomorphic to A, and the first projection is going to give you
  -- paris of identical elements. For the ℕ case, it can also be seen as the
  -- inductive family:

  data BiCon : ℕ → ℕ → Set where
    zero : BiCon zero zero
    suc : ∀{m n} → BiCon m n → BiCon (suc m) (suc n)

  -- which clearly has the same structure as the natural numbers (especially if
  -- we imagine that suc does not store m and n, since they are for indexing
  -- purposes), but is presented as a family indexed by two naturals.

  -- Any algebra with carrier A gives rise to an algebra with carrier A × A by
  -- simply applying the algebra to both sides.
  --
  --   α : F A → A
  --   ⟨ α ∘ F fst , α ∘ F snd ⟩ : F (A × A) → A × A

  both : ∀{A} → (1+ A → A) → 1+ (A × A) → A × A
  both α zero = α zero , α zero
  both α (suc (x , y)) = α (suc x) , α (suc y)
  
  -- If we apply this to include : 1+ ℕ → ℕ, we get diag as our unique homomorphism
  -- ℕ → ℕ × ℕ.

  -- This is a natural thing to use for lifting display maps in a similary way as we
  -- did earlier. In fact, for any algebra β : F B → B and display map f : A → B, there
  -- is a display map inc f = β ∘ F f : F A → B. With both include this corresponds to
  -- the family:

  data Inc₂ (R : ℕ → ℕ → Set) : ℕ → ℕ → Set where
    zero : Inc₂ R zero zero
    suc : ∀{m n} → R m n → Inc₂ R (suc m) (suc n)

  -- And we can again consider index-preserving algebras

  --   ρ : ∀{m n} → Inc₂ R m n → R m n
  --
  --                   ρ
  --         1+(∫ R) ----> ∫ R
  --            |           |
  -- inc ∫-disp |           | ∫-disp
  --            v           v
  --          ℕ × ℕ ===== ℕ × ℕ

  -- If we have such an algebra, then there is a unique homomorphism:

  --        1+ ℕ ----> 1+(∫ R)
  --         |           |
  -- include |           | ρ
  --         v           v
  --         ℕ -------> ∫ R
  --            fold ρ

  -- As before, we also know that our display map is a homomorphism
  --
  --    1+(∫ R) --> 1+(ℕ × ℕ)
  --      |             |
  --   ρ  |             | both include
  --      v             v
  --     ∫ R -------> ℕ × ℕ
  --          ∫-disp


  -- So, the composition:
  --   ∫-disp ∘ fold ρ : ℕ → ℕ × ℕ
  -- is also a homomorphism. But we already determined earlier that diag is the unique
  -- such homomorphism. This means fold ρ is a slice map:
  
  --           fold ρ
  --        ℕ -------> ∫ R
  --        |           |
  --   diag |           | ∫-disp
  --        v           v
  --       ℕ×ℕ ======= ℕ×ℕ

  -- And we are again justified in giving a fancy type to our recursion principle:

  bi-induction : ∀{T : ℕ → ℕ → Set} → T zero zero
               → (∀ m n → T m n → T (suc m) (suc n))
               → ∀ m n → m ≡ n → T m n
  bi-induction Tz Ts zero zero refl = Tz
  bi-induction Tz Ts (suc m) (suc n) refl = Ts m n (bi-induction Tz Ts m n refl)
  bi-induction Tz Ts zero (suc n) ()
  bi-induction Tz Ts (suc m) zero ()

  -- If we imagine that the earlier induction principle was for proving that a
  -- predicate holds for all naturals, this one is for proving that a relation on the
  -- naturals is reflexive.

module Coinduction-2 where
  open Induction-1 using (1+; zero; suc)
  open Coinduction-1 using (coℕ; unfold)
  open coℕ

  -- Because of intensionality, for coinduction it will sometimes be more convenient
  -- to work with indexes involving F, rather than the coinductive type directly.
  -- Mainly this is true when we want to talk about maps that commute with incremental
  -- observations. While it's standard that the final coalgebra action out : νF → F νF
  -- is an isomorphism, Agda doesn't actually give a way to establish this, let alone
  -- conveniently work with it.

  -- Given a display map into νF, there are two ways of creating display maps into
  -- F νF:

  -- ∫-disp : ∫ T → νF
  -- F ∫-disp : F (∫ T) → F νF
  -- out ∘ ∫-disp : ∫ T → F νF

  -- These correspond to the types:

  -- F ∫-disp
  data Inc (T : coℕ → Set) : 1+ coℕ → Set where
    zero : Inc T zero
    suc : ∀{n} → T n → Inc T (suc n)

  -- out ∘ ∫-disp
  record Observed (T : coℕ → Set) (m : 1+ coℕ) : Set where
    field
      out : ∀ n → out n ≡ m → T n

  -- If we have a coalgebra τ : ∫ T → F (∫ T), then the index preservation we care
  -- about for it comes via these two constructions. That is, we want τ to be a
  -- slice map:

  --                     τ
  --              ∫ T ------> F (∫ T)
  --               |             |
  --  out ∘ ∫-disp |             | F ∫-disp
  --               v             v
  --              F νF ======== F νF

  -- If the isomorphism held, this would be equivalent to the equation
  --   ∫-disp = in ∘ ∫-disp

  -- In a case where this diagram commutes, τ can be given a type:

  --   τ : ∀{m} → Observed T m → Inc T m

  -- REVISIT --
  -- One might expect that we have a difficulty to overcome from the use of
  -- products. Previously we had a construction F (A × A) → A × A that
  -- applied an algebra on A to both halves of a tuple, which told us that
  -- diag : ℕ → ℕ × ℕ was a homomorphism.
  -- REVISIT --

  -- Now, suppose T : νF × νF → Set

module Dual where
  -- The most obvious way to reuse the original induction argument is to simply
  -- dualize everything, including the slice category. At that point, the same
  -- arguments work out nicely.

  -- The action of the final coalgebra is an object of the category over νF:

  --    out : νF → F νF

  -- Given any coslice object we can construct a new one

  --   f : νF → A 
  --   F f ∘ out : νF → F A

  -- We can consider coalgebras that are also maps of the coslice category:

  --   νF ====== νF
  --   |          |
  -- f |          | F f ∘ out
  --   v          v
  --   A ------> F A
  --        α

  -- Given one of these, we have:

  --       unfold α
  --    A ---------> νF
  --    |             |
  -- α  |             | out
  --    v             v
  --   F A -------> F νF
  
  -- f is by hypothesis a homomorphism:

  --          f
  --    νF -------> A
  --     |          |
  -- out |          | α
  --     v          v
  --   F νF -----> F A

  -- So unfold α ∘ f = id, making unfold α a coslice map:

  --  νF ========== νF
  --   |            |
  -- f |            | id
  --   v            v
  --   A ---------> νF
  --      unfold α

  -- where id is the _initial_ coslice object.
