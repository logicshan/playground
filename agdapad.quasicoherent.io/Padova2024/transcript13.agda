{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Fin
open import Data.Product hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Bool
open import Data.List.Relation.Unary.Any hiding (map)

record IsFinitelyEnumerable (X : Set) : Set where
  field
    elems : List X
    enum  : (x : X) → x ∈ elems

_ : IsFinitelyEnumerable Bool
_ = record
  { elems = false ∷ true ∷ []
  ; enum  = λ { false → here refl ; true → there (here refl) }
  }

_ : IsFinitelyEnumerable ℕ → ⊥
_ = {!!}

-- The type of graphs with an arbitrary number of vertices and
-- an arbitrary number of edges between any two vertices
record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : (a b : Vertex) → Set
    -- "Edge a b" will be the type of edges from a to b

example : Graph
example = record
  { Vertex = V
  ; Edge   = E
  }
  where
  data V : Set where
    u v w : V
  data E : V → V → Set where
    f : E u v
    g : E w v
    h : E w v
{-
     f      g
  u---->v<-----w
        ^      |
        |      |
        +------+
            h
-}

divisibility : Graph
divisibility = record
  { Vertex = ℕ
  ; Edge   = λ a b → Σ[ x ∈ ℕ ] (b ≡ x * a)
                 --  ^^^^^^^^^^^^^^^^^^^^^^ the type of edges from a to b
                 --  This type might be empty, in which case there is no edge from a to b.
  }
{-

     24
     ^^
    / |
    4 6  8
    ^ ^  ^
    |/ \ |
    2----+ 
       |
       |
       3
-}

complete : ℕ → Graph
complete n = record
  { Vertex = Fin n
  ; Edge   = λ a b → ⊤
  }

module _ (G : Graph) where
  open Graph G renaming (Vertex to V; Edge to E)

  -- "Path a b" will be the type of all paths from "a" to "b"
  data Path : V → V → Set where
    _∷[] : {a b : V} → E a b → Path a b
    _∷_  : {a b c : V} → E a b → Path b c → Path a c

  _++ᵖ_ : {a b c : V} → Path a b → Path b c → Path a c
  xs ++ᵖ ys = {!!}

  -- "Neighbor v" will be the type of all neighbors of "v".
  Neighbor : V → Set
  Neighbor v = Σ[ w ∈ V ] E v w
  -- An element of "Neighbor v" is a pair (w , e) consisting of a value w : V
  -- and a value e : E v w.

  -- A graph is locally finite iff every vertex only has finitely many neighbors.
  IsLocallyFinite : Set
  IsLocallyFinite = (v : V) → IsFinitelyEnumerable (Neighbor v)

  IsFinite : Set
  IsFinite = IsFinitelyEnumerable V × IsLocallyFinite

  -- "Reachable a" will be the type of all vertices reachable from a.
  Reachable : V → Set
  Reachable a = Σ[ b ∈ V ] Path a b

  neighbor→reachable : {a : V} → Neighbor a → Reachable a
  neighbor→reachable (v , e) = v , e ∷[]

  -- Objective: Given a vertex "a", compute the list of all vertices reachable from "a".
  module _ (fin : IsFinite) where
    open IsFinitelyEnumerable

    {-# TERMINATING #-}
    dfs : (a : V) → (seen : List V) → List (Reachable a)
    dfs a seen =
      map neighbor→reachable all-neighbors ++
      concat (map (λ (v , e) → map (λ (w , p) → w , e ∷ p) (dfs v seen')) unseen-neighbors)
      where
      -- concat : {A : Set} → List (List A) → List A

      all-neighbors : List (Neighbor a)
      all-neighbors = elems (proj₂ fin a)

      unseen-neighbors : List (Neighbor a)
      unseen-neighbors = filter (λ (v , e) → {!!}) all-neighbors
                          -- ^^^^^^^^^^^^^^^^^^
                          -- formalize the property that "v" is not an element of "seen"

      seen' = map proj₁ all-neighbors ++ seen

    -- Take care: Not correctly stated, should require only target vertex of z to be mentioned in "dfs a []".
    theorem : {a : V} → (z : Reachable a) → z ∈ dfs a []
    theorem (v , (e ∷[])) = {!!}
    theorem (v , (e ∷ p)) = {!theorem ...!}

record WeightedGraph (L : Set) : Set₁ where
  field
    Vertex : Set
    Edge   : (a b : Vertex) → Set
    weight : {a b : Vertex} (e : Edge a b) → L

record ColoredGraph (C : Set) : Set₁ where
  field
    Vertex : Set
    Edge   : (a b : Vertex) → Set
    color  : Vertex → C
