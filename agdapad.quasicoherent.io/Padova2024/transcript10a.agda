{-# OPTIONS --allow-unsolved-meta #-}
{-
  plan for today:

  1. game theory
  2. simply-typed lambda calculus
  3. your questions
-}


{-
  In Standard Agda and in ordinary Martin-Löf type theory,
  for any two types "A" and "B", we have a type "A ≡ B"
  of equality witnesses between "A" and "B". However,
  unlike in HoTT / CTT, this type is severely underspecified.

  In HoTT / CTT, this defect is remedied. Namely:
  Every equivalence A → B can be turned into an equality witness A ≡ B.
  ("univalence axiom")
-}

module transcript10a where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

module _ (String : Set) where
  data Bool : Set where
    false true : Bool

  record Person : Set where
    field
      surname : String
      age     : ℕ
      address : String

  jenny : Person
  jenny = record
    { surname = {!!}
    ; age     = succ (succ zero)
    ; address = {!!}
    }

  isOfLegalAge : Person → Bool
  isOfLegalAge (record { surname = surname ; age = age ; address = address }) = {!age ≥? 18!}

  isOfLegalAge' : (surname : String) (age : ℕ) (address : String) → Bool
  isOfLegalAge' surname age address = {!!}

record Game : Set₁ where
  field
    Pos  : Set               -- type of possible positions
    Move : Pos → Pos → Set   -- Move a b is the type of possible moves from position a to pos. b

module Basics (G : Game) where
  open Game G
  -- now we have "Pos" and "Move" available;
  -- without opening, we would need to write "Game.Pos G"

  data Winning : Pos → Set
  data Loosing : Pos → Set

  data Winning where
    -- win : {a : Pos} → ...there is a move out of position a which results in a loosing position... → Winning a
    win : {a b : Pos} → Move a b → Loosing b → Winning a
 
  data Loosing where
    -- trivial : {a : Pos} → (...no moves are possible starting in position a...) → Loosing a
    -- trivial : {a : Pos} → ({b : Pos} → Move a b → ⊥) → Loosing a
    -- the "trivial" constructor is redundant

    -- loose   : {a : Pos} → (...no matter which move we take, the next position) → Loosing a
    --                          will be a winning position.....................
    loose   : {a : Pos} → ({b : Pos} → Move a b → Winning b) → Loosing a

  module _ (enum : {!!}) where
    determined : (a : Pos) → Winning a ⊎ Loosing a
    determined = {!!}
  
{-
  |  |  |  |  |  |  |  |  |  |  |
  |  |  |  |  |  |  |  |  |  |  |
  |  |  |  |  |  |  |  |  |  |  |
  |  |  |  |  |  |  |  |  |  |  |
-}
module Take-3 where
  Pos : Set
  Pos = ℕ

  data Move : Pos → Pos → Set where
    take₁ : {n : Pos} → Move (succ n)               n
    take₂ : {n : Pos} → Move (succ (succ n))        n
    take₃ : {n : Pos} → Move (succ (succ (succ n))) n

  G : Game
  G = record { Pos = Pos ; Move = Move }

  open Basics G

  0-loosing : Loosing zero
  0-loosing = loose (λ ())

  1-winning : Winning (succ zero)
  1-winning = win take₁ 0-loosing

  -- TASK: Verify that G is finite in the sense required by "determined".

module Chomp where
  -- 1. The game is finite.
  -- 2. No draw possible.
  -- 3. Hence the game is determined: For one of the two players, a winning strategy needs to exist.
  -- 4. Even though concrete winning strategies are unknown in most cases, we do know that
  --    there is a winning strategy for the first player. ("strategy stealing")
