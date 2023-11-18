module Test where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_] ; lookup)
open import Data.Vec.Properties hiding (lookup-map ; map-lookup-allFin ; tabulate∘lookup)
open import Function hiding (id)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Ucwf

open import Unityped.ImpSub


r1 : Ren 0 0
r1 = []

r2 : Ren 0 0
r2 = id

r3 : Ren 1 1
r3 = ↑ r2              -- [0]

r4 : Ren 1 2
r4 = zero ∷ zero ∷ []  -- [0 0]

r5 : Ren 2 3
r5 = ↑ r4              -- [0 1 1]

r6 : Ren 1 1
r6 = id                -- [0]

r7 : Ren 2 2
r7 = id                -- [0 1]

r8 : Ren 3 3
r8 = id                -- [0 1 2]

r9 : Ren 4 4
r9 = id                -- [0 1 2 3]

r10 : Ren 2 2
r10 = 1 ↑⋆ r6          -- [0 1]

r11 : Ren 3 4
r11 = 2 ↑⋆ r4          -- [0 1 2 2]

r12 : Ren 3 3
r12 = p⋆ 0             -- [0 1 2]

r13 : Ren 4 3
r13 = p⋆ 1             -- [1 2 3]

r14 : Ren 5 3
r14 = p⋆ 2             -- [2 3 4]

r15 : Ren 5 4
r15 = p⋆ 1             -- [1 2 3 4]

x1 : Fin 5
x1 = lookup zero r14   -- 2

x2 : Fin 5
x2 = lookup (suc (suc zero)) r14   -- 4

x3 : Ren 4 3
x3 = tabulate suc
