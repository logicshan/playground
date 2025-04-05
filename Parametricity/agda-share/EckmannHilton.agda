
-- A formalization of the Eckmann-Hilton argument

open import Relation.Binary.PropositionalEquality

-- Given a set M, and two unital binary operations (•, e₁) and (∗, e₂)
-- on M, such that the below exchange law holds...
module EckmannHilton
          (M     : Set)
          (_•_   : M → M → M)
          (_∗_   : M → M → M)
          (e₁ e₂ : M)
          (idˡ₁ : ∀ y → e₁ • y ≡ y)
          (idˡ₂ : ∀ y → e₂ ∗ y ≡ y)
          (idʳ₁ : ∀ x → x • e₁ ≡ x)
          (idʳ₂ : ∀ x → x ∗ e₂ ≡ x)
          (exch   : ∀ w x y z → (w ∗ x) • (y ∗ z) ≡ (w • y) ∗ (x • z)) where

import Relation.Binary.EqReasoning as Reasoning

open Reasoning (setoid M)

-- the units are the same...
id-same : e₂ ≡ e₁
id-same = begin
            e₂
          ≡⟨ sym (idˡ₂ e₂) ⟩
            e₂ ∗ e₂
          ≡⟨ cong (λ z → z ∗ e₂) (sym (idˡ₁ e₂)) ⟩
            (e₁ • e₂) ∗ e₂
          ≡⟨ cong (λ z → (e₁ • e₂) ∗ z) (sym (idʳ₁ e₂)) ⟩
            (e₁ • e₂) ∗ (e₂ • e₁)
          ≡⟨ sym (exch e₁ e₂ e₂ e₁) ⟩
            (e₁ ∗ e₂) • (e₂ ∗ e₁)
          ≡⟨ cong (λ z → z • (e₂ ∗ e₁)) (idʳ₂ e₁) ⟩
            e₁ • (e₂ ∗ e₁)
          ≡⟨ cong (λ z → e₁ • z) (idˡ₂ e₁) ⟩
            e₁ • e₁
          ≡⟨ idˡ₁ e₁ ⟩
            e₁
          ∎

-- the operations are the same...
op-same : ∀ x y → x • y ≡ x ∗ y
op-same x y = begin
                x • y
              ≡⟨ cong (λ z → z • y) (sym (idʳ₂ x)) ⟩
                (x ∗ e₂) • y
              ≡⟨ cong (λ z → (x ∗ e₂) • z) (sym (idˡ₂ y)) ⟩
                (x ∗ e₂) • (e₂ ∗ y)
              ≡⟨ exch x e₂ e₂ y ⟩
                (x • e₂) ∗ (e₂ • y)
              ≡⟨ cong (λ e → (x • e) ∗ (e • y)) id-same ⟩
                (x • e₁) ∗ (e₁ • y)
              ≡⟨ cong (λ z → z ∗ (e₁ • y)) (idʳ₁ x) ⟩
                x ∗ (e₁ • y)
              ≡⟨ cong (λ z → x ∗ z) (idˡ₁ y) ⟩
                x ∗ y
              ∎

-- and the operation is commutative.
comm₁ : ∀ x y → x • y ≡ y • x
comm₁ x y = begin 
              x • y
            ≡⟨ cong (λ z → z • y) (sym (idˡ₂ x)) ⟩
              (e₂ ∗ x) • y
            ≡⟨ cong (λ z → (e₂ ∗ x) • z) (sym (idʳ₂ y)) ⟩
              (e₂ ∗ x) • (y ∗ e₂)
            ≡⟨ exch e₂ x y e₂ ⟩
              (e₂ • y) ∗ (x • e₂)
            ≡⟨ cong (λ e → (e • y) ∗ (x • e)) id-same ⟩
              (e₁ • y) ∗ (x • e₁)
            ≡⟨ cong (λ z → z ∗ (x • e₁)) (idˡ₁ y) ⟩
              y ∗ (x • e₁)
            ≡⟨ cong (λ z → y ∗ z) (idʳ₁ x) ⟩
              y ∗ x
            ≡⟨ sym (op-same y x) ⟩
              y • x
            ∎

comm₂ : ∀ x y → x ∗ y ≡ y ∗ x
comm₂ x y = begin
              x ∗ y
            ≡⟨ sym (op-same x y) ⟩
              x • y
            ≡⟨ comm₁ x y ⟩
              y • x
            ≡⟨ op-same y x ⟩
              y ∗ x
            ∎
