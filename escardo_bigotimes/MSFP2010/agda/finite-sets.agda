module finite-sets where

open import Equality
open import Logic
open import Induction

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)


embed : {n : ℕ} → Fin n → Fin (succ n)
embed {O} ()
embed {succ n} (fzero {.n}) = fzero {succ n}
embed {succ n} (fsucc {.n} i) = fsucc(embed {n} i)

nat : {n : ℕ} → Fin n → ℕ
nat {O} ()
nat {succ n} fzero = O
nat {succ n} (fsucc i) = succ(nat {n} i)

-- nat-embed-lemma : ∀(n : ℕ) → ∀(i : Fin n) → nat {n} i ≡ nat {succ n} (embed {n} i)
nat-embed-lemma : ∀(n : ℕ) → ∀(i : Fin n) → nat i ≡ nat(embed i)
nat-embed-lemma O ()
nat-embed-lemma (succ n) fzero = reflexivity
nat-embed-lemma (succ n) (fsucc i) = lemma
  where induction-hypothesis : nat {n} i ≡ nat {succ n} (embed {n} i)
        induction-hypothesis = nat-embed-lemma n i

        lemma₀ : nat {succ n} (fsucc i) ≡ succ(nat {n} i)
        lemma₀ = reflexivity

        lemma₁ : succ(nat {n} i) ≡ succ(nat{succ n} (embed {n} i))
        lemma₁ = compositionality succ induction-hypothesis

        lemma₂ : nat {succ n} (fsucc i) ≡ succ(nat{succ n} (embed {n} i))
        lemma₂ = transitivity lemma₀ lemma₁

        lemma₃ : succ(nat{succ n} (embed {n} i)) ≡ nat{succ(succ n)} (embed {succ n} (fsucc i))
        lemma₃ = reflexivity

        lemma : nat {succ n} (fsucc i) ≡ nat{succ(succ n)} (embed {succ n} (fsucc i))
        lemma = transitivity lemma₂ lemma₃

nat-embed-lemma-quick-obscure-proof : ∀(n : ℕ) → ∀(i : Fin n) → nat i ≡ nat(embed i)
nat-embed-lemma-quick-obscure-proof O ()
nat-embed-lemma-quick-obscure-proof (succ n) fzero = reflexivity
nat-embed-lemma-quick-obscure-proof (succ n) (fsucc i) = 
 transitivity (transitivity reflexivity (compositionality succ (nat-embed-lemma-quick-obscure-proof n i))) reflexivity


tan : (n : ℕ) → Fin(succ n)
tan O = fzero
tan (succ n) = fsucc(tan n)

nat∘tan-is-identity : (∀(n : ℕ) → nat(tan n) ≡ n)
nat∘tan-is-identity O = reflexivity
nat∘tan-is-identity (succ n) = lemma
 where induction_hypothesis : nat(tan n) ≡ n
       induction_hypothesis  = nat∘tan-is-identity n

       lemma₀ :  nat(tan(succ n)) ≡ nat(fsucc(tan n))
       lemma₀ = reflexivity

       lemma₁ : nat(fsucc(tan n)) ≡ succ(nat(tan n))
       lemma₁ = reflexivity

       lemma₂ : succ(nat(tan n)) ≡ succ n
       lemma₂ = compositionality succ induction_hypothesis

       lemma : nat(tan(succ n)) ≡ succ n
       lemma = transitivity (transitivity lemma₀ lemma₁) lemma₂

nat∘tan-is-identity-quick-obscure-proof : (∀(n : ℕ) → nat(tan n) ≡ n)
nat∘tan-is-identity-quick-obscure-proof =  
 induction reflexivity (λ k r → transitivity (transitivity reflexivity reflexivity) (compositionality succ r))


FinSeq : (X : ℕ → Set) → (n : ℕ) → Set 
FinSeq X n = (i : Fin n) → X(nat i)


remove-last : {X : ℕ → Set} → {n : ℕ} → FinSeq X (succ n) → FinSeq X n
remove-last {X} {n} s i = coersion(s(embed i))
 where coersion : X(nat(embed i)) → X(nat i) 
       coersion = set-compositionality X (symmetry (nat-embed-lemma n i))

append : {A : ℕ → Ω} → {k : ℕ} → FinSeq A k → A k →  FinSeq A (succ k)
append {A} {O} s a fzero = a
append {A} {O} s a (fsucc ())
append {A} {succ k} s a fzero = s fzero
append {A} {succ k} s a (fsucc j) = append {λ n → A(succ n)} {k} (λ i → s(fsucc i)) a j

ppend : {k : ℕ} → {A : Fin(succ k) → Ω} → (∀(i : Fin k) → A(embed i)) → A(tan k) →  ∀(j : Fin(succ k)) → A j
ppend {O} {A} s a fzero = a
ppend {O} {A} s a (fsucc ())
ppend {succ k} {A} s a fzero = s fzero
ppend {succ k} {A} s a (fsucc j) = ppend {k} {λ n → A(fsucc n)} (λ i → s(fsucc i)) a j
