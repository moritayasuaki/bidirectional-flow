
module multi-category where
  nary-prod : Set → Nat.ℕ → Set
  nary-prod C Nat.zero = Data.Unit.⊤
    where import Data.Unit
  nary-prod C (Nat.suc n) = C × nary-prod C n

  nary-hom : Set → Nat.ℕ → Set
  nary-hom C n = nary-prod C n → C

  nary-ihom : Set → Set
  nary-ihom C = ∀ n → nary-hom C n

  fsum : ∀{n : Nat.ℕ} → Vec.Vec Nat.ℕ n → Nat.ℕ
  fsum [] = Nat.zero
  fsum (x ∷ k) = x Nat.+ fsum k

  nary-comp : (C : Set) → (n : Nat.ℕ) → (k : Vec.Vec Nat.ℕ n) → ((i : Fin n) → nary-hom C (lookup k i)) → nary-hom C (fsum k)
  nary-comp C n k x x₁ = {!!}
