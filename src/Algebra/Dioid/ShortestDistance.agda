module Algebra.Dioid.ShortestDistance where

  open import Algebra.Nat
  open import Reasoning.Equality
  open import Reasoning.Equational

  data ShortestDistance : Set where
    Distance : ℕ → ShortestDistance
    Unreachable :  ShortestDistance

  _∨_ : ShortestDistance → ShortestDistance → ShortestDistance
  Distance x ∨ Distance y = Distance (min x y)
  a ∨ Unreachable = a
  Unreachable ∨ b = b

  _∧_ : ShortestDistance → ShortestDistance → ShortestDistance
  Distance x ∧ Distance y = Distance (x + y)
  a ∧ Unreachable = Unreachable
  Unreachable ∧ b = Unreachable

  lemma-n-implies-distance : {x y : ℕ} → x ≡ y → Distance x ≡ Distance y
  lemma-n-implies-distance refl = refl
  lemma-n-implies-distance (symm p) = symm (lemma-n-implies-distance p)
  lemma-n-implies-distance (trans p q) =
    trans (lemma-n-implies-distance p) (lemma-n-implies-distance q)
