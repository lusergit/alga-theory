module Algebra.Nat where

  open import Reasoning.Equality
  open import Reasoning.Equational
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  succ a + b = succ (a + b)

  min : ℕ → ℕ → ℕ
  min  zero     b       = zero
  min  a        zero    = zero
  min (succ a) (succ b) = succ (min a b)
  
  lemma-min-idempotence : (n : ℕ) → (min n n) ≡ n
  lemma-min-idempotence zero = refl
  lemma-min-idempotence (succ n) = cong succ (lemma-min-idempotence n)

  lemma-zero-min-ℕ-right : (n : ℕ) → min n zero ≡ zero
  lemma-zero-min-ℕ-right zero = refl
  lemma-zero-min-ℕ-right (succ n) = refl

  lemma-zero-min-ℕ-left : (n : ℕ) → min zero n ≡ zero
  lemma-zero-min-ℕ-left zero = refl
  lemma-zero-min-ℕ-left (succ n) = refl

  lemma-min-commutativity : (n m : ℕ) → min m n ≡ min n m
  lemma-min-commutativity zero m = lemma-zero-min-ℕ-right m
  lemma-min-commutativity (succ n) zero = refl
  lemma-min-commutativity (succ n) (succ m) = cong succ (lemma-min-commutativity n m)

  lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
  lemma-+-zero zero     = refl
  lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
  
  lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
  lemma-+-succ zero     b = refl
  lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)
  
  lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
  lemma-+-commutative zero     b = symm (lemma-+-zero b)
  lemma-+-commutative (succ a) b =
    trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))
  
  lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
  lemma-+-associative zero b c = refl
  lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)
  
  distributivity-min-right : (x y z : ℕ) → (x + min y z) ≡ min (x + y) (x + z)
  distributivity-min-right zero y z = refl
  distributivity-min-right (succ x) y z = cong succ (distributivity-min-right x y z)

  lemma-min-sum : (x y : ℕ) → min x (x + y) ≡ x
  lemma-min-sum zero y = refl
  lemma-min-sum (succ x) y = cong succ (lemma-min-sum x y)

  distributivity-min-left : (x y z : ℕ) → (min x y + z) ≡ min (x + z) (y + z)
  distributivity-min-left x y z = begin
    min x y + z         ≡⟨ lemma-+-commutative (min x y) z ⟩
    z + min x y         ≡⟨ distributivity-min-right z x y ⟩
    min (z + x) (z + y) ≡⟨ cong (min (z + x)) (lemma-+-commutative z y) ⟩
    min (z + x) (y + z) ≡⟨ lemma-min-commutativity (y + z) (z + x) ⟩
    min (y + z) (z + x) ≡⟨ cong (min (y + z)) (lemma-+-commutative z x) ⟩
    min (y + z) (x + z) ≡⟨ lemma-min-commutativity (x + z) (y + z) ⟩
    min (x + z) (y + z) ∎

  lemma-min-associative : (x y z : ℕ) → min x (min y z) ≡ min (min x y) z
  lemma-min-associative zero y z = refl
  lemma-min-associative (succ x) zero z = refl
  lemma-min-associative (succ x) (succ y) zero = refl
  lemma-min-associative (succ x) (succ y) (succ z) = cong succ (lemma-min-associative x y z)

  lemma-sum-assoc : (x y z : ℕ) → (x + succ (y + z)) ≡ succ ((x + y) + z)
  lemma-sum-assoc zero y z = refl
  lemma-sum-assoc (succ x) y z = begin
    succ (x + succ (y + z)) ≡⟨ cong succ (lemma-+-succ x (y + z)) ⟩
    succ (succ (x + (y + z))) ≡⟨ cong succ (cong succ (lemma-+-associative x y z)) ⟩
    succ (succ ((x + y) + z)) ∎
    
