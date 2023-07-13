module Algebra.Dioid.ShortestDistance.Theorems where

  open import Algebra.Dioid
  open import Algebra.Nat
  open import Algebra.Dioid.ShortestDistance
  open import Reasoning.Equality
  open import Reasoning.Equational

  ∨-left-congruence : ∀ {b c d : ShortestDistance} → b ≡ c → (b ∨ d) ≡ (c ∨ d)
  ∨-left-congruence {b} {c} {d} p = begin
    b ∨ d ≡⟨ cong (λ x → x ∨ d) p ⟩
    c ∨ d ∎
    
  ∨-right-congruence : ∀ {b c d : ShortestDistance} → c ≡ d → (b ∨ c) ≡ (b ∨ d)
  ∨-right-congruence {b} {c} {d} p = begin
    b ∨ c ≡⟨ cong (_∨_ b) p ⟩
    b ∨ d ∎
    
  ∧-left-congruence : ∀ {b c d : ShortestDistance} → b ≡ c → (b ∧ d) ≡ (c ∧ d)
  ∧-left-congruence {b} {c} {d} p = begin
    b ∧ d ≡⟨ cong (λ x → x ∧ d) p ⟩
    c ∧ d ∎
    
  ∧-right-congruence : ∀ {b c d : ShortestDistance} → c ≡ d → (b ∧ c) ≡ (b ∧ d)
  ∧-right-congruence {b} {c} {d} p = begin
    b ∧ c ≡⟨ cong (_∧_ b) p ⟩
    b ∧ d ∎
    
  ∨-idempotence : ∀ {b : ShortestDistance} → (b ∨ b) ≡ b
  ∨-idempotence {Distance x}  = lemma-n-implies-distance (lemma-min-idempotence x)
  ∨-idempotence {Unreachable} = refl

  ∨-unreach-identity : ∀ {b : ShortestDistance} → (b ∨ Unreachable) ≡ b
  ∨-unreach-identity {Distance x}  = refl
  ∨-unreach-identity {Unreachable} = refl

  ∨-unreach-identity-left : ∀ {b : ShortestDistance} → (Unreachable ∨ b) ≡ b
  ∨-unreach-identity-left {Distance x}  = refl
  ∨-unreach-identity-left {Unreachable} = refl
    
  ∨-commutativity : ∀ {r s : ShortestDistance} → (r ∨ s) ≡ (s ∨ r)
  ∨-commutativity {Distance x} {Distance y} = lemma-n-implies-distance (lemma-min-commutativity y x)
  ∨-commutativity {Distance x} {Unreachable} = refl
  ∨-commutativity {Unreachable} {s} = begin
    Unreachable ∨ s ≡⟨ ∨-unreach-identity-left ⟩
    s               ≡⟨ symm ∨-unreach-identity ⟩
    s ∨ Unreachable ∎

  ∨-associativity : ∀ {b c d : ShortestDistance} → (b ∨ (c ∨ d)) ≡ ((b ∨ c) ∨ d)
  ∨-associativity {Distance x} {Distance y} {Distance z}   = lemma-n-implies-distance (lemma-min-associative x y z)
  ∨-associativity {Distance x} {Unreachable} {Distance z}  = refl
  ∨-associativity {Unreachable} {Distance y} {Distance z}  = refl
  ∨-associativity {Unreachable} {Unreachable} {Distance z} = refl
  ∨-associativity {b} {c} {Unreachable} = begin
    b ∨ (c ∨ Unreachable) ≡⟨ cong (_∨_ b) ∨-unreach-identity ⟩
    b ∨ c                 ≡⟨ symm ∨-unreach-identity ⟩
    (b ∨ c) ∨ Unreachable ∎

  ∧-left-unreach : ∀ {b : ShortestDistance} → (Unreachable ∧ b) ≡ Unreachable
  ∧-left-unreach {Distance x} = refl
  ∧-left-unreach {Unreachable} = refl
  
  ∧-right-unreach : ∀ {b : ShortestDistance} → (b ∧ Unreachable) ≡ Unreachable
  ∧-right-unreach {Distance x} = refl
  ∧-right-unreach {Unreachable} = refl
  
  ∧-associativity : ∀ {b c d : ShortestDistance} → (b ∧ (c ∧ d)) ≡ ((b ∧ c) ∧ d)
  ∧-associativity {Distance x} {Distance y} {Distance z} = lemma-n-implies-distance (lemma-+-associative x y z)
  ∧-associativity {Unreachable} {c} {d} = begin
    Unreachable ∧ (c ∧ d) ≡⟨ ∧-left-unreach ⟩
    Unreachable           ≡⟨ symm ∧-left-unreach ⟩
    Unreachable ∧ d       ≡⟨ cong (λ x → (x ∧ d)) (symm ∧-left-unreach) ⟩
    (Unreachable ∧ c) ∧ d ∎
  ∧-associativity {b} {Unreachable} {d} = begin
    b ∧ (Unreachable ∧ d)  ≡⟨ cong (_∧_ b) ∧-left-unreach ⟩
    b ∧ Unreachable        ≡⟨ ∧-right-unreach ⟩
    Unreachable            ≡⟨ symm ∧-left-unreach ⟩ 
    Unreachable ∧ d        ≡⟨ cong (λ x → x ∧ d) (symm ∧-right-unreach) ⟩
    (b ∧ Unreachable) ∧ d ∎
  ∧-associativity {b} {c} {Unreachable} = begin
    b ∧ (c ∧ Unreachable) ≡⟨ cong (_∧_ b) ∧-right-unreach ⟩
    b ∧ Unreachable       ≡⟨ ∧-right-unreach ⟩
    Unreachable           ≡⟨ symm ∧-right-unreach ⟩
    (b ∧ c) ∧ Unreachable ∎
    
  ∧-left-dist-zero : ∀ {b : ShortestDistance} → (Distance zero ∧ b) ≡ b
  ∧-left-dist-zero {Distance x}  = refl
  ∧-left-dist-zero {Unreachable} = refl
    
  ∧-right-dist-zero : ∀ {b : ShortestDistance} → (b ∧ Distance zero) ≡ b
  ∧-right-dist-zero {Distance x}  = lemma-n-implies-distance (lemma-+-zero x)
  ∧-right-dist-zero {Unreachable} = refl
    
  left-distributivity : ∀ {b c d : ShortestDistance} → (b ∧ (c ∨ d)) ≡ ((b ∧ c) ∨ (b ∧ d))
  left-distributivity {Distance x} {Distance y} {Distance z}    = lemma-n-implies-distance (distributivity-min-right x y z)
  left-distributivity {Distance x} {Distance y} {Unreachable}   = refl
  left-distributivity {Distance x} {Unreachable} {Distance z}   = refl
  left-distributivity {Distance x} {Unreachable} {Unreachable}  = refl
  left-distributivity {Unreachable} {Distance y} {Distance z}   = refl
  left-distributivity {Unreachable} {Distance y} {Unreachable}  = refl
  left-distributivity {Unreachable} {Unreachable} {Distance z}  = refl
  left-distributivity {Unreachable} {Unreachable} {Unreachable} = refl
    
  right-distributivity : ∀ {b c d : ShortestDistance} → ((b ∨ c) ∧ d) ≡ ((b ∧ d) ∨ (c ∧ d))
  right-distributivity {Distance x} {Distance y} {Distance z} = lemma-n-implies-distance (distributivity-min-left x y z)
  right-distributivity {Unreachable} {c} {d} = begin
    (Unreachable ∨ c) ∧ d       ≡⟨ cong (λ x → x ∧ d) ∨-unreach-identity-left ⟩
    c ∧ d                       ≡⟨ symm ∨-unreach-identity-left ⟩
    Unreachable ∨ (c ∧ d)       ≡⟨ cong (λ x → x ∨ (c ∧ d)) (symm (∧-left-unreach {d})) ⟩
    (Unreachable ∧ d) ∨ (c ∧ d) ∎
  right-distributivity {b} {Unreachable} {d} = begin
    (b ∨ Unreachable) ∧ d       ≡⟨ cong (λ x → x ∧ d) ∨-unreach-identity ⟩
    b ∧ d                       ≡⟨ symm ∨-unreach-identity ⟩
    (b ∧ d) ∨ Unreachable       ≡⟨ cong (_∨_ (b ∧ d)) (symm (∧-left-unreach {d})) ⟩
    (b ∧ d) ∨ (Unreachable ∧ d) ∎
  right-distributivity {b} {c} {Unreachable} = begin
    (b ∨ c) ∧ Unreachable                 ≡⟨ ∧-right-unreach ⟩
    Unreachable ∨ Unreachable             ≡⟨ cong (_∨_ Unreachable) (symm (∧-right-unreach {c})) ⟩
    Unreachable ∨ (c ∧ Unreachable)       ≡⟨ cong (λ x → x ∨ (c ∧ Unreachable)) (symm (∧-right-unreach {b})) ⟩
    (b ∧ Unreachable) ∨ (c ∧ Unreachable) ∎

  shortest-distance-dioid : Dioid ShortestDistance _≡_
  shortest-distance-dioid = record
    { zero = Unreachable
    ; one  = Distance zero
    ; _+_  = _∨_
    ; _*_  = _∧_
    ; reflexivity  = refl
    ; symmetry     = symm
    ; transitivity = trans
  
    ; +left-congruence  = ∨-left-congruence
    ; *left-congruence  = ∧-left-congruence
    ; *right-congruence = ∧-right-congruence

    ; +idempotence   = ∨-idempotence
    ; +commutativity = λ {x} {y} → ∨-commutativity {x} {y}
    ; +associativity = λ {x} {y} {z} → ∨-associativity {x} {y} {z}
    ; +zero-identity = ∨-unreach-identity
  
    ; *associativity  = ∧-associativity
    ; *left-zero      = ∧-left-unreach
    ; *right-zero     = ∧-right-unreach
    ; *left-identity  = ∧-left-dist-zero
    ; *right-identity = ∧-right-dist-zero
  
    ; left-distributivity  = left-distributivity
    ; right-distributivity = λ {x} {y} {z} → right-distributivity {x} {y} {z}
    }
