data _⊎_ (X Y : Set) : Set where
  left  : X → X ⊎ Y
  right : Y → X ⊎ Y

open import Reasoning.Equality as EQ

module Impl
  (A : Set)
  (_≤_ : A → A → Set)
  (cmp? : (a b : A) → (a ≤ b) ⊎ (b ≤ a))
  where

  open import Algebra.LabelledGraph
  open import Algebra.LabelledGraph.Reasoning
  open import Algebra.Dioid
  open import Algebra.Graph using (Graph)
  import Algebra.Graph as Graph
  import Algebra.Graph.Reasoning as Graph
  import Algebra.Graph.Theorems as Graph
  import Algebra.Dioid.Bool as Bool
  import Algebra.Dioid.Bool.Theorems as Bool
  import Algebra.Dioid.ShortestDistance as SD using (ShortestDistance; Unreachable; Distance)
  import Algebra.Dioid.ShortestDistance.Theorems as SD

  djikstra : LabelledGraph SD.shortest-distance-dioid A → (a b : A) → SD.ShortestDistance
  djikstra ε x y = SD.Unreachable
  djikstra (v z) x y = {!!}
  djikstra (g [ x₁ ]> g₁) x y = {!!}
