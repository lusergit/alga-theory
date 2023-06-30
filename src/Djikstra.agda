{-# OPTIONS --allow-unsolved-metas #-}
  
module Djikstra
  (A : Set)
  where

  open import Algebra.LabelledGraph
  open import Algebra.Graph
  import Algebra.LabelledGraph as LG
  import Algebra.Graph as G
  open import Algebra.Nat
  open import Algebra.Dioid.ShortestDistance
  open import Algebra.Dioid.ShortestDistance.Theorems
  
  to-graph : ∀ {A} → LabelledGraph shortest-distance-dioid A → Graph A
  to-graph ε = G.ε
  to-graph (v x) = G.v x
  to-graph (l [ Distance x ]> m) = to-graph l G.* to-graph m
  to-graph (l [ Unreachable ]> m) = to-graph l G.+ to-graph m

  from-graph : ∀ {A} → Graph A → LabelledGraph shortest-distance-dioid A
  from-graph ε = ε
  from-graph (v x) = (v x)
  from-graph (p Graph.+ q) = (from-graph p) [ Unreachable ]> (from-graph q)
  from-graph (p Graph.* q) = (from-graph p) [ (Distance (succ zero)) ]> (from-graph q)

  min-dist : ∀ {A} → LabelledGraph shortest-distance-dioid A → LabelledGraph shortest-distance-dioid A
  min-dist (g [ Distance x ]> h) with g LG.⊆ h
  ... | p = {!!}
  min-dist (g [ Unreachable ]> h) = {!!}
  min-dist x = x
  
