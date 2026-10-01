# Cylinder and arrow presentations over the same parameter

Flattening a functor from the interval into a functor category gives a
functor on the interval cylinder. The endpoint comparisons induce an
equivalence of the corresponding pullbacks, with its parameter projection
comparison retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.DiagramInterchange as Interchange
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Cospans

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CylinderEndpointComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (ConeIso)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)

module At (Y C : CAT) {B : CAT} (u v : MAP B (Fun Y C)) where
  module Flatten = Interchange.Flatten 𝒯 M ℱ [1] Y C using (module Exp; module Outer)
  module Source = EndpointFiber u v using (category; base)
  boundary = pair u v
  cylinder-endpoints : MAP (Fun ([1] × Y) C) (Fun Y C × Fun Y C)
  cylinder-endpoints = pair (funPre (pair (const zero) (id Y))) (funPre (pair (const one) (id Y)))
  category = Pullback cylinder-endpoints boundary
  projection : MAP category B
  projection = pullback₂

  boundary-frame : (cylinder-endpoints ∘ Flatten.Exp.forward) =₁ endpoints
  boundary-frame = pair-cong (Flatten.Outer.boundary zero) (Flatten.Outer.boundary one) ∙
    pair-pre (funPre (pair (const zero) (id Y))) (funPre (pair (const one) (id Y))) Flatten.Exp.forward

  change : CospanMap endpoints boundary cylinder-endpoints boundary
  change = record { left = Flatten.Exp.forward ; right = id B ; base = id (Fun Y C × Fun Y C)
    ; leftSquare = (comp-unitˡ endpoints) ⁻¹ ∙ boundary-frame
    ; rightSquare = (comp-unitˡ boundary) ⁻¹ ∙ comp-unitʳ boundary }
  module Change = CospanMap change using (pullbackMap; pullbackMap-β)
  module Equivalence = Cospans.CospanEquivalence 𝒯 P change Flatten.Exp.forward-isEquiv
    (id-isEquiv B) (id-isEquiv (Fun Y C × Fun Y C)) using (pullbackMap-isEquiv)

  abstract
    forward : MAP Source.category category
    forward = Change.pullbackMap

    forward-isEquiv : IsEquiv forward
    forward-isEquiv = Equivalence.pullbackMap-isEquiv

    projection-comparison : (projection ∘ forward) =₁ Source.base
    projection-comparison = comp-unitˡ Source.base ∙ ConeIso.rightIso Change.pullbackMap-β
```
