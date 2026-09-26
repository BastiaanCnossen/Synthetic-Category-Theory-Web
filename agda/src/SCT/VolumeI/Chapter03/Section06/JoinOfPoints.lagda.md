# The join of two points

For `ex:[0]star[0]is[1]`, the left edge of the defining pushout is an
equivalence. Thus its cylinder map is an equivalence. The specified
height comparison identifies the composite with projection to `[1]`,
proving that the actual height is the required equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinOfPoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-all)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence; degenerate-pullback-converse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J

module Diagram = Span (terminate One) (terminate One)
module Pushout = JoinPushout (mapping-out (terminate One) (terminate One) one-isAn)

abstract
  terminal-map-isEquiv : IsEquiv (terminate One)
  terminal-map-isEquiv = equiv-transport (terminal-iso (id One) (terminate One)) (id-isEquiv One)

  first-isEquiv : IsEquiv (pullback₁ {f = terminate One} {terminate One})
  first-isEquiv = pullback-equivalence (terminate One) (terminate One) terminal-map-isEquiv

  second-isEquiv : IsEquiv (pullback₂ {f = terminate One} {terminate One})
  second-isEquiv = degenerate-pullback-converse terminal-map-isEquiv
    (coneSwap (pullbackCone (terminate One) (terminate One)))
    (pullback-swap (pullbackCone (terminate One) (terminate One))
      (pullbackCone-isPullback (terminate One) (terminate One)))

  cylinder-isEquiv : IsEquiv Pushout.cylinder
  cylinder-isEquiv = pre-tests-all Pushout.cylinder (λ E →
    degenerate-pullback-converse (mapPre-isEquiv Diagram.left (Diagram.left-isEquiv first-isEquiv second-isEquiv))
      (mappingOut Pushout.square E) (Pushout.universal E))

  cylinder-projection-isEquiv : IsEquiv (pr₂ {Diagram.W} {[1]})
  cylinder-projection-isEquiv = equiv-transport
    (comp-unitˡ pr₂ ∙ pair-β₂ (pullback₁ ∘ pr₁) (id [1] ∘ pr₂))
    (equiv-compose (productMap pullback₁ (id [1])) pr₂
      (productMap-isEquiv pullback₁ (id [1]) first-isEquiv (id-isEquiv [1]))
      (oneProduct-pr₂-isEquiv [1]))

comparison : MAP (One ⋆ One) [1]
comparison = pr₂ ∘ height (terminate One) (terminate One)

abstract
  cylinder-comparison : (comparison ∘ Pushout.cylinder) =₁ pr₂
  cylinder-comparison = pair-β₂ (Diagram.base ∘ pr₁) pr₂ ∙
    ((pr₂ ◁ Pushout.height-cylinder) ∙ comp-assoc Pushout.cylinder (height (terminate One) (terminate One)) pr₂)

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-cancel-right Pushout.cylinder comparison cylinder-isEquiv
    (equiv-transport (cylinder-comparison ⁻¹) cylinder-projection-isEquiv)
```
