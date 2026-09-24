# The inclusion of a base change

The comparison obtained by nesting and symmetry identifies the whole
induced cone with the direct base-change cone. Its matching compatibility
is used when gluing the coproduct descent square. The two earlier
projection formulas are also retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.BaseChangeInclusion
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.CompositeCones 𝒯
  using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc;
    compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullbackSwap)

module Inclusion {C S E Z : CAT} (i : MAP C S) (h : MAP S Z) (φ : MAP E Z)
  {f : MAP C Z} (α : f =₁ (h ∘ i)) where

  Total = Pullback h φ
  p : MAP Total S
  p = pullback₁
  q : MAP Total E
  q = pullback₂
  module Change = ChangeLeft α φ
  module N = Nested i h φ
  swapComparison = pullbackSwap i p
  inner = N.insert ∘ Change.forward
  identify = swapComparison ∘ inner
  include = pullback₁ ∘ identify

  include-normal : include =₁ (N.inner ∘ Change.forward)
  include-normal = (pullbackLift-β₂ N.insertionCone ▷ Change.forward) ∙
    ((comp-assoc Change.forward N.insert pullback₂) ⁻¹ ∙
    ((pullbackLift-β₁ (coneSwap (pullbackCone i p)) ▷ inner) ∙ (comp-assoc inner swapComparison pullback₁) ⁻¹))

  directCone : Cone h φ (Pullback f φ)
  directCone = compositeCone i h (changeLeft α Change.source)

  opaque
    include-comparison : ConeIso (conePre include (pullbackCone h φ)) directCone
    include-comparison = coneIso-compose (compositeConeIso i h (pullbackLift-β (changeLeft α Change.source)))
      (coneIso-compose (compositeCone-pre i h Change.forward N.outerCone)
      (coneIso-compose (coneIso-pre Change.forward (pullbackLift-β N.innerCone))
      (coneIso-compose (coneIso-inverse (conePre-assoc Change.forward N.inner (pullbackCone h φ)))
        (cone-action (pullbackCone h φ) include-normal))))

  include-β₁ : (p ∘ include) =₁ (i ∘ pullback₁ {f = f} {φ})
  include-β₁ = (i ◁ pullbackLift-β₁ (changeLeft α Change.source)) ∙
    (comp-assoc Change.forward N.outerLeft i ∙
    ((pullbackLift-β₁ N.innerCone ▷ Change.forward) ∙
    ((comp-assoc Change.forward N.inner p) ⁻¹ ∙ (p ◁ include-normal))))

  include-β₂ : (q ∘ include) =₁ (pullback₂ {f = f} {φ})
  include-β₂ = pullbackLift-β₂ (changeLeft α Change.source) ∙
    ((pullbackLift-β₂ N.innerCone ▷ Change.forward) ∙
    ((comp-assoc Change.forward N.inner q) ⁻¹ ∙ (q ◁ include-normal)))
```
