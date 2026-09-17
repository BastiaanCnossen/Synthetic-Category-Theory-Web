# The inclusion of a base change

The comparison obtained by nesting and symmetry identifies the whole
induced cone with the direct base-change cone. Its matching compatibility
is used when gluing the coproduct descent square. The two earlier
projection formulas are also retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.BaseChangeInclusion
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.CompositeCones 𝒯
  using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc;
    compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section05.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section05.NestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section05.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P using (pullbackSwap)

module Inclusion {C S E Z : CAT} (i : MAP C S) (h : MAP S Z) (φ : MAP E Z)
  {f : MAP C Z} (α : NatIso f (h ∘ i)) where

  Total = Pullback h φ
  p : MAP Total S
  p = pb₁
  q : MAP Total E
  q = pb₂
  module Change = ChangeLeft α φ
  module N = Nested i h φ
  swapComparison = pullbackSwap i p
  inner = N.insert ∘ Change.forward
  identify = swapComparison ∘ inner
  include = pb₁ ∘ identify

  include-normal : NatIso include (N.inner ∘ Change.forward)
  include-normal = (pbLift-β₂ N.insertionCone ▷ Change.forward) ∙
    (invIso (comp-assoc Change.forward N.insert pb₂) ∙
    ((pbLift-β₁ (coneSwap (pbCone i p)) ▷ inner) ∙ invIso (comp-assoc inner swapComparison pb₁)))

  directCone : Cone h φ (Pullback f φ)
  directCone = compositeCone i h (changeLeft α Change.source)

  opaque
    include-comparison : ConeIso (conePre include (pbCone h φ)) directCone
    include-comparison = coneIso-compose (compositeConeIso i h (pbLift-β (changeLeft α Change.source)))
      (coneIso-compose (compositeCone-pre i h Change.forward N.outerCone)
      (coneIso-compose (coneIso-pre Change.forward (pbLift-β N.innerCone))
      (coneIso-compose (coneIso-inverse (conePre-assoc Change.forward N.inner (pbCone h φ)))
        (cone-action (pbCone h φ) include-normal))))

  include-β₁ : NatIso (p ∘ include) (i ∘ pb₁ {f = f} {φ})
  include-β₁ = (i ◁ pbLift-β₁ (changeLeft α Change.source)) ∙
    (comp-assoc Change.forward N.outerLeft i ∙
    ((pbLift-β₁ N.innerCone ▷ Change.forward) ∙
    (invIso (comp-assoc Change.forward N.inner p) ∙ (p ◁ include-normal))))

  include-β₂ : NatIso (q ∘ include) (pb₂ {f = f} {φ})
  include-β₂ = pbLift-β₂ (changeLeft α Change.source) ∙
    ((pbLift-β₂ N.innerCone ▷ Change.forward) ∙
    (invIso (comp-assoc Change.forward N.inner q) ∙ (q ◁ include-normal)))
```
