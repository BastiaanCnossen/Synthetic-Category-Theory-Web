# Reflecting a higher comparison over the base

To compare two relative identifications into a pullback, compare their
induced cones and verify the triangle equation using the specified
second-leg comparison. Higher pullback lifting then supplies the
underlying identification with precisely that second-projection image.
Substitution into the triangle equation gives the full native comparison.

The input includes the matching witness of the higher cone comparison.
Agreement of its two legs alone would not suffice.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherReflection 𝒯 P
  using () renaming (module Reflection to ConeReflection)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherLifting 𝒯 P using (module Lifting)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂)

module Reflection {X C D S : CAT} {g : MAP C S} {p : MAP D S} {r : MAP X D}
  (u v : FunctorOver r (pullback₂ {f = g} {p}))
  {Φ Ψ : FunctorOverIso u v}
  (Ξ : ConeIso₂
    (ConeReflection.induced-cone (FunctorLift.lift u) (FunctorLift.lift v) (FunctorOverIso.underlying Φ))
    (ConeReflection.induced-cone (FunctorLift.lift u) (FunctorLift.lift v) (FunctorOverIso.underlying Ψ))) where

  module Lifted = Lifting (FunctorLift.lift u) (FunctorLift.lift v)
    {α = FunctorOverIso.underlying Φ} {β = FunctorOverIso.underlying Ψ} Ξ
    using (lift; left-image; right-image)

  -- This is the remaining triangle equation after both cone legs and
  -- their matching have been supplied. It is a premise, not an axiom.
  Triangle : Set m
  Triangle = (FunctorOverIso.compatible Ψ ∙
    isoComp-cong (idIso (FunctorLift.comparison v)) (ConeIso₂.rightId Ξ)) =₃
      FunctorOverIso.compatible Φ

  opaque
    boundary-image :
      isoComp-cong (idIso (FunctorLift.comparison v))
        (postWhisker (pullback₂ {f = g} {p}) ◁ Lifted.lift) =₃
      isoComp-cong (idIso (FunctorLift.comparison v)) (ConeIso₂.rightId Ξ)
    boundary-image = postWhisker isoComp ◁
      pair-cong-Iso₂ (idIso (idIso (FunctorLift.comparison v))) Lifted.right-image

    comparison : Triangle → FunctorOverIso₂ Φ Ψ
    comparison triangle = record
      { underlying = Lifted.lift
      ; compatible = triangle ∙
          isoComp-cong (idIso (FunctorOverIso.compatible Ψ)) boundary-image }

    left-image : (triangle : Triangle) →
      (postWhisker (pullback₁ {f = g} {p}) ◁ FunctorOverIso₂.underlying (comparison triangle)) =₃
        ConeIso₂.leftId Ξ
    left-image triangle = Lifted.left-image

    right-image : (triangle : Triangle) →
      (postWhisker (pullback₂ {f = g} {p}) ◁ FunctorOverIso₂.underlying (comparison triangle)) =₃
        ConeIso₂.rightId Ξ
    right-image triangle = Lifted.right-image
```
