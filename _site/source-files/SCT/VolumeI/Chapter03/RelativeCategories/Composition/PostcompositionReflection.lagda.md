# Recovering a triangle from a prescribed projected comparison

Suppose a comparison is known after postcomposition by a triangle.
Any lift of its underlying identification, with the prescribed image,
is automatically compatible with the original triangles. This cancels
the invertible base comparison; the postcomposing functor need not be
an embedding.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering using (substitution-square-projection)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module Recover {X C D B : CAT} {f : MAP X B} {g : MAP C B} {h : MAP D B}
  (w : FunctorOver g h) {u v : FunctorOver f g}
  (Φ : FunctorOverIso (compose-over w u) (compose-over w v))
  (δ : FunctorLift.lift u =₁ FunctorLift.lift v)
  (image : (FunctorLift.lift w ◁ δ) =₂ FunctorOverIso.underlying Φ) where
  z = FunctorLift.lift w
  β = FunctorLift.comparison w
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  au = (β ▷ FunctorLift.lift u) ∙ (comp-assoc (FunctorLift.lift u) z h) ⁻¹
  av = (β ▷ FunctorLift.lift v) ∙ (comp-assoc (FunctorLift.lift v) z h) ⁻¹

  abstract
    comparison : FunctorOverIso u v
    comparison = record { underlying = δ
      ; compatible = cancel-right-reflect au
          (FunctorOverIso.compatible Φ ∙
            (isoComp-cong (idIso (θv ∙ av)) (postWhisker h ◁ image) ∙
              ((isoComp-assoc-at θv av (h ◁ (z ◁ δ))) ⁻¹ ∙
                (isoComp-cong (idIso θv) ((substitution-square-projection h z g β δ) ⁻¹) ∙
                  isoComp-assoc-at θv (g ◁ δ) au)))) }
    underlying-image : FunctorOverIso.underlying comparison =₂ δ
    underlying-image = idIso δ
```
