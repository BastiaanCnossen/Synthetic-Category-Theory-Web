# Recovering a triangle comparison after restriction

A comparison between restricted relative functors determines the
restriction of their base-triangle compatibility. Cancel the common
source triangle and the associator. This will let the two coproduct
inclusions jointly detect comparisons over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PrecompositionCompatibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; move-square)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module Restriction {A B C S : CAT} {p : MAP A S} {q : MAP B S} {r : MAP C S}
  (i : FunctorOver p q) (u v : FunctorOver q r)
  (α : FunctorLift.lift u =₁ FunctorLift.lift v)
  (compatible : (FunctorLift.comparison (compose-over v i) ∙
    (r ◁ (α ▷ FunctorLift.lift i))) =₂ FunctorLift.comparison (compose-over u i)) where
  j = FunctorLift.lift i
  source-assoc = comp-assoc j (FunctorLift.lift u) r
  target-assoc = comp-assoc j (FunctorLift.lift v) r
  s = FunctorLift.comparison u ▷ j
  t = FunctorLift.comparison v ▷ j
  d = (r ◁ α) ▷ j
  e = r ◁ (α ▷ j)
  κ = FunctorLift.comparison i
  abstract
    moved : (target-assoc ⁻¹ ∙ e) =₂ (d ∙ source-assoc ⁻¹)
    moved = move-square target-assoc d e source-assoc (whisker-mixed-at α j r)
    stripped : ((t ∙ target-assoc ⁻¹) ∙ e) =₂ (s ∙ source-assoc ⁻¹)
    stripped = cancel-left-reflect κ
      (compatible ∙ (isoComp-assoc-at κ (t ∙ target-assoc ⁻¹) e) ⁻¹)
    normalized : ((t ∙ d) ∙ source-assoc ⁻¹) =₂ (s ∙ source-assoc ⁻¹)
    normalized = stripped ∙
      ((isoComp-assoc-at t (target-assoc ⁻¹) e) ⁻¹ ∙
        (isoComp-cong (idIso t) (moved ⁻¹) ∙ isoComp-assoc-at t d (source-assoc ⁻¹)))
    comparison : ((FunctorLift.comparison v ∙ (r ◁ α)) ▷ j) =₂
      (FunctorLift.comparison u ▷ j)
    comparison = cancel-right-reflect (source-assoc ⁻¹) normalized ∙
      preWhisker-isoComp-at (FunctorLift.comparison v) (r ◁ α) j
```
