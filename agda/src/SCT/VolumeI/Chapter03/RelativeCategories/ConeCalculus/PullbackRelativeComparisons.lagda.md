# Relative comparisons and restricted pullback cones

A relative comparison with the left projection of a map into a pullback
is a comparison of whole cones. Its right leg is the inverse of the
specified base triangle. This converts the native relative-functor
calculus into the endpoint comparisons used for interval lifting.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackRelativeComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module At {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (q : MAP Γ D) (h : FunctorOver q (Cone.right t)) where
  left-projection : FunctorOver (g ∘ Cone.right t) f
  left-projection = record { lift = Cone.left t ; comparison = Cone.match t }
  projected = compose-over left-projection (postbase g h)
  r = FunctorLift.lift h
  ρ = FunctorLift.comparison h
  projection-assoc = comp-assoc r (Cone.right t) g
  b = (Cone.match t ▷ r) ∙ (comp-assoc r (Cone.left t) f) ⁻¹
  matching = Cone.match (conePre r t)

  abstract
    projected-frame : FunctorLift.comparison projected =₂ ((g ◁ ρ) ∙ matching)
    projected-frame = isoComp-assoc-at (g ◁ ρ) projection-assoc b

  module WithComparison (w : FunctorOver (g ∘ q) f) (Φ : FunctorOverIso w projected) where
    source : Cone f g Γ
    source = record { left = FunctorLift.lift w ; right = q ; match = FunctorLift.comparison w }
    γ = FunctorOverIso.underlying Φ
    τ = FunctorLift.comparison w
    edge = f ◁ γ

    abstract
      compatible : (matching ∙ edge) =₂ ((g ◁ ρ ⁻¹) ∙ τ)
      compatible = isoComp-cong (post-inverse g ρ ⁻¹) (idIso τ) ∙
        (isoComp-cong (idIso ((g ◁ ρ) ⁻¹))
          (FunctorOverIso.compatible Φ ∙
            isoComp-cong (projected-frame ⁻¹) (idIso edge) ∙
              isoComp-assoc-at (g ◁ ρ) matching edge ⁻¹) ∙
          (cancel-left (g ◁ ρ) (matching ∙ edge)) ⁻¹)

    value : ConeIso source (conePre r t)
    value = record { leftIso = γ ; rightIso = ρ ⁻¹ ; compatible = compatible }
```
