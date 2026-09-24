# Introduction and reconstruction for hom categories

Normalize the terminal leg of an endpoint-fiber cone. Its two projected
matching equations are precisely the endpoint frames of `hom-expression`.
The full cone comparison gives reconstruction; the pullback beta comparison
then gives introduction with both endpoint equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCoordinates 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section04.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open import SCT.VolumeI.Chapter02.Section01.ExpressionComparisons 𝒯 M ℱ P I using (module Decode)
import SCT.VolumeI.Chapter01.Section06.PairedConeCoordinates 𝒯 as Paired

module Normalize {Γ C : CAT} {x y : Obj-abs C} (h : MAP Γ (Hom C x y)) where
  module H = EndpointFiber x y
  module Coordinates = Paired.Coordinates (ev₀ {C}) ev₁ x y
    using (edge₁; edge₂; edge₁-restrict; edge₂-restrict; encode-edge₁; encode-edge₂; cone-from-coordinates)
  raw = conePre h (pullbackCone endpoints (pair x y))
  homExpression = hom-expression h
  normalized = H.cone (terminate Γ) homExpression
  τ = terminal-iso (H.base ∘ h) (terminate Γ)

  source-equation : (Coordinates.edge₁ normalized ∙ (ev₀ ◁ idIso (H.arrow ∘ h))) =₂
    ((x ◁ τ) ∙ Coordinates.edge₁ raw)
  source-equation = (isoComp-cong (idIso (x ◁ τ))
    (Coordinates.edge₁-restrict h (pullbackCone endpoints (pair x y)))) ⁻¹ ∙
    (isoComp-unitʳ-at (MorphismExpression.source-frame homExpression) ∙
      isoComp-cong (Coordinates.encode-edge₁ (H.arrow ∘ h) (terminate Γ)
        (MorphismExpression.source-frame homExpression) (MorphismExpression.target-frame homExpression))
        (postWhisker-idIso ev₀ (H.arrow ∘ h)))

  target-equation : (Coordinates.edge₂ normalized ∙ (ev₁ ◁ idIso (H.arrow ∘ h))) =₂
    ((y ◁ τ) ∙ Coordinates.edge₂ raw)
  target-equation = (isoComp-cong (idIso (y ◁ τ))
    (Coordinates.edge₂-restrict h (pullbackCone endpoints (pair x y)))) ⁻¹ ∙
    (isoComp-unitʳ-at (MorphismExpression.target-frame homExpression) ∙
      isoComp-cong (Coordinates.encode-edge₂ (H.arrow ∘ h) (terminate Γ)
        (MorphismExpression.source-frame homExpression) (MorphismExpression.target-frame homExpression))
        (postWhisker-idIso ev₁ (H.arrow ∘ h)))

  comparison : ConeIso raw normalized
  comparison = Coordinates.cone-from-coordinates raw normalized (idIso (H.arrow ∘ h)) τ
    source-equation target-equation

hom-η : {Γ C : CAT} {x y : Obj-abs C} (h : MAP Γ (Hom C x y)) →
  hom-intro (hom-expression h) =₁ h
hom-η h = pullback-η h ∙ pullbackLift-cong (coneIso-inverse (Normalize.comparison h))

hom-β : {Γ C : CAT} {x y : Obj-abs C}
  (f : MorphismExpression (const {P = Γ} x) (const y)) →
  ExpressionIso (hom-expression (hom-intro f)) f
hom-β {Γ} {x = x} {y} f = Decode.comparison x y (terminate Γ)
  (hom-expression (hom-intro f)) f cones (terminal-Iso₂ _ _)
  where
  cones = coneIso-compose (EndpointFiber.lift-β x y (terminate Γ) f)
    (coneIso-inverse (Normalize.comparison (hom-intro f)))
```
