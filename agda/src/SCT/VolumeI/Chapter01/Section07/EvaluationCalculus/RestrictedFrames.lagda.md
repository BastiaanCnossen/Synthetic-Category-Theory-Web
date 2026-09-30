# Uncurrying a restricted frame

A specified identification after restriction induces a frame after
uncurrying. The following identity compares its restriction formula
with the direct formula obtained from evaluation and product substitution.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
module PS = Projection 𝒯

module At {Γ Δ X C : CAT} (H : MAP Γ (Fun X C)) (i : MAP Δ Γ)
  {f : MAP Δ (Fun X C)} (p : (H ∘ i) =₁ f) where
  s : MAP (Δ × X) (Γ × X)
  s = productMap i (id X)
  K : MAP (Γ × X) (Fun X C × X)
  K = productMap H (id X)
  χ : (K ∘ s) =₁ productMap (H ∘ i) (id X)
  χ = slice-comparison H i
  δ : productMap (H ∘ i) (id X) =₁ productMap f (id X)
  δ = productMap-cong p (idIso (id X))
  A : ((funEval ∘ K) ∘ s) =₁ (funEval ∘ (K ∘ s))
  A = comp-assoc s K funEval

  abstract
    inverse-image : (funEval ◁ χ ⁻¹) ⁻¹ =₂ (funEval ◁ χ)
    inverse-image = (postWhisker funEval ◁ inverse-inverse χ) ∙
      (PS.post-inverse funEval (χ ⁻¹)) ⁻¹

    inverse-restriction : (funUncurry-restrict H i) ⁻¹ =₂ ((funEval ◁ χ) ∙ A)
    inverse-restriction = isoComp-cong inverse-image (inverse-inverse A) ∙
      inverse-composite (A ⁻¹) (funEval ◁ χ ⁻¹)

    comparison : (funUncurryIso p ∙ (funUncurry-restrict H i) ⁻¹) =₂
      ((funEval ◁ (δ ∙ χ)) ∙ A)
    comparison = isoComp-cong ((postWhisker-isoComp-at funEval δ χ) ⁻¹) (idIso A) ∙
      (isoComp-assoc-at (funEval ◁ δ) (funEval ◁ χ) A) ⁻¹ ∙
      isoComp-cong (funUncurryIso-at p) inverse-restriction
```
