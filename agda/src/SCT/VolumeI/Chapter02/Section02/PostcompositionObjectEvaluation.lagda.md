# Postcomposition and an identification of evaluation objects

Evaluation after postcomposition is natural in the object at which a
family is evaluated. Both sides use the specified `evaluate-cong`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.PostcompositionObjectEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.EndpointInputNaturality as Objects
import SCT.VolumeI.Chapter02.Section02.PostcompositionParameterEvaluation as Parameter
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (post-square)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)

module At {Γ A C D : CAT} (F : MAP C D) (h : MAP Γ (Fun A C))
  {x y : Obj-abs A} (η : x =₁ y) where
  hF = funPost F ∘ h
  H = funUncurry h
  HF = funUncurry hF
  φ = funPost-uncurry F h
  i = insert {X = Γ} x
  j = insert {X = Γ} y
  δ = Objects.insert-cong 𝒯 M ℱ {X = Γ} η
  α = evaluate-cong {C = D} η ▷ hF
  β = F ◁ (evaluate-cong {C = C} η ▷ h)
  γ = F ◁ (H ◁ δ)
  Qx = evaluate-uncurry x hF
  Qy = evaluate-uncurry y hF
  Ax = comp-assoc i H F
  Ay = comp-assoc j H F
  Tx = Ax ∙ ((φ ▷ i) ∙ Qx)
  Ty = Ay ∙ ((φ ▷ j) ∙ Qy)
  Lx = F ◁ evaluate-uncurry x h
  Ly = F ◁ evaluate-uncurry y h
  Kx = evaluate-post-at x F h
  Ky = evaluate-post-at y F h

  abstract
    raw-square : (Ty ∙ α) =₂ (γ ∙ Tx)
    raw-square = paste-squares ((φ ▷ i) ∙ Qx) ((φ ▷ j) ∙ Qy)
      Ax Ay α ((F ∘ H) ◁ δ) γ
      (paste-squares Qx Qy (φ ▷ i) (φ ▷ j) α (HF ◁ δ) ((F ∘ H) ◁ δ)
        (Objects.EvaluationObject.natural 𝒯 M ℱ hF η) (interchange-at φ δ))
      (postWhisker-comp-at δ H F)

    original-square : (Ly ∙ β) =₂ (γ ∙ Lx)
    original-square = post-square F _ _ _ _ (Objects.EvaluationObject.natural 𝒯 M ℱ h η)

    comparison : (Ky ∙ α) =₂ (β ∙ Kx)
    comparison = cancel-left-reflect Ly
      (isoComp-assoc-at Ly β Kx ∙
      isoComp-cong (original-square ⁻¹) (idIso Kx) ∙
      (isoComp-assoc-at γ Lx Kx) ⁻¹ ∙
      isoComp-cong (idIso γ) (Parameter.At.comparison 𝒯 M ℱ F h x) ∙
      raw-square ∙
      isoComp-cong ((Parameter.At.comparison 𝒯 M ℱ F h y) ⁻¹) (idIso α) ∙
      (isoComp-assoc-at Ly Ky α) ⁻¹)
```
