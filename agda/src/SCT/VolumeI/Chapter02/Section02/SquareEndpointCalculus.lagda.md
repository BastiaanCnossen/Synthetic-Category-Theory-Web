# Endpoint algebra for a square in the arrow category

The double-evaluation equation converts a geometric corner equation
into the corresponding endpoint equation, and conversely. This calculation
is independent of the construction of the square and its boundary maps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.SquareEndpointCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.ExpressionPostcomposition 𝒯 M ℱ I public
import SCT.VolumeI.Chapter01.Section03.PairingUnits as VerticalUnits
open VerticalUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

module At {Γ C : CAT} (N : MAP Γ (Ar (Ar C))) (u v : Obj-abs [1])
  {h₀ k₀ : MAP Γ (Ar C)}
  (a₀ : (funPost (evaluate u) ∘ N) =₁ h₀)
  (b₀ : (evaluate v ∘ N) =₁ k₀)
  (τ : (evaluate v ∘ h₀) =₁ (evaluate u ∘ k₀))
  (evaluation : ((evaluate u ◁ b₀) ∙ evaluate-post-at v (evaluate u) N) =₂
    (τ ∙ (evaluate v ◁ a₀)))
  {h k : MAP Γ (Ar C)} {z : MAP Γ C}
  (α : h₀ =₁ h) (β : k₀ =₁ k)
  (p : (evaluate v ∘ h) =₁ z) (q : (evaluate u ∘ k) =₁ z) where
  eα = evaluate v ◁ α
  eβ = evaluate u ◁ β
  η = evaluate v ◁ a₀
  eb = evaluate u ◁ b₀
  tail = evaluate-post-at v (evaluate u) N

  abstract
    left-normal : (p ∙ (evaluate v ◁ (α ∙ a₀))) =₂ ((p ∙ eα) ∙ η)
    left-normal = (isoComp-assoc-at p eα η) ⁻¹ ∙
      isoComp-cong (idIso p) (postWhisker-isoComp-at (evaluate v) α a₀)

    right-normal : ((q ∙ (eβ ∙ τ)) ∙ η) =₂
      (q ∙ post-boundary v (evaluate u) N (β ∙ b₀))
    right-normal = isoComp-cong (idIso q)
        ((post-boundary-normal v (evaluate u) N (β ∙ b₀)) ⁻¹ ∙
          isoComp-cong ((postWhisker-isoComp-at (evaluate u) β b₀) ⁻¹) (idIso tail) ∙
          (isoComp-assoc-at eβ eb tail) ⁻¹) ∙
      isoComp-cong (idIso q) (isoComp-cong (idIso eβ) (evaluation ⁻¹)) ∙
      isoComp-cong (idIso q) (isoComp-assoc-at eβ τ η) ∙
      isoComp-assoc-at q (eβ ∙ τ) η

    to-endpoint : (p ∙ eα) =₂ (q ∙ (eβ ∙ τ)) →
      (p ∙ (evaluate v ◁ (α ∙ a₀))) =₂
        (q ∙ post-boundary v (evaluate u) N (β ∙ b₀))
    to-endpoint corner = right-normal ∙ isoComp-cong corner (idIso η) ∙ left-normal

    from-endpoint : (p ∙ (evaluate v ◁ (α ∙ a₀))) =₂
      (q ∙ post-boundary v (evaluate u) N (β ∙ b₀)) →
      (p ∙ eα) =₂ (q ∙ (eβ ∙ τ))
    from-endpoint endpoint = cancel-right-reflect η (right-normal ⁻¹ ∙ endpoint ∙ left-normal ⁻¹)
```
