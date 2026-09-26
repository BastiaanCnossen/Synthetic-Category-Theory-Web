# Composition of specified restriction identifications

The chosen action on restriction identifications preserves a commuting
triangle. We prove this through its retained uncurrying witness. It will
compare the two long edges of a glued square with one common diagonal.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorCoherence as Products

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionIdentificationComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (decode-encode)

module At {A B C : CAT} where
  X = Fun B C
  image : {f g : MAP A B} → f =₁ g →
    (funEval ∘ productMap (id X) f) =₁ (funEval ∘ productMap (id X) g)
  image α = funEval ◁ productMap-cong (idIso (id X)) α

  abstract
    normalize : {f g : MAP A B} (α : f =₁ g) →
      changeEndpoints (funPre-β f) (funPre-β g) (funUncurryIso (preCong α)) =₂ image α
    normalize {f} {g} α = decode-encode (funPre-β f) (funPre-β g) (image α) ∙
      changeEndpoints-cong (funPre-β f) (funPre-β g) (preCong-β α)

    image-comp : {f g h : MAP A B} (β : g =₁ h) (α : f =₁ g) →
      image (β ∙ α) =₂ (image β ∙ image α)
    image-comp β α = postWhisker-isoComp-at funEval _ _ ∙
      (postWhisker funEval ◁
        (productMap-cong-comp (idIso (id X)) (idIso (id X)) β α ∙
          productMap-cong-Iso₂ ((isoComp-unitˡ-at (idIso (id X))) ⁻¹) (idIso (β ∙ α))))

    image-cong : {f g : MAP A B} {α β : f =₁ g} → α =₂ β → image α =₂ image β
    image-cong η = postWhisker funEval ◁ productMap-cong-Iso₂ (idIso (idIso (id X))) η

    triangle : {f g h : MAP A B} (β : g =₁ h) (α : f =₁ g)
      (γ : f =₁ h) → (β ∙ α) =₂ γ →
      (preCong {E = C} β ∙ preCong α) =₂ preCong γ
    triangle {f} {g} {h} β α γ same = funReflect-Iso₂ _ _
      (changeEndpoints-reflect (funPre-β f) (funPre-β h) _ _
        (normalize γ ⁻¹ ∙ image-cong same ∙ image-comp β α ⁻¹ ∙
          isoComp-cong (normalize β) (normalize α) ∙
          (changeEndpoints-comp (funPre-β f) (funPre-β g) (funPre-β h)
            (funUncurryIso (preCong β)) (funUncurryIso (preCong α))) ⁻¹ ∙
          changeEndpoints-cong (funPre-β f) (funPre-β h)
            (funUncurryIso-comp (preCong β) (preCong α))))
```
