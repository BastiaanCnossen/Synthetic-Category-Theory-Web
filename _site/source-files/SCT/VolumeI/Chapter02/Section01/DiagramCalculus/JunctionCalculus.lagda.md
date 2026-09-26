# Comparing the common vertex of two edges

Two endpoint triangles give the matching equation of a cocone comparison.
The following cancellation calculation retains the chosen matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.JunctionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DiagramComparisons 𝒯 M ℱ I using (undo-frame)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right)

framed-junction : {X C : CAT} {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
  (A : a₀ =₁ a₁) (B : b₀ =₁ b₁) (l : a₀ =₁ l₀) (r : b₀ =₁ r₀)
  (nl : l₀ =₁ z) (nr : r₀ =₁ z) (δ : b₁ =₁ a₁) →
  (((nl ∙ l) ∙ A ⁻¹) ∙ δ) =₂ ((nr ∙ r) ∙ B ⁻¹) →
  ((nr ⁻¹ ∙ nl) ∙ l) =₂ (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A)))
framed-junction A B l r nl nr δ compatible =
  cancel-left nr (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A))) ∙
  (isoComp-cong (idIso (nr ⁻¹)) (normalized ⁻¹) ∙ isoComp-assoc-at (nr ⁻¹) nl l)
  where
  inverse-compatible : (((nr ∙ r) ∙ B ⁻¹) ∙ δ ⁻¹) =₂ ((nl ∙ l) ∙ A ⁻¹)
  inverse-compatible = cancel-right δ ((nl ∙ l) ∙ A ⁻¹) ∙
    isoComp-cong (compatible ⁻¹) (idIso (δ ⁻¹))
  normalized : (nr ∙ (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A)))) =₂ (nl ∙ l)
  normalized = undo-frame A (nl ∙ l) ∙
    (isoComp-cong inverse-compatible (idIso A) ∙
    ((isoComp-assoc-at ((nr ∙ r) ∙ B ⁻¹) (δ ⁻¹) A) ⁻¹ ∙
    ((isoComp-assoc-at (nr ∙ r) (B ⁻¹) (δ ⁻¹ ∙ A)) ⁻¹ ∙
      (isoComp-assoc-at nr r (B ⁻¹ ∙ (δ ⁻¹ ∙ A))) ⁻¹)))

forward-junction : {X C : CAT} {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
  (A : a₀ =₁ a₁) (B : b₀ =₁ b₁) (l : a₀ =₁ l₀) (r : b₀ =₁ r₀)
  (nl : l₀ =₁ z) (nr : r₀ =₁ z) (δ : a₁ =₁ b₁) →
  (((nr ∙ r) ∙ B ⁻¹) ∙ δ) =₂ ((nl ∙ l) ∙ A ⁻¹) →
  ((nr ⁻¹ ∙ nl) ∙ l) =₂ (r ∙ (B ⁻¹ ∙ (δ ∙ A)))
forward-junction A B l r nl nr δ compatible =
  cancel-left nr (r ∙ (B ⁻¹ ∙ (δ ∙ A))) ∙
  (isoComp-cong (idIso (nr ⁻¹)) (normalized ⁻¹) ∙ isoComp-assoc-at (nr ⁻¹) nl l)
  where
  normalized : (nr ∙ (r ∙ (B ⁻¹ ∙ (δ ∙ A)))) =₂ (nl ∙ l)
  normalized = undo-frame A (nl ∙ l) ∙
    (isoComp-cong compatible (idIso A) ∙
    ((isoComp-assoc-at ((nr ∙ r) ∙ B ⁻¹) δ A) ⁻¹ ∙
    ((isoComp-assoc-at (nr ∙ r) (B ⁻¹) (δ ∙ A)) ⁻¹ ∙
      (isoComp-assoc-at nr r (B ⁻¹ ∙ (δ ∙ A))) ⁻¹)))
```

