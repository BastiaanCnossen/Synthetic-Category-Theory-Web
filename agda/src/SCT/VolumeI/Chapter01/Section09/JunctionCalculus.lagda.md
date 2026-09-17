# Comparing the common vertex of two edges

Two endpoint triangles give the matching equation of a cocone comparison.
The following cancellation calculation retains the chosen matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.JunctionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.Morphisms 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section09.DiagramComparisons 𝒯 M ℱ I using (undo-frame)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right)

framed-junction : {X C : CAT} {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
  (A : =₁ a₀ a₁) (B : =₁ b₀ b₁) (l : =₁ a₀ l₀) (r : =₁ b₀ r₀)
  (nl : =₁ l₀ z) (nr : =₁ r₀ z) (δ : =₁ b₁ a₁) →
  =₂ (((nl ∙ l) ∙ invIso A) ∙ δ) ((nr ∙ r) ∙ invIso B) →
  =₂ ((invIso nr ∙ nl) ∙ l) (r ∙ (invIso B ∙ (invIso δ ∙ A)))
framed-junction A B l r nl nr δ compatible =
  cancel-left nr (r ∙ (invIso B ∙ (invIso δ ∙ A))) ∙
  (isoComp-cong (idIso (invIso nr)) (invIso normalized) ∙ isoComp-assoc-at (invIso nr) nl l)
  where
  inverse-compatible : =₂ (((nr ∙ r) ∙ invIso B) ∙ invIso δ) ((nl ∙ l) ∙ invIso A)
  inverse-compatible = cancel-right δ ((nl ∙ l) ∙ invIso A) ∙
    isoComp-cong (invIso compatible) (idIso (invIso δ))
  normalized : =₂ (nr ∙ (r ∙ (invIso B ∙ (invIso δ ∙ A)))) (nl ∙ l)
  normalized = undo-frame A (nl ∙ l) ∙
    (isoComp-cong inverse-compatible (idIso A) ∙
    (invIso (isoComp-assoc-at ((nr ∙ r) ∙ invIso B) (invIso δ) A) ∙
    (invIso (isoComp-assoc-at (nr ∙ r) (invIso B) (invIso δ ∙ A)) ∙
      invIso (isoComp-assoc-at nr r (invIso B ∙ (invIso δ ∙ A))))))

forward-junction : {X C : CAT} {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
  (A : =₁ a₀ a₁) (B : =₁ b₀ b₁) (l : =₁ a₀ l₀) (r : =₁ b₀ r₀)
  (nl : =₁ l₀ z) (nr : =₁ r₀ z) (δ : =₁ a₁ b₁) →
  =₂ (((nr ∙ r) ∙ invIso B) ∙ δ) ((nl ∙ l) ∙ invIso A) →
  =₂ ((invIso nr ∙ nl) ∙ l) (r ∙ (invIso B ∙ (δ ∙ A)))
forward-junction A B l r nl nr δ compatible =
  cancel-left nr (r ∙ (invIso B ∙ (δ ∙ A))) ∙
  (isoComp-cong (idIso (invIso nr)) (invIso normalized) ∙ isoComp-assoc-at (invIso nr) nl l)
  where
  normalized : =₂ (nr ∙ (r ∙ (invIso B ∙ (δ ∙ A)))) (nl ∙ l)
  normalized = undo-frame A (nl ∙ l) ∙
    (isoComp-cong compatible (idIso A) ∙
    (invIso (isoComp-assoc-at ((nr ∙ r) ∙ invIso B) δ A) ∙
    (invIso (isoComp-assoc-at (nr ∙ r) (invIso B) (δ ∙ A)) ∙
      invIso (isoComp-assoc-at nr r (invIso B ∙ (δ ∙ A))))))
```

