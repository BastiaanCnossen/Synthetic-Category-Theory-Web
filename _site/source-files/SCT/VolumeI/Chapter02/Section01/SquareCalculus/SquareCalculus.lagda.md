# Minimum, maximum, and projections as glued squares

The minimum and maximum identities follow from the horizontal boundary
values and endpoint uniqueness. For the first projection, its full cocone
is transported along the product projection comparisons. This fixes the
common-edge matching in the notation `square(s₀,s₁)`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.SquareGluing 𝒯 M ℱ P I E Q public
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.LatticeUniqueness 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)

minimum-cocone maximum-cocone : Cocone d₁ d₁ [1]
minimum-cocone = record { left = s₀ ; right = s₀ ; match = idIso (s₀ ∘ d₁) }
maximum-cocone = record { left = s₁ ; right = s₁ ; match = idIso (s₁ ∘ d₁) }

square-minimum : (glue minimum-cocone) =₁ min
square-minimum = recognize-min _ (s₀-d₂ ∙ glue-bottom minimum-cocone) (s₀-d₀ ∙ glue-top minimum-cocone)

square-maximum : (glue maximum-cocone) =₁ max
square-maximum = recognize-max _ (s₁-d₂ ∙ glue-bottom maximum-cocone) (s₁-d₀ ∙ glue-top maximum-cocone)

first-projection-cocone : Cocone d₁ d₁ [1]
first-projection-cocone = coconeRetarget (coconePost pr₁ (squareCocone gluing-square)) s₀ s₁
  (pair-β₁ s₀ s₁) (pair-β₁ s₁ s₀)

square-first-projection : (glue first-projection-cocone) =₁ pr₁
square-first-projection = glue-compare _ _
  (coconeIso-compose (coconeIso-inverse
    (coconeRetarget-β (coconePost pr₁ (squareCocone gluing-square)) s₀ s₁
      (pair-β₁ s₀ s₁) (pair-β₁ s₁ s₀))) (glue-β first-projection-cocone))

second-projection-cocone : Cocone d₁ d₁ [1]
second-projection-cocone = record
  { left = s₁ ; right = s₀ ; match = s₀-d₁ ⁻¹ ∙ s₁-d₁ }

square-second-projection : (glue second-projection-cocone) =₁ pr₂
square-second-projection = recognize-second-projection _
  (s₀-d₂ ∙ glue-bottom second-projection-cocone) (s₁-d₀ ∙ glue-top second-projection-cocone)
```
