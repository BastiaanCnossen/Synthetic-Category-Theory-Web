# Degenerate triangles retain all three vertices

Both simplicial degeneracies compare with the expected pair of interval
arrows as whole cocones. The matching equation follows from the two
endpoint equations of the middle face identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.DegenerateCocones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.WalkingTriangle 𝒯 M ℱ P I E public
import SCT.VolumeI.Chapter01.Section09.MiddleVertex as Middle
import SCT.VolumeI.Chapter01.Section09.OuterVertices as Outer
open import SCT.VolumeI.Chapter01.Section09.JunctionCalculus 𝒯 M ℱ P I using (framed-junction; forward-junction)
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 public
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)

triangle-edges : Cocone one zero [2]
triangle-edges = record { left = d₂ ; right = d₀ ; match = invIso face-middle }

left-identity-pair right-identity-pair : Cocone one zero [1]
left-identity-pair = record
  { left = const zero ; right = id [1]
  ; match = invIso (comp-unitˡ zero) ∙ (constant-boundary one zero) }
right-identity-pair = record
  { left = id [1] ; right = const one
  ; match = invIso (constant-boundary zero one) ∙ comp-unitˡ one }

left-degeneracy : CoconeIso (coconePost s₀ triangle-edges) left-identity-pair
left-degeneracy = record
  { leftIso = s₀-d₂ ; rightIso = s₀-d₀
  ; compatible = isoComp-cong (idIso (s₀-d₀ ▷ zero))
      (isoComp-cong (idIso (invIso (comp-assoc zero d₀ s₀)))
        (isoComp-cong (invIso (post-inverse s₀ face-middle)) (idIso (comp-assoc one d₂ s₀)))) ∙
      framed-junction (comp-assoc one d₂ s₀) (comp-assoc zero d₀ s₀)
        (s₀-d₂ ▷ one) (s₀-d₀ ▷ zero) (constant-boundary one zero) (comp-unitˡ zero)
        (s₀ ◁ face-middle) (Middle.source-compatible 𝒯 M ℱ P I E) }

right-degeneracy : CoconeIso (coconePost s₁ triangle-edges) right-identity-pair
right-degeneracy = record
  { leftIso = s₁-d₂ ; rightIso = s₁-d₀
  ; compatible = isoComp-cong (idIso (s₁-d₀ ▷ zero))
      (isoComp-cong (idIso (invIso (comp-assoc zero d₀ s₁)))
        (isoComp-cong (invIso (post-inverse s₁ face-middle)) (idIso (comp-assoc one d₂ s₁)))) ∙
      framed-junction (comp-assoc one d₂ s₁) (comp-assoc zero d₀ s₁)
        (s₁-d₂ ▷ one) (s₁-d₀ ▷ zero) (comp-unitˡ one) (constant-boundary zero one)
        (s₁ ◁ face-middle) (Middle.target-compatible 𝒯 M ℱ P I E) }

triangle-source : Cocone zero zero [2]
triangle-source = record { left = d₁ ; right = d₂ ; match = face-bottom }

upper-edges : Cocone one one [2]
upper-edges = record { left = d₀ ; right = d₁ ; match = face-top }

left-source-pair right-source-pair : Cocone zero zero [1]
left-source-pair = record { left = id [1] ; right = const zero
  ; match = invIso (constant-boundary zero zero) ∙ comp-unitˡ zero }
right-source-pair = record { left = id [1] ; right = id [1]
  ; match = invIso (comp-unitˡ zero) ∙ comp-unitˡ zero }

left-target-pair right-target-pair : Cocone one one [1]
left-target-pair = record { left = id [1] ; right = id [1]
  ; match = invIso (comp-unitˡ one) ∙ comp-unitˡ one }
right-target-pair = record { left = const one ; right = id [1]
  ; match = invIso (comp-unitˡ one) ∙ (constant-boundary one one) }

left-source : CoconeIso (coconePost s₀ triangle-source) left-source-pair
left-source = record { leftIso = s₀-d₁ ; rightIso = s₀-d₂
  ; compatible = forward-junction (comp-assoc zero d₁ s₀) (comp-assoc zero d₂ s₀)
      (s₀-d₁ ▷ zero) (s₀-d₂ ▷ zero) (comp-unitˡ zero) (constant-boundary zero zero)
      (s₀ ◁ face-bottom) (Outer.Bottom.source-compatible 𝒯 M ℱ P I E) }
right-source : CoconeIso (coconePost s₁ triangle-source) right-source-pair
right-source = record { leftIso = s₁-d₁ ; rightIso = s₁-d₂
  ; compatible = forward-junction (comp-assoc zero d₁ s₁) (comp-assoc zero d₂ s₁)
      (s₁-d₁ ▷ zero) (s₁-d₂ ▷ zero) (comp-unitˡ zero) (comp-unitˡ zero)
      (s₁ ◁ face-bottom) (Outer.Bottom.target-compatible 𝒯 M ℱ P I E) }
left-target : CoconeIso (coconePost s₀ upper-edges) left-target-pair
left-target = record { leftIso = s₀-d₀ ; rightIso = s₀-d₁
  ; compatible = forward-junction (comp-assoc one d₀ s₀) (comp-assoc one d₁ s₀)
      (s₀-d₀ ▷ one) (s₀-d₁ ▷ one) (comp-unitˡ one) (comp-unitˡ one)
      (s₀ ◁ face-top) (Outer.Top.source-compatible 𝒯 M ℱ P I E) }
right-target : CoconeIso (coconePost s₁ upper-edges) right-target-pair
right-target = record { leftIso = s₁-d₀ ; rightIso = s₁-d₁
  ; compatible = forward-junction (comp-assoc one d₀ s₁) (comp-assoc one d₁ s₁)
      (s₁-d₀ ▷ one) (s₁-d₁ ▷ one) (constant-boundary one one) (comp-unitˡ one)
      (s₁ ◁ face-top) (Outer.Top.target-compatible 𝒯 M ℱ P I E) }
```



