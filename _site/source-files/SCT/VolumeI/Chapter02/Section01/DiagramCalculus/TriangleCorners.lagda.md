# The vertices of the triangle inside the square

The lower triangle occupies the corners `(00,01,11)`. Its retraction
also sends the remaining corner `(10)` to vertex zero. These are the
point computations used in the core calculation.

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

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.TriangleCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareRetractions 𝒯 M ℱ P I E Q public

s₀-vertex₀ : (s₀ ∘ vertex₀) =₁ zero
s₀-vertex₀ = constant-boundary zero zero ∙ evaluate-name zero (const zero)
s₁-vertex₀ : (s₁ ∘ vertex₀) =₁ zero
s₁-vertex₀ = constant-boundary one zero ∙ evaluate-name one (const zero)
s₀-vertex₁ : (s₀ ∘ vertex₁) =₁ zero
s₀-vertex₁ = comp-unitˡ zero ∙ evaluate-name zero (id [1])
s₁-vertex₁ : (s₁ ∘ vertex₁) =₁ one
s₁-vertex₁ = comp-unitˡ one ∙ evaluate-name one (id [1])
s₀-vertex₂ : (s₀ ∘ vertex₂) =₁ one
s₀-vertex₂ = constant-boundary zero one ∙ evaluate-name zero (const one)
s₁-vertex₂ : (s₁ ∘ vertex₂) =₁ one
s₁-vertex₂ = constant-boundary one one ∙ evaluate-name one (const one)

j₀-vertex₀ : (j₀ ∘ vertex₀) =₁ pair zero zero
j₀-vertex₀ = pair-cong s₀-vertex₀ s₁-vertex₀ ∙ pair-pre s₀ s₁ vertex₀
j₀-vertex₁ : (j₀ ∘ vertex₁) =₁ pair zero one
j₀-vertex₁ = pair-cong s₀-vertex₁ s₁-vertex₁ ∙ pair-pre s₀ s₁ vertex₁
j₀-vertex₂ : (j₀ ∘ vertex₂) =₁ pair one one
j₀-vertex₂ = pair-cong s₀-vertex₂ s₁-vertex₂ ∙ pair-pre s₀ s₁ vertex₂
j₁-vertex₁ : (j₁ ∘ vertex₁) =₁ pair one zero
j₁-vertex₁ = pair-cong s₁-vertex₁ s₀-vertex₁ ∙ pair-pre s₁ s₀ vertex₁

retract-corner : (v : Obj-abs [2]) (z : Obj-abs ([1] × [1])) →
  (j₀ ∘ v) =₁ z → (p₀ ∘ z) =₁ v
retract-corner v z ε = comp-unitˡ v ∙ ((p₀-j₀ ▷ v) ∙
  ((comp-assoc v j₀ p₀) ⁻¹ ∙ (p₀ ◁ ε ⁻¹)))

p₀-corner₀₀ : (p₀ ∘ pair zero zero) =₁ vertex₀
p₀-corner₀₀ = retract-corner vertex₀ _ j₀-vertex₀
p₀-corner₀₁ : (p₀ ∘ pair zero one) =₁ vertex₁
p₀-corner₀₁ = retract-corner vertex₁ _ j₀-vertex₁
p₀-corner₁₁ : (p₀ ∘ pair one one) =₁ vertex₂
p₀-corner₁₁ = retract-corner vertex₂ _ j₀-vertex₂
p₀-corner₁₀ : (p₀ ∘ pair one zero) =₁ vertex₀
p₀-corner₁₀ = d₁-zero ∙ ((d₁ ◁ s₀-vertex₁) ∙
  (comp-assoc vertex₁ s₀ d₁ ∙ ((p₀-j₁ ▷ vertex₁) ∙
    ((comp-assoc vertex₁ j₁ p₀) ⁻¹ ∙ (p₀ ◁ j₁-vertex₁ ⁻¹)))))
```
