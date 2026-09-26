# Two triangles forming a square

For `def:Commutative_Square` a square in `C` is a functor from
`[1] × [1]`. The maps `j₀` and `j₁` give its two triangles. Both long
edges compare with the diagonal, fixing the matching in
`eq:Commutative_Square_Axiom`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯

CommutativeSquare : CAT → Set m
CommutativeSquare C = MAP ([1] × [1]) C

j₀ j₁ : MAP [2] ([1] × [1])
j₀ = pair s₀ s₁
j₁ = pair s₁ s₀

diagonal : MAP [1] ([1] × [1])
diagonal = pair (id [1]) (id [1])

j₀-diagonal : (j₀ ∘ d₁) =₁ diagonal
j₀-diagonal = pair-cong s₀-d₁ s₁-d₁ ∙ pair-pre s₀ s₁ d₁

j₁-diagonal : (j₁ ∘ d₁) =₁ diagonal
j₁-diagonal = pair-cong s₁-d₁ s₀-d₁ ∙ pair-pre s₁ s₀ d₁

gluing-square : Square d₁ d₁ j₀ j₁
gluing-square = record { commute = j₁-diagonal ⁻¹ ∙ j₀-diagonal }

bottom-boundary : (j₁ ∘ d₂) =₁ (insert zero)
bottom-boundary = pair-cong s₁-d₂ s₀-d₂ ∙ pair-pre s₁ s₀ d₂

top-boundary : (j₀ ∘ d₀) =₁ (insert one)
top-boundary = pair-cong s₀-d₀ s₁-d₀ ∙ pair-pre s₀ s₁ d₀
```
