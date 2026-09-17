# The walking triangle and its simplicial identities

This is `def:Walking_Commutative_Triangle`, the face and degeneracy
construction, and `exercise:Simplicial_Identities`. Faces retain the names
`d₀`, `d₁`, `d₂`; the lower-dimensional faces are written `one`, `zero`
to keep their domains evident. The identities are natural isomorphisms
of the actual functors, not judgmental equalities.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter01.Section09.MiddleVertex as Middle
import SCT.VolumeI.Chapter01.Section09.OuterVertices as Outer

module SCT.VolumeI.Chapter01.Section09.WalkingTriangle
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.Lattice 𝒯 M ℱ P I E public

[0] [2] : CAT
[0] = One
[2] = Ar [1]

vertex₀ vertex₁ vertex₂ : Obj-abs [2]
vertex₀ = nameFun (const zero)
vertex₁ = nameFun (id [1])
vertex₂ = nameFun (const one)

d₀ d₁ d₂ : MAP [1] [2]
d₀ = max̄
d₁ = identityArrow
d₂ = min̄

s₀ s₁ : MAP [2] [1]
s₀ = ev₀
s₁ = ev₁

d₀-zero : =₁ (d₀ ∘ zero) vertex₁
d₀-zero = max-at-zero
d₀-one : =₁ (d₀ ∘ one) vertex₂
d₀-one = max-at-one
d₁-zero : =₁ (d₁ ∘ zero) vertex₀
d₁-zero = constantDiagram-point zero
d₁-one : =₁ (d₁ ∘ one) vertex₂
d₁-one = constantDiagram-point one
d₂-zero : =₁ (d₂ ∘ zero) vertex₀
d₂-zero = min-at-zero
d₂-one : =₁ (d₂ ∘ one) vertex₁
d₂-one = min-at-one

face-top : =₁ (d₀ ∘ one) (d₁ ∘ one)
face-top = Outer.Top.value 𝒯 M ℱ P I E
face-middle : =₁ (d₀ ∘ zero) (d₂ ∘ one)
face-middle = Middle.middle 𝒯 M ℱ P I E
face-bottom : =₁ (d₁ ∘ zero) (d₂ ∘ zero)
face-bottom = Outer.Bottom.value 𝒯 M ℱ P I E

s₀-d₀ : =₁ (s₀ ∘ d₀) (id [1])
s₀-d₀ = MorphismExpression.source-frame max-expression
s₀-d₁ : =₁ (s₀ ∘ d₁) (id [1])
s₀-d₁ = identity-source
s₀-d₂ : =₁ (s₀ ∘ d₂) (const zero)
s₀-d₂ = MorphismExpression.source-frame min-expression
s₁-d₀ : =₁ (s₁ ∘ d₀) (const one)
s₁-d₀ = MorphismExpression.target-frame max-expression
s₁-d₁ : =₁ (s₁ ∘ d₁) (id [1])
s₁-d₁ = identity-target
s₁-d₂ : =₁ (s₁ ∘ d₂) (id [1])
s₁-d₂ = MorphismExpression.target-frame min-expression
```


