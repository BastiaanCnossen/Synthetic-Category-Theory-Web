# The walking triangle and its simplicial identities

This is `def:Walking_Commutative_Triangle`, the face and degeneracy
construction, and `exercise:Simplicial_Identities`. Faces retain the names
`d₀`, `d₁`, `d₂`; the lower-dimensional faces are written `one`, `zero`
to keep their domains evident. The identities are natural isomorphisms
of the actual functors, not judgmental equalities.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.MiddleVertex as Middle
import SCT.VolumeI.Chapter02.Section01.OuterVertices as Outer

module SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E public

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

d₀-zero : (d₀ ∘ zero) =₁ vertex₁
d₀-zero = max-at-zero
d₀-one : (d₀ ∘ one) =₁ vertex₂
d₀-one = max-at-one
d₁-zero : (d₁ ∘ zero) =₁ vertex₀
d₁-zero = constantDiagram-point zero
d₁-one : (d₁ ∘ one) =₁ vertex₂
d₁-one = constantDiagram-point one
d₂-zero : (d₂ ∘ zero) =₁ vertex₀
d₂-zero = min-at-zero
d₂-one : (d₂ ∘ one) =₁ vertex₁
d₂-one = min-at-one

face-top : (d₀ ∘ one) =₁ (d₁ ∘ one)
face-top = Outer.Top.value 𝒯 M ℱ P I E
face-middle : (d₀ ∘ zero) =₁ (d₂ ∘ one)
face-middle = Middle.middle 𝒯 M ℱ P I E
face-bottom : (d₁ ∘ zero) =₁ (d₂ ∘ zero)
face-bottom = Outer.Bottom.value 𝒯 M ℱ P I E

s₀-d₀ : (s₀ ∘ d₀) =₁ (id [1])
s₀-d₀ = MorphismExpression.source-frame max-expression
s₀-d₁ : (s₀ ∘ d₁) =₁ (id [1])
s₀-d₁ = identity-source
s₀-d₂ : (s₀ ∘ d₂) =₁ (const zero)
s₀-d₂ = MorphismExpression.source-frame min-expression
s₁-d₀ : (s₁ ∘ d₀) =₁ (const one)
s₁-d₀ = MorphismExpression.target-frame max-expression
s₁-d₁ : (s₁ ∘ d₁) =₁ (id [1])
s₁-d₁ = identity-target
s₁-d₂ : (s₁ ∘ d₂) =₁ (id [1])
s₁-d₂ = MorphismExpression.target-frame min-expression
```


