# Adjunctions on functor categories

For `prop:Adjunction_On_Functor_Categories`, an adjunction induces
adjunctions by postcomposition and precomposition. In the second case,
precomposition by the original right adjoint is the new left adjoint:
it maps `Fun(C,K)` to `Fun(D,K)`.

Both constructions curry the original unit and counit components. Their
proofs evaluate the actual chosen transformations, retain one common
middle frame in each triangle, and reflect the original component
triangles. These are global comparisons at an arbitrary absolute `K`;
no objectwise criterion or functoriality of universals is required.

The supporting endpoint calculations are in `AdjunctionCalculus/`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.FunctorCategoryAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PostcompositionAdjunctions as Post
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionAdjunctions as Pre

postcomposition : {C D : CAT} {l : MAP C D} {r : MAP D C} → Adjunction l r → (K : CAT) →
  Adjunction (funPost {C = K} l) (funPost {C = K} r)
postcomposition adj K = Post.At.value 𝒯 M ℱ P I E S adj K

precomposition : {C D : CAT} {l : MAP C D} {r : MAP D C} → Adjunction l r → (K : CAT) →
  Adjunction (funPre {D = K} r) (funPre {D = K} l)
precomposition adj K = Pre.At.value 𝒯 M ℱ P I E S adj K
```
