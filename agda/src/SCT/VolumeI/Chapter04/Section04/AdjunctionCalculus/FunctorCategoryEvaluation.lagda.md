# Evaluation of the functor-category unit and counit

The chosen transformations on functor categories evaluate to their
defining framed diagrams. These comparisons use the full recovery theorem
for currying, rather than an identification of underlying arrows alone.
The triangle identities remain a separate obligation.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S
  using (uncurry-expression)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryComponents as Components
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingCurryingRecovery as Recovery

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (A : Adjunction l r) (K : CAT) where
  module Chosen = Components.At 𝒯 M ℱ P I E S A K
  module Postcomposition where
    open Chosen.Postcomposition public
    unit-comparison : ExpressionIso (uncurry-expression unit) unit-diagram
    unit-comparison = Recovery.At.value 𝒯 M ℱ P I E (id (Fun K C)) (right ∘ left) unit-diagram
    counit-comparison : ExpressionIso (uncurry-expression counit) counit-diagram
    counit-comparison = Recovery.At.value 𝒯 M ℱ P I E (left ∘ right) (id (Fun K D)) counit-diagram

  module Precomposition where
    open Chosen.Precomposition public
    unit-comparison : ExpressionIso (uncurry-expression unit) unit-diagram
    unit-comparison = Recovery.At.value 𝒯 M ℱ P I E (id (Fun C K)) (right ∘ left) unit-diagram
    counit-comparison : ExpressionIso (uncurry-expression counit) counit-diagram
    counit-comparison = Recovery.At.value 𝒯 M ℱ P I E (left ∘ right) (id (Fun D K)) counit-diagram
```
