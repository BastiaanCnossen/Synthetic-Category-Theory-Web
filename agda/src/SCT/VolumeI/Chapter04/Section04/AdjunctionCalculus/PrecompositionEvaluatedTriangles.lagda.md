# The evaluated precomposition triangles

Pairing the original component triangles with the identity of the functor
coordinate and evaluating proves the normalized target triangles. The
left precomposition triangle uses the original right triangle, and the
right one uses the original left triangle. Identifying these expressions
with the chosen curried unit and counit is a separate obligation.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionEvaluatedTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles as Triangles
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.FixedCoordinateTriangles as Fixed

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj
  module Original = Triangles.Components 𝒯 M ℱ P I E S adj
  X = Fun C K
  Y = Fun D K
  e : MAP (X × C) K
  e = funEval
  d : MAP (Y × D) K
  d = funEval
  module Left = Fixed.At 𝒯 M ℱ P I E S (pr₁ {X} {D})
    (A.unit-at (r ∘ pr₂)) (post-expression r (A.counit-at pr₂)) e
  module Right = Fixed.At 𝒯 M ℱ P I E S (pr₁ {Y} {C})
    (post-expression l (A.unit-at pr₂)) (A.counit-at (l ∘ pr₂)) d

  abstract
    left-triangle : ExpressionIso (compose-expression Left.first Left.second)
      (identity-expression (e ∘ pair pr₁ (r ∘ pr₂ {X} {D})))
    left-triangle = Left.value (Original.right-triangle-at (pr₂ {X} {D}))

    right-triangle : ExpressionIso (compose-expression Right.first Right.second)
      (identity-expression (d ∘ pair pr₁ (l ∘ pr₂ {Y} {C})))
    right-triangle = Right.value (Original.left-triangle-at (pr₂ {Y} {C}))
```
