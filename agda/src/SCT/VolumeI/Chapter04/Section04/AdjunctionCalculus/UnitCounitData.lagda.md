# Units and counits before the triangle equations

These constructions depend on a unit and counit with their specified
endpoints. They can be used while proving the triangle equations, before
an adjunction record is available. The `Adjunction` record reuses these
normalizations, so the pre-triangle construction and its final record have
one chosen definition of every component.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public

module Data {C D : CAT} (l : MAP C D) (r : MAP D C)
  (unit : MorphismExpression (id C) (r ∘ l))
  (counit : MorphismExpression (l ∘ r) (id D)) where

  left-unit : MorphismExpression l ((l ∘ r) ∘ l)
  left-unit = retarget-expression (post-expression l unit)
    (comp-unitʳ l) ((comp-assoc l r l) ⁻¹)
  left-counit : MorphismExpression ((l ∘ r) ∘ l) l
  left-counit = retarget-expression (restrict-expression counit l)
    (idIso ((l ∘ r) ∘ l)) (comp-unitˡ l)
  right-unit : MorphismExpression r ((r ∘ l) ∘ r)
  right-unit = retarget-expression (restrict-expression unit r)
    (comp-unitˡ r) (idIso ((r ∘ l) ∘ r))
  right-counit : MorphismExpression ((r ∘ l) ∘ r) r
  right-counit = retarget-expression (post-expression r counit)
    ((comp-assoc r l r) ⁻¹) (comp-unitʳ r)

  unit-at : {Γ : CAT} (x : MAP Γ C) → MorphismExpression x (r ∘ (l ∘ x))
  unit-at x = retarget-expression (restrict-expression unit x)
    (comp-unitˡ x) (comp-assoc x l r)

  counit-at : {Γ : CAT} (y : MAP Γ D) → MorphismExpression (l ∘ (r ∘ y)) y
  counit-at y = retarget-expression (restrict-expression counit y)
    (comp-assoc y r l) (comp-unitˡ y)
```
