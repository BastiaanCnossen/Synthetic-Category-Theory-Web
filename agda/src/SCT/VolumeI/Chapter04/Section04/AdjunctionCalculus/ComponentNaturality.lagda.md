# Naturality of the unit and counit components

The components in `Adjunctions` use the external unitors and
associators to give their stated endpoints. The naturality comparisons
below preserve precisely these frames. They hold for arbitrary absolute
parameter categories and do not use functoriality of universals.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.Naturality 𝒯 M ℱ P I E S using (naturality)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E
  using (post-composite)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E
  using (post-id)

module Components {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private module A = Adjunction adj

  abstract
    unit-natural : {Γ : CAT} {x y : MAP Γ C} (u : MorphismExpression x y) →
      ExpressionIso
        (compose-expression (A.unit-at x) (post-expression r (post-expression l u)))
        (compose-expression u (A.unit-at y))
    unit-natural {x = x} {y} u = expressionIso-compose
      (compose-expression-cong (post-id u) (expressionIso-id (A.unit-at y)))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition (post-expression (id C) u)
          (restrict-expression A.unit y) (comp-unitˡ x) (comp-unitˡ y) (comp-assoc y l r)))
        (expressionIso-compose
          (retarget-expressionIso (naturality A.unit u) (comp-unitˡ x) (comp-assoc y l r))
          (expressionIso-compose
            (retarget-composition (restrict-expression A.unit x) (post-expression (r ∘ l) u)
              (comp-unitˡ x) (comp-assoc x l r) (comp-assoc y l r))
            (compose-expression-cong (expressionIso-id (A.unit-at x))
              (expressionIso-inverse (post-composite l r u))))))

    counit-natural : {Γ : CAT} {x y : MAP Γ D} (u : MorphismExpression x y) →
      ExpressionIso
        (compose-expression (post-expression l (post-expression r u)) (A.counit-at y))
        (compose-expression (A.counit-at x) u)
    counit-natural {x = x} {y} u = expressionIso-compose
      (compose-expression-cong (expressionIso-id (A.counit-at x)) (post-id u))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition (restrict-expression A.counit x)
          (post-expression (id D) u) (comp-assoc x r l) (comp-unitˡ x) (comp-unitˡ y)))
        (expressionIso-compose
          (retarget-expressionIso (expressionIso-inverse (naturality A.counit u))
            (comp-assoc x r l) (comp-unitˡ y))
          (expressionIso-compose
            (retarget-composition (post-expression (l ∘ r) u) (restrict-expression A.counit y)
              (comp-assoc x r l) (comp-assoc y r l) (comp-unitˡ y))
            (compose-expression-cong (expressionIso-inverse (post-composite r l u))
              (expressionIso-id (A.counit-at y))))))
```
