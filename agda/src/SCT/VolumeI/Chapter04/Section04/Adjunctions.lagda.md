# Units, counits, and the triangle identities

The record `Adjunction` formalizes `def:Adjunction` using framed
morphism expressions for natural transformations. Each triangle is an
endpoint-preserving comparison with the identity transformation.
This is the book's single-counit definition; no category of adjunctions
is asserted.

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

module SCT.VolumeI.Chapter04.Section04.Adjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public

record Adjunction {C D : CAT} (l : MAP C D) (r : MAP D C) : Set m where
  field
    unit : MorphismExpression (id C) (r ∘ l)
    counit : MorphismExpression (l ∘ r) (id D)

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

  field
    left-triangle : ExpressionIso (compose-expression left-unit left-counit) (identity-expression l)
    right-triangle : ExpressionIso (compose-expression right-unit right-counit) (identity-expression r)

  unit-at : {Γ : CAT} (x : MAP Γ C) → MorphismExpression x (r ∘ (l ∘ x))
  unit-at x = retarget-expression (restrict-expression unit x)
    (comp-unitˡ x) (comp-assoc x l r)

  counit-at : {Γ : CAT} (y : MAP Γ D) → MorphismExpression (l ∘ (r ∘ y)) y
  counit-at y = retarget-expression (restrict-expression counit y)
    (comp-assoc y r l) (comp-unitˡ y)

  transpose : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D) →
    MorphismExpression (l ∘ x) y → MorphismExpression x (r ∘ y)
  transpose x y α = compose-expression (unit-at x) (post-expression r α)

  untranspose : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D) →
    MorphismExpression x (r ∘ y) → MorphismExpression (l ∘ x) y
  untranspose x y β = compose-expression (post-expression l β) (counit-at y)
```

The displayed `transpose` and `untranspose` are the formulas used in
`prop:Adjunctions_Via_Natural_Equivalence_Hom_Groupoids`.
This module constructs the transformations; their inverse equations are
a separate proof obligation and are not asserted here.

