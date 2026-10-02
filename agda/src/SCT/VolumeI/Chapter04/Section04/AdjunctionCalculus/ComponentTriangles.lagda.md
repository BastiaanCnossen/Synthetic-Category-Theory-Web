# Triangle identities at arbitrary parameters

Restrict a triangle identity and identify its two sides. The composite
is identified with the composite of the normalized components by
`RawComponentTriangles`; the restricted identity is identified with the
identity component. The frame calculations are shared with the converse
construction of an adjunction from its component triangles.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdRestriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.RawComponentTriangles as Raw
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData as Data

private
  corner : {Γ C D : CAT} (x : MAP Γ C) (l : MAP C D) (r : MAP D C) →
    (((l ∘ r) ∘ l) ∘ x) =₁ (l ∘ (r ∘ (l ∘ x)))
  corner x l r = comp-assoc (l ∘ x) r l ∙ comp-assoc x l (l ∘ r)

module Components {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private
    module A = Data.Data 𝒯 M ℱ P I E S l r (Adjunction.unit adj) (Adjunction.counit adj) using (left-unit; left-counit; right-unit; right-counit; unit-at; counit-at)
    module RawComponents = Raw.Components 𝒯 M ℱ P I E S l r (Adjunction.unit adj) (Adjunction.counit adj) using (left-unit-component; left-counit-component; right-unit-component; right-counit-component; left-expanded; right-expanded)

  abstract
    left-unit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-unit x)
        (idIso (l ∘ x)) (corner x l r)) (post-expression l (A.unit-at x))
    left-unit-component {Γ} x = RawComponents.left-unit-component {Γ = Γ} x

    left-counit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-counit x)
        (corner x l r) (idIso (l ∘ x))) (A.counit-at (l ∘ x))
    left-counit-component {Γ} x = RawComponents.left-counit-component {Γ = Γ} x

    right-unit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-unit y)
        (idIso (r ∘ y)) (corner y r l)) (A.unit-at (r ∘ y))
    right-unit-component {Γ} x = RawComponents.right-unit-component {Γ = Γ} x

    right-counit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-counit y)
        (corner y r l) (idIso (r ∘ y))) (post-expression r (A.counit-at y))
    right-counit-component {Γ} x = RawComponents.right-counit-component {Γ = Γ} x

    left-triangle-at : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (compose-expression (post-expression l (A.unit-at x)) (A.counit-at (l ∘ x)))
        (identity-expression (l ∘ x))
    left-triangle-at x = expressionIso-compose (IdRestriction.Restrict.comparison 𝒯 M ℱ P I E l x)
      (expressionIso-compose (restrict-expressionIso (Adjunction.left-triangle adj) x)
        (expressionIso-inverse (RawComponents.left-expanded x)))

    right-triangle-at : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (compose-expression (A.unit-at (r ∘ y)) (post-expression r (A.counit-at y)))
        (identity-expression (r ∘ y))
    right-triangle-at y = expressionIso-compose (IdRestriction.Restrict.comparison 𝒯 M ℱ P I E r y)
      (expressionIso-compose (restrict-expressionIso (Adjunction.right-triangle adj) y)
        (expressionIso-inverse (RawComponents.right-expanded y)))
```
