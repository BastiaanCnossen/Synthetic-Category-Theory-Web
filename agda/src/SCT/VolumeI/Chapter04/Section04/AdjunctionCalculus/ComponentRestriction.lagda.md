# Restriction of unit and counit components

Restrict the unit and counit transformations, then normalize their endpoints
by the unitor and associator. Mapping these sections through endpoint
transport supplies both restriction and parameter-change comparisons.
Their values are the explicit components defined in `Adjunctions`.

`UnitCounitLaws` takes the two transformations without triangle identities.
`Components` specializes it to an adjunction and retains the usual names.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData as Data
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I
  using (FamilySection; variable-family; post; represented; unit-frame; associator-frame;
    restricted-section; map-section; transport)

module UnitCounitLaws {C D : CAT} (l : MAP C D) (r : MAP D C)
  (unit : MorphismExpression (id C) (r ∘ l))
  (counit : MorphismExpression (l ∘ r) (id D)) where
  private module A = Data.Data 𝒯 M ℱ P I E S l r unit counit

  unit-section : FamilySection (variable-family C) (post r (represented l))
  unit-section = map-section
    (transport (unit-frame C) (associator-frame l r)) (restricted-section unit)

  counit-section : FamilySection (post l (represented r)) (variable-family D)
  counit-section = map-section
    (transport (associator-frame r l) (unit-frame D)) (restricted-section counit)

  abstract
    unit-restrict : {Γ Δ : CAT} (x : MAP Γ C) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (A.unit-at x) h)
        (idIso (x ∘ h))
        ((r ◁ comp-assoc h x l) ∙ comp-assoc h (l ∘ x) r))
        (A.unit-at (x ∘ h))
    unit-restrict = FamilySection.on-restriction unit-section

    counit-restrict : {Γ Δ : CAT} (y : MAP Γ D) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (A.counit-at y) h)
        ((l ◁ comp-assoc h y r) ∙ comp-assoc h (r ∘ y) l)
        (idIso (y ∘ h))) (A.counit-at (y ∘ h))
    counit-restrict = FamilySection.on-restriction counit-section

    unit-parameter : {Γ : CAT} {x x′ : MAP Γ C} (ξ : x =₁ x′) →
      ExpressionIso (retarget-expression (A.unit-at x) ξ (r ◁ (l ◁ ξ))) (A.unit-at x′)
    unit-parameter = FamilySection.on-change unit-section

    counit-parameter : {Γ : CAT} {y y′ : MAP Γ D} (ξ : y =₁ y′) →
      ExpressionIso (retarget-expression (A.counit-at y) (l ◁ (r ◁ ξ)) ξ) (A.counit-at y′)
    counit-parameter = FamilySection.on-change counit-section

module Components {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) = UnitCounitLaws l r (Adjunction.unit adj) (Adjunction.counit adj)
```
