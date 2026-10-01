# Restricting evaluated precomposition components

Restricting the unit in the object coordinate gives its component at the
image under the original right adjoint. The dual calculation restricts
the counit. These retain the middle frames used by the triangles.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionRestrictedComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionNormalizedComponents as Normalized
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestrictionParameters as Parameters
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedPairRestriction as Paired
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj
  module N = Normalized.At 𝒯 M ℱ P I E S adj K
  module LF = N.LeftFrames
  module RF = N.RightFrames
  module Changed = Parameters.At 𝒯 M ℱ P I E S adj
  module Unit = Changed.Unit (pr₂ {N.X} {C}) LF.W LF.second-coordinate
  module Counit = Changed.Counit (pr₂ {N.Y} {D}) RF.W RF.second-coordinate

  abstract
    left-identity : ExpressionIso
      (retarget-expression (restrict-expression (identity-expression (pr₁ {N.X} {C})) LF.W)
        LF.first-coordinate LF.first-coordinate) (identity-expression (pr₁ {N.X} {D}))
    left-identity = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E LF.first-coordinate)
      (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E (pr₁ {N.X} {C}) LF.W)
        LF.first-coordinate LF.first-coordinate)

    right-identity : ExpressionIso
      (retarget-expression (restrict-expression (identity-expression (pr₁ {N.Y} {D})) RF.W)
        RF.first-coordinate RF.first-coordinate) (identity-expression (pr₁ {N.Y} {C}))
    right-identity = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E RF.first-coordinate)
      (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E (pr₁ {N.Y} {D}) RF.W)
        RF.first-coordinate RF.first-coordinate)

    unit-coordinate : LF.nested-coordinate =₂ Unit.target-change
    unit-coordinate = isoComp-assoc-at (r ◁ (l ◁ LF.second-coordinate))
        (r ◁ comp-assoc LF.W pr₂ l) (comp-assoc LF.W (l ∘ pr₂) r) ∙
      isoComp-cong (postWhisker-isoComp-at r (l ◁ LF.second-coordinate) (comp-assoc LF.W pr₂ l))
        (idIso (comp-assoc LF.W (l ∘ pr₂) r))

    counit-coordinate : RF.nested-coordinate =₂ Counit.source-change
    counit-coordinate = isoComp-assoc-at (l ◁ (r ◁ RF.second-coordinate))
        (l ◁ comp-assoc RF.W pr₂ r) (comp-assoc RF.W (r ∘ pr₂) l) ∙
      isoComp-cong (postWhisker-isoComp-at l (r ◁ RF.second-coordinate) (comp-assoc RF.W pr₂ r))
        (idIso (comp-assoc RF.W (r ∘ pr₂) l))

    unit-component : ExpressionIso
      (retarget-expression (restrict-expression (A.unit-at (pr₂ {N.X} {C})) LF.W)
        LF.second-coordinate LF.nested-coordinate) (A.unit-at (r ∘ pr₂ {N.X} {D}))
    unit-component = expressionIso-compose Unit.value
      (retarget-cong (restrict-expression (A.unit-at (pr₂ {N.X} {C})) LF.W)
        (idIso LF.second-coordinate) unit-coordinate)

    counit-component : ExpressionIso
      (retarget-expression (restrict-expression (A.counit-at (pr₂ {N.Y} {D})) RF.W)
        RF.nested-coordinate RF.second-coordinate) (A.counit-at (l ∘ pr₂ {N.Y} {C}))
    counit-component = expressionIso-compose Counit.value
      (retarget-cong (restrict-expression (A.counit-at (pr₂ {N.Y} {D})) RF.W)
        counit-coordinate (idIso RF.second-coordinate))

  module Left = Paired.At 𝒯 M ℱ P I E S
    (identity-expression (pr₁ {N.X} {C})) (A.unit-at pr₂) LF.W N.e
    LF.first-coordinate LF.first-coordinate LF.second-coordinate LF.nested-coordinate left-identity unit-component
  module Right = Paired.At 𝒯 M ℱ P I E S
    (identity-expression (pr₁ {N.Y} {D})) (A.counit-at pr₂) RF.W N.d
    RF.first-coordinate RF.first-coordinate RF.nested-coordinate RF.second-coordinate right-identity counit-component
```
