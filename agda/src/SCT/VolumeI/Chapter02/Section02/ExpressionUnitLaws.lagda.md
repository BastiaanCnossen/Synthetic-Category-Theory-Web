# The unit laws with specified endpoints

Restrict the universal degenerate triangles along the arrow functor of
an expression. Restore its endpoint frames, identify the restricted
identity diagrams, and apply uniqueness of a composite presentation.
The resulting identifications preserve both specified endpoints, as required
by `lem:Composition_Is_Unital`.

`compose-expression f g` denotes the composite that first follows `f`,
then `g`. Here `left-unit` and `right-unit` refer to the position of the
identity in this argument list. The two endpoint claims are the
`source-compatible` and `target-compatible` fields of each `ExpressionIso`.

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

module SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GlobalCompositionExpressions 𝒯 M ℱ P I E S
  using (global-compose-expression; global-composition-comparison)
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitPresentations as Universal
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationSubstitution as Presentations
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.UniversalArrowSubstitution as Arrow
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityRetargeting

module At {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) where
  module F = MorphismExpression f
  module U = Universal.Universal 𝒯 M ℱ P I E S C
  module RestrictedArrow = Arrow.At 𝒯 M ℱ P I E f
    using (comparison)

  identity-comparison : (v : MAP (Ar C) C) {z : MAP Γ C} (b : (v ∘ F.arrow) =₁ z) →
    ExpressionIso
      (retarget-expression (restrict-expression (identity-expression v) F.arrow) b b)
      (identity-expression z)
  identity-comparison v b = expressionIso-compose
    (IdentityRetargeting.At.comparison 𝒯 M ℱ P I E b)
    (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E v F.arrow) b b)

  module Left where
    module Restricted = Presentations.Restrict 𝒯 M ℱ P I E S U.Left.presentation F.arrow
    module Reframed = Presentations.Retarget 𝒯 M ℱ P I E S Restricted.value
      F.source-frame F.source-frame F.target-frame
      using (value)

    comparison : ExpressionIso (compose-expression (identity-expression x) f) f
    comparison = expressionIso-compose RestrictedArrow.comparison
      (expressionIso-compose (recognize-composite Reframed.value)
        (expressionIso-inverse (compose-expression-cong
          (identity-comparison ev₀ F.source-frame) RestrictedArrow.comparison)))

  module Right where
    module Restricted = Presentations.Restrict 𝒯 M ℱ P I E S U.Right.presentation F.arrow
    module Reframed = Presentations.Retarget 𝒯 M ℱ P I E S Restricted.value
      F.source-frame F.target-frame F.target-frame
      using (value)

    comparison : ExpressionIso (compose-expression f (identity-expression y)) f
    comparison = expressionIso-compose RestrictedArrow.comparison
      (expressionIso-compose (recognize-composite Reframed.value)
        (expressionIso-inverse (compose-expression-cong RestrictedArrow.comparison
          (identity-comparison ev₁ F.target-frame))))

left-unit : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (compose-expression (identity-expression x) f) f
left-unit = At.Left.comparison

right-unit : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (compose-expression f (identity-expression y)) f
right-unit = At.Right.comparison

global-left-unit : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (global-compose-expression (identity-expression x) f) f
global-left-unit f = expressionIso-compose (left-unit f)
  (global-composition-comparison (identity-expression _) f)

global-right-unit : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (global-compose-expression f (identity-expression y)) f
global-right-unit f = expressionIso-compose (right-unit f)
  (global-composition-comparison f (identity-expression _))
```
