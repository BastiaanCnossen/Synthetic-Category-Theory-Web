# Hom composition detects invertible morphisms

For postcomposition, lift the identity at the target to obtain a right
inverse. Reflect the other inverse equation using the test at the source.
Precomposition gives the dual argument. Only these two object tests are needed.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section06.HomCompositionDetection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.ExpressionCancellation 𝒯 M ℱ P I E S Q using (module InverseEquation; compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S using (invertible-expression-lift)
open import SCT.VolumeI.Chapter02.Section03.UniversalInverseExpressions 𝒯 M ℱ P I E S using (IsInvertibleExpression; IsoLift)

module Detect {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  module F = At e
  f = F.family One
  identity-x = identity-expression (const {P = One} x)
  identity-y = identity-expression (const {P = One} y)

  post-intro : {z : Obj-abs C} (h : MorphismExpression (const {P = One} z) (const x)) →
    ExpressionIso (hom-expression (F.postcompose z ∘ hom-intro h)) (compose-expression h f)
  post-intro h = expressionIso-compose (compose-expression-cong (hom-β h) (expressionIso-id f))
    (F.postcompose-β _ (hom-intro h))

  pre-intro : {z : Obj-abs C} (h : MorphismExpression (const {P = One} y) (const z)) →
    ExpressionIso (hom-expression (F.precompose z ∘ hom-intro h)) (compose-expression f h)
  pre-intro h = expressionIso-compose (compose-expression-cong (expressionIso-id f) (hom-β h))
    (F.precompose-β _ (hom-intro h))

  point-lift : IsInvertibleExpression f → IsoLift (MorphismExpression.arrow (hom-expression e))
  point-lift w = record { lift = IsoLift.lift lifted
    ; comparison = ExpressionIso.comparison F.family-at-point ∙ IsoLift.comparison lifted }
    where lifted = invertible-expression-lift f w

  module FromPost (at-source : IsEquiv (F.postcompose x)) (at-target : IsEquiv (F.postcompose y)) where
    lifted-identity = equiv-lift at-target (hom-intro identity-y)
    g = hom-expression (FunctorLift.lift lifted-identity)

    right-law : ExpressionIso (compose-expression g f) identity-y
    right-law = expressionIso-compose (hom-β identity-y)
      (expressionIso-compose (hom-expression-cong (FunctorLift.comparison lifted-identity))
        (expressionIso-inverse (F.postcompose-β y (FunctorLift.lift lifted-identity))))

    module Right = InverseEquation g f right-law
    candidate = compose-expression f g

    same-image : (F.postcompose x ∘ hom-intro candidate) =₁ (F.postcompose x ∘ hom-intro identity-x)
    same-image = hom-reflect (expressionIso-compose
      (expressionIso-inverse (expressionIso-compose (left-unit f) (post-intro identity-x)))
      (expressionIso-compose (Right.cancel-after f) (post-intro candidate)))

    left-law : ExpressionIso candidate identity-x
    left-law = hom-intro-reflect (equiv-reflect at-source (hom-intro candidate) (hom-intro identity-x) same-image)

    inverse-data : IsInvertibleExpression f
    inverse-data = record { right-inverse = g ; left-inverse = g
      ; right-inverse-law = right-law ; left-inverse-law = left-law }

    lift : IsoLift (MorphismExpression.arrow (hom-expression e))
    lift = point-lift inverse-data

  module FromPre (at-source : IsEquiv (F.precompose x)) (at-target : IsEquiv (F.precompose y)) where
    lifted-identity = equiv-lift at-source (hom-intro identity-x)
    g = hom-expression (FunctorLift.lift lifted-identity)

    left-law : ExpressionIso (compose-expression f g) identity-x
    left-law = expressionIso-compose (hom-β identity-x)
      (expressionIso-compose (hom-expression-cong (FunctorLift.comparison lifted-identity))
        (expressionIso-inverse (F.precompose-β x (FunctorLift.lift lifted-identity))))

    module Left = InverseEquation f g left-law
    candidate = compose-expression g f

    same-image : (F.precompose y ∘ hom-intro candidate) =₁ (F.precompose y ∘ hom-intro identity-y)
    same-image = hom-reflect (expressionIso-compose
      (expressionIso-inverse (expressionIso-compose (right-unit f) (pre-intro identity-y)))
      (expressionIso-compose (Left.cancel-before f) (pre-intro candidate)))

    right-law : ExpressionIso candidate identity-y
    right-law = hom-intro-reflect (equiv-reflect at-target (hom-intro candidate) (hom-intro identity-y) same-image)

    inverse-data : IsInvertibleExpression f
    inverse-data = record { right-inverse = g ; left-inverse = g
      ; right-inverse-law = right-law ; left-inverse-law = left-law }

    lift : IsoLift (MorphismExpression.arrow (hom-expression e))
    lift = point-lift inverse-data
```
