# Uniqueness of inverse expressions

A right inverse and a left inverse of the same expression agree. Thus a
specified one-sided inverse of an invertible expression is itself
invertible. These comparisons use associativity and the unit laws, and
retain the two endpoints throughout.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionInverseLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  public using (CAT; MAP; MorphismExpression; ExpressionIso; IsInvertibleExpression;
    compose-expression; identity-expression; identified-invertible)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S
  using (left-unit)
open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q
  using (associativity)
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.ExpressionCancellation 𝒯 M ℱ P I E S Q
  using (module InverseEquation)

inverse-comparison : {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (r l : MorphismExpression y x) →
  ExpressionIso (compose-expression r f) (identity-expression y) →
  ExpressionIso (compose-expression f l) (identity-expression x) → ExpressionIso r l
inverse-comparison f r l right-law left-law = expressionIso-compose (left-unit l)
  (expressionIso-compose (compose-expression-cong right-law (expressionIso-id l))
    (expressionIso-inverse (InverseEquation.cancel-after f l left-law r)))

module Inverses {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (w : IsInvertibleExpression f) where
  private module W = IsInvertibleExpression w

  comparison : ExpressionIso W.right-inverse W.left-inverse
  comparison = inverse-comparison f W.right-inverse W.left-inverse
    W.right-inverse-law W.left-inverse-law

  right-inverse-invertible : IsInvertibleExpression W.right-inverse
  right-inverse-invertible = record
    { right-inverse = f
    ; left-inverse = f
    ; right-inverse-law = expressionIso-compose W.left-inverse-law
        (compose-expression-cong (expressionIso-id f) comparison)
    ; left-inverse-law = W.right-inverse-law }

  left-inverse-invertible : IsInvertibleExpression W.left-inverse
  left-inverse-invertible = identified-invertible comparison right-inverse-invertible

  any-left-inverse-invertible : (g : MorphismExpression y x) →
    ExpressionIso (compose-expression f g) (identity-expression x) → IsInvertibleExpression g
  any-left-inverse-invertible g law = identified-invertible
    (inverse-comparison f W.right-inverse g W.right-inverse-law law) right-inverse-invertible

  any-right-inverse-invertible : (g : MorphismExpression y x) →
    ExpressionIso (compose-expression g f) (identity-expression y) → IsInvertibleExpression g
  any-right-inverse-invertible g law = identified-invertible
    (expressionIso-inverse (inverse-comparison f g W.left-inverse law W.left-inverse-law))
    left-inverse-invertible

compose-invertible : {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) →
  IsInvertibleExpression f → IsInvertibleExpression g →
  IsInvertibleExpression (compose-expression f g)
compose-invertible f g ef eg = record
  { right-inverse = compose-expression G.right-inverse F.right-inverse
  ; left-inverse = compose-expression G.left-inverse F.left-inverse
  ; right-inverse-law = expressionIso-compose G.right-inverse-law
      (expressionIso-compose
        (compose-expression-cong (expressionIso-id G.right-inverse)
          (InverseEquation.cancel-before F.right-inverse f F.right-inverse-law g))
        (expressionIso-inverse (associativity G.right-inverse F.right-inverse (compose-expression f g))))
  ; left-inverse-law = expressionIso-compose F.left-inverse-law
      (expressionIso-compose
        (compose-expression-cong (expressionIso-id f)
          (InverseEquation.cancel-before g G.left-inverse G.left-inverse-law F.left-inverse))
        (expressionIso-inverse (associativity f g (compose-expression G.left-inverse F.left-inverse)))) }
  where
  module F = IsInvertibleExpression ef
  module G = IsInvertibleExpression eg
```
