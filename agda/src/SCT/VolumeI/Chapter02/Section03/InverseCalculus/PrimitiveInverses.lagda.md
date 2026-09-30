# Inverse equations for primitive identifications

The expressions associated to an identification and its inverse compose
to the identity expressions, with their specified endpoint frames. This
also supplies a triangle identity whenever two expressions have been
identified with these inverse expressions.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.PrimitiveInverses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-cong; isomorphism-id)
open import SCT.VolumeI.Chapter02.Section02.PrimitiveIdentificationComposition 𝒯 M ℱ P I E S
  using (identification-composition)

abstract
  identification-left-inverse : {Γ C : CAT} {x y : MAP Γ C} (α : x =₁ y) →
    ExpressionIso (compose-expression (isomorphism-expression α) (isomorphism-expression (α ⁻¹)))
      (identity-expression x)
  identification-left-inverse {x = x} α = expressionIso-compose (isomorphism-id x)
    (expressionIso-compose (isomorphism-cong (isoComp-inverseˡ-at α))
      (identification-composition α (α ⁻¹)))

  identification-right-inverse : {Γ C : CAT} {x y : MAP Γ C} (α : x =₁ y) →
    ExpressionIso (compose-expression (isomorphism-expression (α ⁻¹)) (isomorphism-expression α))
      (identity-expression y)
  identification-right-inverse {y = y} α = expressionIso-compose (isomorphism-id y)
    (expressionIso-compose (isomorphism-cong (isoComp-inverseʳ-at α))
      (identification-composition (α ⁻¹) α))

  identification-invertible : {Γ C : CAT} {x y : MAP Γ C} (α : x =₁ y) →
    IsInvertibleExpression (isomorphism-expression α)
  identification-invertible α = record
    { right-inverse = isomorphism-expression (α ⁻¹)
    ; left-inverse = isomorphism-expression (α ⁻¹)
    ; right-inverse-law = identification-right-inverse α
    ; left-inverse-law = identification-left-inverse α }

  identified-inverse-triangle : {Γ C : CAT} {x y : MAP Γ C}
    (α : x =₁ y) (f : MorphismExpression x y) (g : MorphismExpression y x) →
    ExpressionIso f (isomorphism-expression α) →
    ExpressionIso g (isomorphism-expression (α ⁻¹)) →
    ExpressionIso (compose-expression f g) (identity-expression x)
  identified-inverse-triangle α f g first second = expressionIso-compose
    (identification-left-inverse α) (compose-expression-cong first second)
```
