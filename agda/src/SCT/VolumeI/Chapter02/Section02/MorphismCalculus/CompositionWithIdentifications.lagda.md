# Composition with an endpoint identification

Composition with a primitive identification agrees with changing the
corresponding endpoint frame. Normalize the identification as a retargeted identity, use
compatibility of composition with endpoint changes, and apply the right
unit law. The comparison retains both endpoint equations.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionWithIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-normal; framed-identity; isomorphism-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S
  using (right-unit; left-unit)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)

abstract
  postcompose-identification : {Γ C : CAT} {x y z : MAP Γ C}
    (f : MorphismExpression x y) (κ : y =₁ z) →
    ExpressionIso (compose-expression f (isomorphism-expression κ))
      (retarget-expression f (idIso x) κ)
  postcompose-identification {x = x} {y} f κ = expressionIso-compose
    (retarget-expressionIso (right-unit f) (idIso x) κ)
    (expressionIso-compose
      (retarget-composition f (identity-expression y) (idIso x) (idIso y) κ)
      (compose-expression-cong (expressionIso-inverse (retarget-id f))
        (expressionIso-inverse (isomorphism-normal κ))))

  precompose-identification : {Γ C : CAT} {x y z : MAP Γ C}
    (κ : x =₁ y) (f : MorphismExpression y z) →
    ExpressionIso (compose-expression (isomorphism-expression κ) f)
      (retarget-expression f (κ ⁻¹) (idIso z))
  precompose-identification {y = y} {z} κ f = expressionIso-compose
    (retarget-expressionIso (left-unit f) (κ ⁻¹) (idIso z))
    (expressionIso-compose
      (retarget-composition (identity-expression y) f (κ ⁻¹) (idIso y) (idIso z))
      (compose-expression-cong (expressionIso-inverse identity-comparison)
        (expressionIso-inverse (retarget-id f))))
    where
    identity-comparison : ExpressionIso
      (retarget-expression (identity-expression y) (κ ⁻¹) (idIso y))
      (isomorphism-expression κ)
    identity-comparison = expressionIso-compose
      (isomorphism-cong (inverse-inverse κ ∙ isoComp-unitˡ-at ((κ ⁻¹) ⁻¹)))
      (framed-identity (κ ⁻¹) (idIso y))
```
