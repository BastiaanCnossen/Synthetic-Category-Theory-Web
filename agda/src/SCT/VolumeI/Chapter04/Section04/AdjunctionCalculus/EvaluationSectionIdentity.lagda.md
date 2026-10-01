# Recognizing the identity on the constant-arrow section

A transformation of the constant-arrow section with constant underlying
diagram is invertible by Rezk. If its evaluated expression is the
identity, evaluation reflects the recovered identification. The conclusion
retains both endpoint frames of the original transformation.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationSectionIdentity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.RezkRecovery 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-post; isomorphism-id; isomorphism-cong)
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison as ConstantIdentity
open ConstantIdentity 𝒯 M ℱ P I E using (constant-isomorphism-comparison)
open import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.IdentificationUniqueness 𝒯 M ℱ P I E S Q R
  using (constant-identification-reflect)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationScalarReflection as Reflection

module At {C : CAT} (p : MAP (Ar C) C) (ρ : (p ∘ identityArrow) =₁ id C)
  (f : MorphismExpression (identityArrow {C}) identityArrow)
  (θ : funUncurry (MorphismExpression.arrow f) =₁ (identityArrow ∘ pr₁)) where
  private
    s = identityArrow {C}
    h = MorphismExpression.arrow f
    module Constant = ConstantIdentity.At 𝒯 M ℱ P I E s
    δ : (identityArrow ∘ s) =₁ h
    δ = funIsoReflect (identityArrow ∘ s) h (θ ⁻¹ ∙ Constant.θ)

  abstract
    lift : IsoLift h
    lift = record
      { lift = identityIso ∘ s
      ; comparison = δ ∙ ((identityIso-arrow ▷ s) ∙ (comp-assoc s identityIso isoArrow) ⁻¹) }

  module Found = Recover f lift

  module Evaluated (normal : ExpressionIso (post-expression p f) (identity-expression (p ∘ s))) where
    private
      χ = Found.identification

    abstract
      image-identity : (p ◁ χ) =₂ idIso (p ∘ s)
      image-identity = constant-identification-reflect (p ◁ χ) (idIso (p ∘ s))
        (expressionIso-compose
          (expressionIso-inverse (constant-isomorphism-comparison (idIso (p ∘ s))))
          (expressionIso-compose (expressionIso-inverse (isomorphism-id (p ∘ s)))
            (expressionIso-compose normal
              (expressionIso-compose (post-expressionIso p Found.isomorphism-recovery)
                (expressionIso-compose (expressionIso-inverse (isomorphism-post p χ))
                  (constant-isomorphism-comparison (p ◁ χ)))))))

      identification-identity : χ =₂ idIso s
      identification-identity = Reflection.At.section-reflect 𝒯 M ℱ P I E S Q R p ρ χ (idIso s)
        ((postWhisker-idIso p s) ⁻¹ ∙ image-identity)

      comparison : ExpressionIso f (identity-expression s)
      comparison = expressionIso-compose (isomorphism-id s)
        (expressionIso-compose (isomorphism-cong identification-identity)
          (expressionIso-inverse Found.isomorphism-recovery))
```
