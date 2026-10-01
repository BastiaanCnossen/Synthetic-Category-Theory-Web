# Composition of primitive identifications as morphisms

A constant arrow with changed endpoint identifications represents a
primitive identification. Retarget a unit triangle by the three vertex
identifications `id`, `α`, and `β ∙ α`. Its short edges represent `α`
and `β`, and its long edge represents their composite. Every comparison
below retains the two original endpoint frames.

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

module SCT.VolumeI.Chapter02.Section02.PrimitiveIdentificationComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdChange

module At {Γ C : CAT} {x y z : MAP Γ C} (α : x =₁ y) (β : y =₁ z) where
  module X = MorphismExpression (identity-expression x)
    using (arrow; source-frame; target-frame)
  module Y = MorphismExpression (identity-expression y)
    using (target-frame)
  module Change = ExpressionIso (IdChange.At.comparison 𝒯 M ℱ P I E α)
    using (comparison; source-compatible; target-compatible)

  normalized : {v : MAP Γ C} (γ : x =₁ v) →
    ExpressionIso (retarget-expression (identity-expression x) (idIso x) γ)
      (isomorphism-expression γ)
  normalized γ = record
    { comparison = idIso X.arrow
    ; source-compatible = (isoComp-unitˡ-at X.source-frame) ⁻¹ ∙
        (isoComp-unitʳ-at X.source-frame ∙
          isoComp-cong (idIso X.source-frame) (postWhisker-idIso ev₀ X.arrow))
    ; target-compatible = isoComp-unitʳ-at (γ ∙ X.target-frame) ∙
        isoComp-cong (idIso (γ ∙ X.target-frame)) (postWhisker-idIso ev₁ X.arrow) }

  second-comparison : ExpressionIso
    (retarget-expression (identity-expression x) α (β ∙ α))
    (isomorphism-expression β)
  second-comparison = record
    { comparison = Change.comparison
    ; source-compatible = Change.source-compatible
    ; target-compatible = (isoComp-assoc-at β α X.target-frame) ⁻¹ ∙
        (isoComp-cong (idIso β) Change.target-compatible ∙
          isoComp-assoc-at β Y.target-frame (ev₁ ◁ Change.comparison)) }

  comparison : ExpressionIso
    (compose-expression (isomorphism-expression α) (isomorphism-expression β))
    (isomorphism-expression (β ∙ α))
  comparison = expressionIso-compose (normalized (β ∙ α))
    (expressionIso-compose
      (retarget-expressionIso (left-unit (identity-expression x)) (idIso x) (β ∙ α))
      (expressionIso-compose
        (retarget-composition (identity-expression x) (identity-expression x) (idIso x) α (β ∙ α))
        (expressionIso-inverse (compose-expression-cong (normalized α) second-comparison))))

identification-composition : {Γ C : CAT} {x y z : MAP Γ C}
  (α : x =₁ y) (β : y =₁ z) →
  ExpressionIso (compose-expression (isomorphism-expression α) (isomorphism-expression β))
    (isomorphism-expression (β ∙ α))
identification-composition = At.comparison
```
