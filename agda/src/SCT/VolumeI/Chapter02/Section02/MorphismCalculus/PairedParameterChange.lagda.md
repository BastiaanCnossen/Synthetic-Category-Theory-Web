# Parameter change for a paired component

A natural component in the second coordinate commutes with a change of
parameter in the first coordinate. The comparison uses specified endpoint
frames and reflects their equality after product normalization.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PairedParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong; retarget-id)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong; retarget-reflect)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E using (post-id)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedPairRestriction as Restriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFunctoriality as Functoriality
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames

module At {X Y A B : CAT} (h : MAP X Y)
  {uY vY : MAP (Y × A) B} {uX vX : MAP (X × A) B}
  (βY : MorphismExpression uY vY) (βX : MorphismExpression uX vX)
  (r : (uY ∘ productMap h (id A)) =₁ uX)
  (s : (vY ∘ productMap h (id A)) =₁ vX)
  (ζ : ExpressionIso (retarget-expression (restrict-expression βY (productMap h (id A))) r s) βX) where
  σ = productMap h (id A)
  HB = productMap h (id B)
  ρ₁ = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)
  γY = pair-expression (identity-expression pr₁) βY
  γX = pair-expression (identity-expression pr₁) βX
  common = pair-expression (identity-expression (h ∘ pr₁)) βX

  abstract
    first-restricted : ExpressionIso
      (retarget-expression (restrict-expression (identity-expression (pr₁ {Y} {A})) σ) ρ₁ ρ₁)
      (identity-expression (h ∘ pr₁))
    first-restricted = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E ρ₁)
      (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E pr₁ σ) ρ₁ ρ₁)

  module Restricted = Restriction.At 𝒯 M ℱ P I E S (identity-expression pr₁) βY σ (id (Y × B))
    ρ₁ ρ₁ r s first-restricted ζ
    using (paired; source-product; target-product)
  source-change = pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ uX)
  target-change = pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ vX)
  source-frame = source-change ∙ productMap-pair h (id B) pr₁ uX
  target-frame = target-change ∙ productMap-pair h (id B) pr₁ vX
  module Mapped = Functoriality.At 𝒯 M ℱ P I E S h (id B) (identity-expression pr₁) βX
    using (value)
  module ProductFrames = Frames.At 𝒯 M ℱ I (post-expression h (identity-expression pr₁)) (post-expression (id B) βX)
    (idIso (h ∘ pr₁)) (idIso (h ∘ pr₁)) (comp-unitˡ uX) (comp-unitˡ vX)
    using (value)

  abstract
    first-mapped : ExpressionIso
      (retarget-expression (post-expression h (identity-expression (pr₁ {X} {A})))
        (idIso (h ∘ pr₁)) (idIso (h ∘ pr₁))) (identity-expression (h ∘ pr₁))
    first-mapped = expressionIso-compose (post-identity h pr₁)
      (retarget-id (post-expression h (identity-expression pr₁)))

    mapped : ExpressionIso (retarget-expression (post-expression HB γX) source-frame target-frame) common
    mapped = expressionIso-compose (pair-expression-cong first-mapped (post-id βX))
      (expressionIso-compose ProductFrames.value
        (expressionIso-compose (retarget-expressionIso Mapped.value source-change target-change)
          (expressionIso-inverse (retarget-assoc (post-expression HB γX)
            (productMap-pair h (id B) pr₁ uX) (productMap-pair h (id B) pr₁ vX) source-change target-change))))

    value : (νₛ : (pair pr₁ uY ∘ σ) =₁ (HB ∘ pair pr₁ uX))
      (νₜ : (pair pr₁ vY ∘ σ) =₁ (HB ∘ pair pr₁ vX)) →
      (source-frame ∙ νₛ) =₂ Restricted.source-product →
      (target-frame ∙ νₜ) =₂ Restricted.target-product →
      ExpressionIso (retarget-expression (restrict-expression γY σ) νₛ νₜ) (post-expression HB γX)
    value νₛ νₜ source-square target-square = retarget-reflect source-frame target-frame
      (expressionIso-compose (expressionIso-inverse mapped)
        (expressionIso-compose Restricted.paired
          (expressionIso-compose (retarget-cong (restrict-expression γY σ) source-square target-square)
            (retarget-assoc (restrict-expression γY σ) νₛ νₜ source-frame target-frame))))
```
