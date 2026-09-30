# Evaluating a postcomposed functor-valued transformation

For any functor with values in a functor category, evaluation of its action on
a transformation agrees with applying its uncurried functor to the paired
transformation. The endpoint comparisons are the chosen uncurrying
restriction comparisons.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc; retarget-cong; retarget-cancel; retarget-move)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I using (restrict-post)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E using (post-composite)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E using (post-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFunctoriality as Products
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitutionPairing as Normalization
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames as Inverse

module At {Γ X A D : CAT} (L : MAP A (Fun X D))
  {f g : MAP Γ A} (α : MorphismExpression f g) where
  fixed : MAP (Γ × X) X
  fixed = id X ∘ pr₂
  original = restrict-expression α (pr₁ {Γ} {X})
  constant = identity-expression fixed
  paired = pair-expression original constant
  J : MAP (A × X) (Fun X D × X)
  J = productMap L (id X)
  module Source = Normalization.At 𝒯 M X L f
  module Target = Normalization.At 𝒯 M X L g
  module Product = Products.At 𝒯 M ℱ P I E S L (id X) original constant
  module PairFrames = Frames.At 𝒯 M ℱ I (post-expression L original) (post-expression (id X) constant)
    Source.first-frame Target.first-frame Source.second-frame Target.second-frame

  abstract
    first : ExpressionIso (retarget-expression (post-expression L original) Source.first-frame Target.first-frame)
      (restrict-expression (post-expression L α) pr₁)
    first = expressionIso-compose
      (retarget-cancel (restrict-expression (post-expression L α) pr₁)
        (comp-assoc pr₁ f L) (comp-assoc pr₁ g L))
      (retarget-expressionIso (expressionIso-inverse (restrict-post L α pr₁)) Source.first-frame Target.first-frame)

    paired-comparison : ExpressionIso (retarget-expression (post-expression J paired)
        (slice-comparison L f) (slice-comparison L g))
      (pair-expression (restrict-expression (post-expression L α) pr₁) constant)
    paired-comparison = expressionIso-compose (pair-expression-cong first (post-id constant))
      (expressionIso-compose PairFrames.value
        (expressionIso-compose (retarget-expressionIso Product.value
            (pair-cong Source.first-frame Source.second-frame) (pair-cong Target.first-frame Target.second-frame))
          (expressionIso-compose
            (expressionIso-inverse (retarget-assoc (post-expression J paired)
              (productMap-pair L (id X) (f ∘ pr₁) fixed) (productMap-pair L (id X) (g ∘ pr₁) fixed)
              (pair-cong Source.first-frame Source.second-frame) (pair-cong Target.first-frame Target.second-frame)))
            (retarget-cong (post-expression J paired) (Source.comparison ⁻¹) (Target.comparison ⁻¹)))))

  module Endpoint (h : MAP Γ A) where
    module Inv = Inverse.At 𝒯 M ℱ L h (idIso (L ∘ h))
    change : (funUncurry L ∘ productMap h (id X)) =₁ funUncurry (L ∘ h)
    change = (funEval ◁ slice-comparison L h) ∙ comp-assoc (productMap h (id X)) J funEval
    normalization : (funUncurry-restrict L h) ⁻¹ =₂ change
    normalization = Inv.inverse-restriction

  abstract
    value : ExpressionIso (retarget-expression (post-expression (funUncurry L) paired)
        ((funUncurry-restrict L f) ⁻¹) ((funUncurry-restrict L g) ⁻¹))
      (uncurry-expression (post-expression L α))
    value = expressionIso-compose (post-expressionIso funEval paired-comparison)
      (expressionIso-compose (expressionIso-inverse (post-retarget funEval (post-expression J paired)
          (slice-comparison L f) (slice-comparison L g)))
        (expressionIso-compose (retarget-expressionIso (post-composite J funEval paired)
            (funEval ◁ slice-comparison L f) (funEval ◁ slice-comparison L g))
          (expressionIso-compose
            (expressionIso-inverse (retarget-assoc (post-expression (funUncurry L) paired)
              (comp-assoc (productMap f (id X)) J funEval) (comp-assoc (productMap g (id X)) J funEval)
              (funEval ◁ slice-comparison L f) (funEval ◁ slice-comparison L g)))
            (retarget-cong (post-expression (funUncurry L) paired) (Endpoint.normalization f) (Endpoint.normalization g)))))

    comparison : ExpressionIso (retarget-expression (uncurry-expression (post-expression L α))
        (funUncurry-restrict L f) (funUncurry-restrict L g))
      (post-expression (funUncurry L) paired)
    comparison = retarget-move (funUncurry-restrict L f) (funUncurry-restrict L g) value
```
