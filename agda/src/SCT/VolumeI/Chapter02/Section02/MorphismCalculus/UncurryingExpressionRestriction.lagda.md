# Restriction commutes with uncurrying

Restrict a functor-valued transformation and then evaluate, or evaluate
first and restrict along the product parameter map. The two expressions
agree with the chosen uncurrying restriction comparisons at their endpoints.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-move)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionRestriction as Products
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionSquare as Square
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames as UncurriedFrames

module At {Γ Δ X C : CAT} {f g : MAP Γ (Fun X C)}
  (α : MorphismExpression f g) (r : MAP Δ Γ) where
  σ : MAP (Δ × X) (Γ × X)
  σ = productMap r (id X)
  fixed : MAP (Γ × X) X
  fixed = id X ∘ pr₂
  original = restrict-expression α (pr₁ {Γ} {X})
  constant = identity-expression fixed
  paired = pair-expression original constant
  module Source = Substitution.Coordinates 𝒯 M X f r
    using (first; normalized; second)
  module Target = Substitution.Coordinates 𝒯 M X g r
  second : (fixed ∘ σ) =₁ (id X ∘ pr₂ {Δ} {X})
  second = Source.second
  first-coordinate : (pr₁ ∘ σ) =₁ (r ∘ pr₁ {Δ} {X})
  first-coordinate = pair-β₁ (r ∘ pr₁) (id X ∘ pr₂)
  module First = Square.At 𝒯 M ℱ I α (pr₁ {Γ} {X}) σ r (pr₁ {Δ} {X}) first-coordinate
    using (value)
  module PairRestriction = Products.At 𝒯 M ℱ P I E S original constant σ
    using (value)
  module PairFrames = Frames.At 𝒯 M ℱ I (restrict-expression original σ) (restrict-expression constant σ)
    Source.first Target.first second second
    using (value)

  abstract
    constant-comparison : ExpressionIso (retarget-expression (restrict-expression constant σ) second second)
      (identity-expression (id X ∘ pr₂ {Δ} {X}))
    constant-comparison = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E second)
      (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E fixed σ) second second)

    paired-comparison : ExpressionIso
      (retarget-expression (restrict-expression paired σ) Source.normalized Target.normalized)
      (pair-expression (restrict-expression (restrict-expression α r) pr₁)
        (identity-expression (id X ∘ pr₂ {Δ} {X})))
    paired-comparison = expressionIso-compose (pair-expression-cong First.value constant-comparison)
      (expressionIso-compose PairFrames.value
        (expressionIso-compose
          (retarget-expressionIso PairRestriction.value
            (pair-cong Source.first second) (pair-cong Target.first second))
          (expressionIso-inverse (retarget-assoc (restrict-expression paired σ)
            (pair-pre (f ∘ pr₁) fixed σ) (pair-pre (g ∘ pr₁) fixed σ)
            (pair-cong Source.first second) (pair-cong Target.first second)))))

  module Frame (h : MAP Γ (Fun X C)) where
    module Product = Substitution.Coordinates 𝒯 M X h r
      using (normalization; normalized)
    module Uncurried = UncurriedFrames.At 𝒯 M ℱ h r (idIso (h ∘ r))
      using (inverse-restriction)
    change : (funUncurry h ∘ σ) =₁ funUncurry (h ∘ r)
    change = (funEval ◁ Product.normalized) ∙ comp-assoc σ (productMap h (id X)) funEval
    normalization : (funUncurry-restrict h r) ⁻¹ =₂ change
    normalization = isoComp-cong (postWhisker funEval ◁ Product.normalization)
      (idIso (comp-assoc σ (productMap h (id X)) funEval)) ∙ Uncurried.inverse-restriction

  abstract
    value : ExpressionIso
      (retarget-expression (restrict-expression (uncurry-expression α) σ)
        ((funUncurry-restrict f r) ⁻¹) ((funUncurry-restrict g r) ⁻¹))
      (uncurry-expression (restrict-expression α r))
    value = expressionIso-compose (post-expressionIso funEval paired-comparison)
      (expressionIso-compose (restrict-post-frames funEval paired σ Source.normalized Target.normalized)
        (retarget-cong (restrict-expression (uncurry-expression α) σ) (Frame.normalization f) (Frame.normalization g)))

    comparison : ExpressionIso
      (retarget-expression (uncurry-expression (restrict-expression α r))
        (funUncurry-restrict f r) (funUncurry-restrict g r))
      (restrict-expression (uncurry-expression α) σ)
    comparison = retarget-move (funUncurry-restrict f r) (funUncurry-restrict g r) value
```
