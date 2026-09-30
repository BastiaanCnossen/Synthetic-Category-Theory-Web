# Recognizing identity expressions from their diagrams

A constant uncurried diagram identifies an expression with the identity
when both specified endpoint frames agree with that same comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFromDiagram
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles 𝒯 M ℱ P I E using (module ReflectedEndpoint)

module At {Γ C : CAT} {x : MAP Γ C}
  (f : MorphismExpression x x)
  (θ : funUncurry (MorphismExpression.arrow f) =₁ (x ∘ pr₁)) where
  private
    h k : MAP Γ (Ar C)
    h = MorphismExpression.arrow f
    k = MorphismExpression.arrow (identity-expression x)
    β : funUncurry k =₁ (x ∘ pr₁ {Γ} {[1]})
    β = funCurry-β (x ∘ pr₁ {Γ} {[1]})
    δ : h =₁ k
    δ = funIsoReflect h k (β ⁻¹ ∙ θ)

  endpoint : (v : Obj-abs [1]) (r : (evaluate v ∘ h) =₁ x) →
    r =₂ (identity-boundary v x ∙ ((θ ▷ insert v) ∙ evaluate-uncurry v h)) →
    ((identity-boundary v x ∙ evaluate-curry v (x ∘ pr₁)) ∙ (evaluate v ◁ δ)) =₂ r
  endpoint v r same = same ⁻¹ ∙
    (isoComp-cong (idIso (identity-boundary v x))
      (ReflectedEndpoint.endpoint v h k β θ δ (funIsoReflect-β h k (β ⁻¹ ∙ θ))) ∙
      isoComp-assoc-at (identity-boundary v x) (evaluate-curry v (x ∘ pr₁)) (evaluate v ◁ δ))

  comparison :
    MorphismExpression.source-frame f =₂
      (identity-boundary zero x ∙ ((θ ▷ insert zero) ∙ evaluate-uncurry zero h)) →
    MorphismExpression.target-frame f =₂
      (identity-boundary one x ∙ ((θ ▷ insert one) ∙ evaluate-uncurry one h)) →
    ExpressionIso f (identity-expression x)
  comparison source target = record
    { comparison = δ
    ; source-compatible = endpoint zero (MorphismExpression.source-frame f) source
    ; target-compatible = endpoint one (MorphismExpression.target-frame f) target }
```
