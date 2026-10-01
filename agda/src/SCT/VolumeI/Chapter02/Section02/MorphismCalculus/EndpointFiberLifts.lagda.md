# Lifting comparisons and restrictions of expressions

The endpoint pullback turns a framed expression into a functor. Identified
expressions give identified functors, and restriction of the expression
agrees with precomposition of that functor. The comparison uses the whole
pullback cone, including its base coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-cong; retarget-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open Laws.PullbackStructure P

module Lifts {B C : CAT} (u v : MAP B C) where
  private
    module F = Fiber u v
      using (encode-comparison; encode-decode; decode-encode; decode-restrict; decode)
  module H = EndpointFiber u v
    using (base; category; cone; lift; lift-β)

  restrict : {Γ Δ : CAT} (b : MAP Γ B)
    (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
    MorphismExpression (u ∘ (b ∘ h)) (v ∘ (b ∘ h))
  restrict b f h = retarget-expression (restrict-expression f h)
    (comp-assoc h b u) (comp-assoc h b v)

  private
    restriction-expression : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (F.decode (conePre h (H.cone b f))) (restrict b f h)
    restriction-expression b f h = expressionIso-compose
      (retarget-expressionIso (restrict-expressionIso (F.decode-encode b f) h)
        (comp-assoc h b u) (comp-assoc h b v))
      (expressionIso-inverse (F.decode-restrict (H.cone b f) h))

  abstract
    lift-universal : H.lift H.base (F.decode (pullbackCone endpoints (pair u v))) =₁ id H.category
    lift-universal = pullback-reflect _ (id H.category)
      (coneIso-compose (coneIso-inverse (conePre-id (pullbackCone endpoints (pair u v))))
        (coneIso-compose (coneIso-inverse (F.encode-decode (pullbackCone endpoints (pair u v))))
          (H.lift-β H.base (F.decode (pullbackCone endpoints (pair u v))))))

    encode-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (u ∘ b) (v ∘ b)} → ExpressionIso f g →
      ConeIso (H.cone b f) (H.cone b g)
    encode-cong b {f} Φ = F.encode-comparison b b f _ (idIso b)
      (expressionIso-compose Φ (expressionIso-compose (retarget-id f)
        (retarget-cong f (postWhisker-idIso u b) (postWhisker-idIso v b))))

    encode-cong-right : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (u ∘ b) (v ∘ b)} (Φ : ExpressionIso f g) →
      ConeIso.rightIso (encode-cong b Φ) =₂ idIso b
    encode-cong-right b Φ = idIso _

    lift-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (u ∘ b) (v ∘ b)} → ExpressionIso f g →
      H.lift b f =₁ H.lift b g
    lift-cong b Φ = pullbackLift-cong (encode-cong b Φ)

    lift-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (g : MorphismExpression (u ∘ d) (v ∘ d))
      (σ : b =₁ d) → ExpressionIso (retarget-expression f (u ◁ σ) (v ◁ σ)) g →
      H.lift b f =₁ H.lift d g
    lift-change f g σ Φ = pullbackLift-cong (F.encode-comparison _ _ f g σ Φ)

    encode-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
      ConeIso (conePre h (H.cone b f)) (H.cone (b ∘ h) (restrict b f h))
    encode-restrict b f h = coneIso-compose
      (encode-cong (b ∘ h) (restriction-expression b f h))
      (F.encode-decode (conePre h (H.cone b f)))

    encode-restrict-right : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
      ConeIso.rightIso (encode-restrict b f h) =₂ idIso (b ∘ h)
    encode-restrict-right b f h = isoComp-unitˡ-at (idIso (b ∘ h)) ∙
      isoComp-cong (encode-cong-right (b ∘ h) (restriction-expression b f h)) (idIso (idIso (b ∘ h)))

    lift-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
      (H.lift b f ∘ h) =₁ H.lift (b ∘ h) (restrict b f h)
    lift-restrict b f h = pullbackLift-cong (encode-restrict b f h) ∙
      (pullbackLift-restrict h (H.cone b f)) ⁻¹
```
