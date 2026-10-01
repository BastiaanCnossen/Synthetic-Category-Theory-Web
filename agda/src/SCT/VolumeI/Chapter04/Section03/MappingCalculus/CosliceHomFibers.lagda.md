# Hom fibers with their normalized universal arrows

The hom category is a fiber of the coslice projection. This presentation
uses the literal universal hom expression for its inclusion, which makes
composition and functorial images available through the existing hom
calculus. Its pullback proof retains the complete endpoint comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceHomFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomNormalization 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cong; retarget-assoc)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantPointRestriction 𝒯 M using (const-One-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre; cone-match-change)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberChangeExpressions as Change
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.RelativeCosliceIntroductions as Introductions
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse; IsPullback; pullback-cone-invariant)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressionCones as ExpressionCones
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as CosliceLifts
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as SourceRestriction
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction 𝒯 M ℱ P I
  using (hom-restrict; hom-expression-restrict)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P using (pullbackCone)

module At {C : CAT} (x z : Obj-abs C) where
  private
    H = Hom C x z
    t = terminate H
    V : MorphismExpression (const {P = H} x) (const z)
    V = hom-expression (id H)
    module Original = EndpointFiber x z
    module Target = EndpointFiber (const {P = One} x) z
    module CosliceFiber = EndpointFiber (const {P = C} x) (id C)
    module Changed = Change.Along 𝒯 M ℱ P I
      {u = x} {v = z} {u′ = const {P = One} x} {v′ = z}
      ((const-One x) ⁻¹) (idIso z) using (map; map-isEquiv; module Specified)
    module Specified = Changed.Specified (hom-intro V) t V (Original.lift-β t V)
      using (family; family-computation)
    module Introduction = Introductions.At 𝒯 M ℱ P I z x t V
      using (relative-expression; ordinary-expression; factor-cone; comparison; comparison-left; module Pullback)

    abstract
      source-frame : ((const-One x) ⁻¹ ▷ t) =₂ (const-pre x t) ⁻¹
      source-frame = (＝-inv ◁ const-One-restrict {Γ = H} x) ∙ pre-inverse (const-One x) t
      normalized-expression : ExpressionIso Specified.family Introduction.relative-expression
      normalized-expression = retarget-cong V source-frame (preWhisker-idIso z t)

    normalized-map : MAP H Target.category
    normalized-map = Target.lift t Introduction.relative-expression
    changed-map : MAP H Target.category
    changed-map = Changed.map ∘ hom-intro V
    normalized-cone : Cone endpoints (pair (const {P = One} x) z) H
    normalized-cone = Target.cone t Introduction.relative-expression

    abstract
      normalized-computation : ConeIso
        (conePre changed-map (pullbackCone endpoints (pair (const {P = One} x) z))) normalized-cone
      normalized-computation = coneIso-compose
        (Lifts.Lifts.encode-cong 𝒯 M ℱ P I (const {P = One} x) z t normalized-expression)
        Specified.family-computation

    normalization-comparison : ConeIso
      (conePre changed-map (pullbackCone endpoints (pair (const {P = One} x) z)))
      (conePre normalized-map (pullbackCone endpoints (pair (const {P = One} x) z)))
    normalization-comparison = coneIso-compose (coneIso-inverse (Target.lift-β t Introduction.relative-expression))
      normalized-computation
    module Reflected = Reflection.Lift 𝒯 P
      {f = endpoints} {g = pair (const {P = One} x) z}
      changed-map normalized-map normalization-comparison using (lift)

    abstract
      normalized-isEquiv : IsEquiv normalized-map
      normalized-isEquiv = equiv-transport Reflected.lift
        (equiv-compose (hom-intro V) Changed.map
          (equiv-transport ((hom-η (id H)) ⁻¹) (id-isEquiv H)) Changed.map-isEquiv)

  inclusion : MAP H (Coslice C x)
  inclusion = coslice-intro x (const z) V

  endpoint-computation : ConeIso
    (conePre inclusion (pullbackCone endpoints (pair (const x) (id C))))
    (CosliceFiber.cone (const z) Introduction.ordinary-expression)
  endpoint-computation = CosliceFiber.lift-β (const z) Introduction.ordinary-expression

  private
    factor-comparison : ConeIso
      (conePre inclusion (coneSwap (pullbackCone endpoints (pair (const x) (id C)))))
      Introduction.factor-cone
    factor-comparison = coneIso-compose (coneIso-inverse Introduction.comparison)
      (coneIso-compose (coneIso-swap endpoint-computation)
        (coneSwap-pre inclusion (pullbackCone endpoints (pair (const x) (id C)))))
    module Result = Introduction.Pullback.WithFunctor normalized-isEquiv inclusion factor-comparison
      using (square; square-isPullback)
  projection : (coslice-projection x ∘ inclusion) =₁ const z
  projection = CosliceFiber.lift-base (const z) Introduction.ordinary-expression

  square : Cone (coslice-projection x) z H
  square = record { left = inclusion ; right = t ; match = projection }

  abstract
    matching-normal : Cone.match Result.square =₂ projection
    matching-normal = isoComp-unitˡ-at projection ∙
      isoComp-cong (inverse-identity (const {P = H} z) ∙
        (＝-inv ◁ Introduction.comparison-left)) (isoComp-unitʳ-at projection)

    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant
      (cone-match-change inclusion t _ _ matching-normal) Result.square-isPullback

  universal = V
  private
    module Read = ExpressionCones.At.FromCone 𝒯 M ℱ P I x inclusion (const z) V endpoint-computation
      using (comparison)
    module Lift = CosliceLifts.At 𝒯 M ℱ P I x using (module Restrict; module Change)
  open Read public renaming (comparison to expression-computation)

  module Family {Γ : CAT} (h : MAP Γ H) where
    family-expression : MorphismExpression (const {P = Γ} x) (const z)
    family-expression = hom-expression h
    private
      raw = restrict-expression V h
      normalized = SourceRestriction.restrict 𝒯 M ℱ I V h
      α = const-pre x h
      β = const-pre z h
      source-id = idIso (const {P = Γ} x)
      target-id = idIso (const {P = H} z ∘ h)
      abstract
        expression-comparison : ExpressionIso
          (retarget-expression normalized source-id β) family-expression
        expression-comparison = expressionIso-compose (hom-expression-cong (comp-unitˡ h))
          (expressionIso-compose (expressionIso-inverse (hom-expression-restrict (id H) h))
          (expressionIso-compose (retarget-cong raw (isoComp-unitˡ-at α) (isoComp-unitʳ-at β))
            (retarget-assoc raw α target-id source-id β)))
      module Restricted = Lift.Restrict (const {P = H} z) V h using (specified-comparison; source-projection; target-projection; base-computation)
      module ChangedFamily = Lift.Change {Γ = Γ} {b = const {P = H} z ∘ h} {d = const {P = Γ} z}
        normalized family-expression β expression-comparison using (specified-comparison; source-projection; target-projection; base-computation)

    specified-comparison : ConeIso
      (conePre (inclusion ∘ h) (pullbackCone endpoints (pair (const x) (id C))))
      (conePre (coslice-intro x (const z) family-expression) (pullbackCone endpoints (pair (const x) (id C))))
    specified-comparison = coneIso-compose ChangedFamily.specified-comparison Restricted.specified-comparison
    source-projection = β ∙ Restricted.source-projection
    target-projection = ChangedFamily.target-projection
    abstract
      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = isoComp-cong (idIso β) Restricted.base-computation ∙
        isoComp-assoc-at β Restricted.target-projection (ConeIso.rightIso Restricted.specified-comparison) ∙
        isoComp-cong ChangedFamily.base-computation (idIso (ConeIso.rightIso Restricted.specified-comparison)) ∙
        (isoComp-assoc-at target-projection (ConeIso.rightIso ChangedFamily.specified-comparison)
          (ConeIso.rightIso Restricted.specified-comparison)) ⁻¹

    private
      module FamilyReflected = Reflection.Lift 𝒯 P
        {f = endpoints} {g = pair (const {P = C} x) (id C)}
        (inclusion ∘ h) (coslice-intro x (const z) family-expression) specified-comparison
        using (lift; comparison-image; left-image; right-image)
    open FamilyReflected public renaming (lift to comparison)
```
