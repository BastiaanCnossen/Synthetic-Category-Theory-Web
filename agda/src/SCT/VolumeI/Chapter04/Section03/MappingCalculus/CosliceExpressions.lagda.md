# Reading the universal arrows in a coslice

The normalized universal arrow of a coslice has constant source and its
target is the projection. Restricting it along a functor reconstructs
that functor by the coslice universal property. The proof compares both
endpoint frames; it does not identify only the underlying arrow diagram.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-cancel; restrict-retarget-outer)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackLift-cong)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-compose)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions as Expressions
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
open Laws.PullbackStructure P using (pullbackCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (conePre; coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection

module At {C : CAT} (x : Obj-abs C) where
  private
    module H = EndpointFiber (const x) (id C)
    module Decoded = Expressions.Fiber 𝒯 M ℱ P I (const x) (id C)
      using (read; decode-restrict; reconstruct; encode-decode)

  universal : MorphismExpression (const x) H.base
  universal = retarget-expression H.frame (const-pre x H.base) (comp-unitˡ H.base)

  read : {Γ : CAT} (h : MAP Γ (Coslice C x)) → MorphismExpression (const x) (H.base ∘ h)
  read h = retarget-expression (restrict-expression universal h)
    (const-pre x h) (idIso (H.base ∘ h))

  module Read {Γ : CAT} (h : MAP Γ (Coslice C x)) where
    private
      p = const-pre x (H.base ∘ h)
      q = comp-unitˡ (H.base ∘ h)
      A = comp-assoc h H.base (const x)
      B = comp-assoc h H.base (id C)
      raw = restrict-expression H.frame h
      normalized = retarget-expression (Decoded.read h) p q
      a₀ = const-pre x h
      b₀ = const-pre x H.base ▷ h

      abstract
        source-normal : (p ∙ A) =₂ (a₀ ∙ b₀)
        source-normal = cancel-inverse-tail (a₀ ∙ b₀) A ∙
          (isoComp-cong ((isoComp-assoc-at a₀ b₀ (A ⁻¹)) ⁻¹) (idIso A) ∙
            isoComp-cong ((const-pre-compose x h H.base) ⁻¹) (idIso A))

        target-normal : (q ∙ B) =₂ (idIso (H.base ∘ h) ∙ (comp-unitˡ H.base ▷ h))
        target-normal = (isoComp-unitˡ-at (comp-unitˡ H.base ▷ h)) ⁻¹ ∙ left-unitor-comp h H.base

        decode-restriction : ExpressionIso
          (retarget-expression raw A B) (Decoded.read h)
        decode-restriction = Decoded.decode-restrict (pullbackCone endpoints (pair (const x) (id C))) h

        change-frames : ExpressionIso
          (retarget-expression (retarget-expression raw A B) p q)
          (retarget-expression raw (a₀ ∙ b₀) (idIso (H.base ∘ h) ∙ (comp-unitˡ H.base ▷ h)))
        change-frames = expressionIso-compose (retarget-cong raw source-normal target-normal)
          (retarget-assoc raw A B p q)

    abstract
      comparison : ExpressionIso normalized (read h)
      comparison = expressionIso-compose
        (expressionIso-inverse (restrict-retarget-outer H.frame
          (const-pre x H.base) (comp-unitˡ H.base) h (const-pre x h) (idIso (H.base ∘ h))))
        (expressionIso-compose change-frames
          (retarget-expressionIso (expressionIso-inverse decode-restriction) p q))

      reconstruction-expression : ExpressionIso
        (retarget-expression (read h) (p ⁻¹) (q ⁻¹)) (Decoded.read h)
      reconstruction-expression = expressionIso-compose (retarget-cancel (Decoded.read h) p q)
        (retarget-expressionIso (expressionIso-inverse comparison) (p ⁻¹) (q ⁻¹))

      reconstruct : coslice-intro x (H.base ∘ h) (read h) =₁ h
      reconstruct = Decoded.reconstruct h ∙ pullbackLift-cong
        (Lifts.Lifts.encode-cong 𝒯 M ℱ P I (const x) (id C) (H.base ∘ h) reconstruction-expression)

  module FromExpression {Γ : CAT} (h : MAP Γ (Coslice C x))
    (f : MorphismExpression (const x) (H.base ∘ h)) (Φ : ExpressionIso f (read h)) where
    private
      p = const-pre x (H.base ∘ h)
      q = comp-unitˡ (H.base ∘ h)
      framed = retarget-expression f (p ⁻¹) (q ⁻¹)
      framed-comparison = expressionIso-compose (Read.reconstruction-expression h)
        (retarget-expressionIso Φ (p ⁻¹) (q ⁻¹))

    cone-comparison = Lifts.Lifts.encode-cong 𝒯 M ℱ P I (const x) (id C)
      (H.base ∘ h) framed-comparison
    specified-comparison = coneIso-compose
      (coneIso-inverse (Decoded.encode-decode (conePre h (pullbackCone endpoints (pair (const x) (id C))))))
      (coneIso-compose cone-comparison (H.lift-β (H.base ∘ h) framed))
    private
      module Reflected = Reflection.Lift 𝒯 P (coslice-intro x (H.base ∘ h) f) h
        specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)
```
