# Lifting normalized expressions to a coslice

Changes of the target and restrictions of a family commute with the
coslice introduction. These comparisons keep the normalized constant
source, so consumers need not expand the endpoint-fiber presentation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; restrict-retarget-outer)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M
  using (const-pre-natural; const-pre-compose)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions as FiberExpressions
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (ConeIso; ConeIso₂; conePre; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open Laws.PullbackStructure P using (pullbackCone)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as Restriction
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {C : CAT} (x : Obj-abs C) where
  private
    module Lift = Lifts.Lifts 𝒯 M ℱ P I (const x) (id C) using (lift-change; lift-cong; lift-restrict; encode-cong; encode-restrict; encode-cong-right; encode-restrict-right)
    module Fiber = FiberExpressions.Fiber 𝒯 M ℱ P I (const x) (id C) using (encode-comparison)
    module H = EndpointFiber (const x) (id C)

  frame : {Γ : CAT} {y : MAP Γ C} → MorphismExpression (const x) y →
    MorphismExpression ((const x) ∘ y) ((id C) ∘ y)
  frame {y = y} f = retarget-expression f ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹)

  module Change {Γ : CAT} {b d : MAP Γ C}
    (f : MorphismExpression (const x) b) (g : MorphismExpression (const x) d)
    (σ : b =₁ d) (Φ : ExpressionIso (retarget-expression f (idIso (const x)) σ) g) where
    private
      pb = const-pre x b
      pd = const-pre x d
      ub = comp-unitˡ b
      ud = comp-unitˡ d
      abstract
        source-change : ((const x ◁ σ) ∙ pb ⁻¹) =₂ (pd ⁻¹ ∙ idIso (const x))
        source-change = (move-square pd (const x ◁ σ) (idIso (const x)) pb
          ((isoComp-unitˡ-at pb) ⁻¹ ∙ const-pre-natural x σ)) ⁻¹
        target-change : ((id C ◁ σ) ∙ ub ⁻¹) =₂ (ud ⁻¹ ∙ σ)
        target-change = (move-square ud (id C ◁ σ) σ ub (postWhisker-id-at σ)) ⁻¹

        framed : ExpressionIso (retarget-expression (frame f) (const x ◁ σ) (id C ◁ σ)) (frame g)
        framed = expressionIso-compose (retarget-expressionIso Φ (pd ⁻¹) (ud ⁻¹))
          (expressionIso-compose (expressionIso-inverse (retarget-assoc f (idIso (const x)) σ (pd ⁻¹) (ud ⁻¹)))
          (expressionIso-compose (retarget-cong f source-change target-change)
            (retarget-assoc f (pb ⁻¹) (ub ⁻¹) (const x ◁ σ) (id C ◁ σ))))

    cone-comparison = Fiber.encode-comparison b d (frame f) (frame g) σ framed
    specified-comparison = coneIso-compose (coneIso-inverse (H.lift-β d (frame g)))
      (coneIso-compose cone-comparison (H.lift-β b (frame f)))
    source-projection = σ ∙ H.lift-base b (frame f)
    target-projection = H.lift-base d (frame g)
    abstract
      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = cancel-inverse target-projection source-projection

    private
      module Reflected = Reflection.Lift 𝒯 P (coslice-intro x b f) (coslice-intro x d g)
        specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)

  abstract
    congruence : {Γ : CAT} {b : MAP Γ C} {f g : MorphismExpression (const x) b} →
      ExpressionIso f g → coslice-intro x b f =₁ coslice-intro x b g
    congruence {b = b} Φ = Lift.lift-cong b
      (retarget-expressionIso Φ ((const-pre x b) ⁻¹) ((comp-unitˡ b) ⁻¹))

  module Restrict {Γ Δ : CAT} (b : MAP Γ C) (f : MorphismExpression (const x) b)
    (h : MAP Δ Γ) where
    private
      pb = const-pre x b
      ub = comp-unitˡ b
      ph = const-pre x h
      pbh = const-pre x (b ∘ h)
      ubh = comp-unitˡ (b ∘ h)
      A₀ = comp-assoc h b (const x)
      B₀ = comp-assoc h b (id C)
      raw = restrict-expression f h
      restricted = Restriction.restrict 𝒯 M ℱ I f h

      abstract
        source-square : (pbh ∙ A₀) =₂ (ph ∙ (pb ▷ h))
        source-square = cancel-inverse-tail (ph ∙ (pb ▷ h)) A₀ ∙
          isoComp-cong ((isoComp-assoc-at ph (pb ▷ h) (A₀ ⁻¹)) ⁻¹ ∙
            (const-pre-compose x h b) ⁻¹) (idIso A₀)
        target-square : (ubh ∙ B₀) =₂ (idIso (b ∘ h) ∙ (ub ▷ h))
        target-square = (isoComp-unitˡ-at (ub ▷ h)) ⁻¹ ∙ left-unitor-comp h b
        source-frame : (A₀ ∙ (pb ⁻¹ ▷ h)) =₂ (pbh ⁻¹ ∙ ph)
        source-frame = (move-square pbh A₀ ph (pb ▷ h) source-square) ⁻¹ ∙
          isoComp-cong (idIso A₀) (pre-inverse pb h)
        target-frame : (B₀ ∙ (ub ⁻¹ ▷ h)) =₂ (ubh ⁻¹ ∙ idIso (b ∘ h))
        target-frame = (move-square ubh B₀ (idIso (b ∘ h)) (ub ▷ h) target-square) ⁻¹ ∙
          isoComp-cong (idIso B₀) (pre-inverse ub h)
        framed : ExpressionIso (Lifts.Lifts.restrict 𝒯 M ℱ P I (const x) (id C) b (frame f) h)
          (frame restricted)
        framed = expressionIso-compose
          (expressionIso-inverse (retarget-assoc raw ph (idIso (b ∘ h)) (pbh ⁻¹) (ubh ⁻¹)))
          (expressionIso-compose (retarget-cong raw source-frame target-frame)
            (restrict-retarget-outer f (pb ⁻¹) (ub ⁻¹) h A₀ B₀))

    cone-comparison = coneIso-compose (Lift.encode-cong (b ∘ h) framed)
      (Lift.encode-restrict b (frame f) h)
    specified-comparison = coneIso-compose (coneIso-inverse (H.lift-β (b ∘ h) (frame restricted)))
      (coneIso-compose cone-comparison
      (coneIso-compose (coneIso-pre h (H.lift-β b (frame f)))
        (coneIso-inverse (conePre-assoc h (coslice-intro x b f)
          (pullbackCone endpoints (pair (const x) (id C)))))))
    source-projection = (H.lift-base b (frame f) ▷ h) ∙
      (comp-assoc h (coslice-intro x b f) H.base) ⁻¹
    target-projection = H.lift-base (b ∘ h) (frame restricted)
    abstract
      cone-comparison-base : ConeIso.rightIso cone-comparison =₂ idIso (b ∘ h)
      cone-comparison-base = isoComp-unitˡ-at (idIso (b ∘ h)) ∙
        isoComp-cong (Lift.encode-cong-right (b ∘ h) framed) (Lift.encode-restrict-right b (frame f) h)

      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = isoComp-unitˡ-at source-projection ∙
        isoComp-cong cone-comparison-base (idIso source-projection) ∙
        cancel-inverse target-projection (ConeIso.rightIso cone-comparison ∙ source-projection)

    private
      module Reflected = Reflection.Lift 𝒯 P (coslice-intro x b f ∘ h)
        (coslice-intro x (b ∘ h) restricted) specified-comparison
        using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)

  module Congruent {Γ : CAT} {b : MAP Γ C} {f g : MorphismExpression (const x) b}
    (Φ : ExpressionIso f g) where
    private
      framed-comparison = retarget-expressionIso Φ ((const-pre x b) ⁻¹) ((comp-unitˡ b) ⁻¹)
    cone-comparison = Lift.encode-cong b framed-comparison
    specified-comparison = coneIso-compose (coneIso-inverse (H.lift-β b (frame g)))
      (coneIso-compose cone-comparison (H.lift-β b (frame f)))
    source-projection = H.lift-base b (frame f)
    target-projection = H.lift-base b (frame g)
    abstract
      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = isoComp-unitˡ-at source-projection ∙
        isoComp-cong (Lift.encode-cong-right b framed-comparison) (idIso source-projection) ∙
        cancel-inverse target-projection (ConeIso.rightIso cone-comparison ∙ source-projection)

    private
      module Reflected = Reflection.Lift 𝒯 P (coslice-intro x b f) (coslice-intro x b g)
        specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)
```
