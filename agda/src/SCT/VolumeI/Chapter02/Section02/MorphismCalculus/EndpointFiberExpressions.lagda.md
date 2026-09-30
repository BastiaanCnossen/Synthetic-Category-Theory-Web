# Expressions and functors into an endpoint fiber

Decoding a cone keeps its base functor and the two projections of its
matching identification. Encoding this expression reconstructs the
whole cone. A comparison may change the base functor: its two images
retarget the decoded expression before the arrow comparison is applied.

This calculus is useful for constructing functors between categories of
morphisms over a base. It does not discard the base comparison or replace
it by equality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointFibers 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (same-arrow; retarget-assoc)
import SCT.VolumeI.Chapter01.Section06.Coordinates.PairedConeCoordinates as Paired
open Laws.PullbackStructure P

module Fiber {B C : CAT} (u v : MAP B C) where
  module H = EndpointFiber u v
  private
    module K = Paired.Coordinates 𝒯 (ev₀ {C}) ev₁ u v
      using (edge₁; edge₂; encode-edge₁; encode-edge₂; coordinate₁; coordinate₂; cone-from-coordinates;
        edge₁-restrict; edge₂-restrict)

  decode : {Γ : CAT} (s : Cone endpoints (pair u v) Γ) →
    MorphismExpression (u ∘ Cone.right s) (v ∘ Cone.right s)
  decode s = record
    { arrow = Cone.left s ; source-frame = K.edge₁ s ; target-frame = K.edge₂ s }

  decode-encode : {Γ : CAT} (b : MAP Γ B)
    (f : MorphismExpression (u ∘ b) (v ∘ b)) → ExpressionIso (decode (H.cone b f)) f
  decode-encode b f = same-arrow F.arrow _ _ _ _
    ((K.encode-edge₁ F.arrow b F.source-frame F.target-frame) ⁻¹)
    ((K.encode-edge₂ F.arrow b F.source-frame F.target-frame) ⁻¹)
    where module F = MorphismExpression f

  encode-decode : {Γ : CAT} (s : Cone endpoints (pair u v) Γ) →
    ConeIso s (H.cone (Cone.right s) (decode s))
  encode-decode s = K.cone-from-coordinates s (H.cone (Cone.right s) (decode s))
    (idIso (Cone.left s)) (idIso (Cone.right s))
    (coordinate ev₀ u (K.edge₁ s) (K.encode-edge₁ _ _ _ _))
    (coordinate ev₁ v (K.edge₂ s) (K.encode-edge₂ _ _ _ _))
    where
    coordinate : (e : MAP (Ar C) C) (w : MAP B C)
      (p : (e ∘ Cone.left s) =₁ (w ∘ Cone.right s))
      {q : (e ∘ Cone.left s) =₁ (w ∘ Cone.right s)} → q =₂ p →
      (q ∙ (e ◁ idIso (Cone.left s))) =₂ ((w ◁ idIso (Cone.right s)) ∙ p)
    coordinate e w p normalized =
      (isoComp-cong (postWhisker-idIso w (Cone.right s)) (idIso p)) ⁻¹ ∙
      (isoComp-unitˡ-at p) ⁻¹ ∙ isoComp-unitʳ-at p ∙
      isoComp-cong normalized (postWhisker-idIso e (Cone.left s))

  decode-comparison : {Γ : CAT} {s t : Cone endpoints (pair u v) Γ} (Φ : ConeIso s t) →
    ExpressionIso (retarget-expression (decode s) (u ◁ ConeIso.rightIso Φ) (v ◁ ConeIso.rightIso Φ)) (decode t)
  decode-comparison Φ = record
    { comparison = ConeIso.leftIso Φ
    ; source-compatible = K.coordinate₁ Φ
    ; target-compatible = K.coordinate₂ Φ }

  decode-restrict : {Γ Δ : CAT} (s : Cone endpoints (pair u v) Γ) (r : MAP Δ Γ) →
    ExpressionIso (retarget-expression (restrict-expression (decode s) r)
      (comp-assoc r (Cone.right s) u) (comp-assoc r (Cone.right s) v))
      (decode (conePre r s))
  decode-restrict s r = same-arrow (Cone.left s ∘ r) _ _ _ _
    (K.edge₁-restrict r s) (K.edge₂-restrict r s)

  encode-comparison : {Γ : CAT} (b d : MAP Γ B)
    (f : MorphismExpression (u ∘ b) (v ∘ b)) (g : MorphismExpression (u ∘ d) (v ∘ d))
    (σ : b =₁ d) → ExpressionIso (retarget-expression f (u ◁ σ) (v ◁ σ)) g →
    ConeIso (H.cone b f) (H.cone d g)
  encode-comparison b d f g σ Φ = K.cone-from-coordinates (H.cone b f) (H.cone d g)
    (ExpressionIso.comparison Φ) σ
    ((isoComp-cong (idIso (u ◁ σ)) (K.encode-edge₁ _ _ _ _)) ⁻¹ ∙
      ExpressionIso.source-compatible Φ ∙
      isoComp-cong (K.encode-edge₁ _ _ _ _) (idIso (ev₀ ◁ ExpressionIso.comparison Φ)))
    ((isoComp-cong (idIso (v ◁ σ)) (K.encode-edge₂ _ _ _ _)) ⁻¹ ∙
      ExpressionIso.target-compatible Φ ∙
      isoComp-cong (K.encode-edge₂ _ _ _ _) (idIso (ev₁ ◁ ExpressionIso.comparison Φ)))

  read : {Γ : CAT} (h : MAP Γ H.category) →
    MorphismExpression (u ∘ (H.base ∘ h)) (v ∘ (H.base ∘ h))
  read h = decode (conePre h (pullbackCone endpoints (pair u v)))

  read-restrict : {Γ Δ : CAT} (h : MAP Γ H.category) (r : MAP Δ Γ) →
    ExpressionIso (retarget-expression (restrict-expression (read h) r)
      ((u ◁ comp-assoc r h H.base) ∙ comp-assoc r (H.base ∘ h) u)
      ((v ◁ comp-assoc r h H.base) ∙ comp-assoc r (H.base ∘ h) v))
      (read (h ∘ r))
  read-restrict h r = expressionIso-compose
    (decode-comparison (conePre-assoc r h (pullbackCone endpoints (pair u v))))
    (expressionIso-compose
      (retarget-expressionIso (decode-restrict (conePre h (pullbackCone endpoints (pair u v))) r)
        (u ◁ comp-assoc r h H.base) (v ◁ comp-assoc r h H.base))
      (expressionIso-inverse (retarget-assoc (restrict-expression (read h) r)
        (comp-assoc r (H.base ∘ h) u) (comp-assoc r (H.base ∘ h) v)
        (u ◁ comp-assoc r h H.base) (v ◁ comp-assoc r h H.base))))

  reconstruct : {Γ : CAT} (h : MAP Γ H.category) → H.lift (H.base ∘ h) (read h) =₁ h
  reconstruct h = pullback-η h ∙ pullbackLift-cong
    (coneIso-inverse (encode-decode (conePre h (pullbackCone endpoints (pair u v)))))

  read-lift : {Γ : CAT} (b : MAP Γ B) (f : MorphismExpression (u ∘ b) (v ∘ b)) →
    ExpressionIso (retarget-expression (read (H.lift b f))
      (u ◁ H.lift-base b f) (v ◁ H.lift-base b f)) f
  read-lift b f = expressionIso-compose (decode-encode b f) (decode-comparison (H.lift-β b f))

  reflect : {Γ : CAT} (h k : MAP Γ H.category) (σ : (H.base ∘ h) =₁ (H.base ∘ k)) →
    ExpressionIso (retarget-expression (read h) (u ◁ σ) (v ◁ σ)) (read k) → h =₁ k
  reflect h k σ Φ = reconstruct k ∙
    pullbackLift-cong (encode-comparison (H.base ∘ h) (H.base ∘ k) (read h) (read k) σ Φ) ∙
    (reconstruct h) ⁻¹
```
