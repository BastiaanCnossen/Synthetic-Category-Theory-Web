# Relative and ordinary coslice introduction

An arrow with constant source can be introduced either in the endpoint
pullback over its original base or in the ordinary coslice over its target.
The comparison below retains the whole cone of the change of base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingBaseChange as PairingChange

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.RelativeCosliceIntroductions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence
  vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
open Laws.PullbackStructure P using (pullbackCone)

module At {Γ C D : CAT} (p : MAP C D) (b : Obj-abs D) (q : MAP Γ C)
  (V : MorphismExpression (const b) (p ∘ q)) where
  private
    module H = EndpointFiber (const {P = C} b) p
    module K = EndpointFiber (const {P = D} b) (id D)
    cp = const-pre b p
    cq = const-pre b q
    cpq = const-pre b (p ∘ q)
    upq = comp-unitˡ (p ∘ q)
    A = comp-assoc q p (const {P = D} b)
    δ₀ = cq ⁻¹ ∙ cpq
    δ₁ = upq
    s = MorphismExpression.source-frame V
    t = MorphismExpression.target-frame V

    abstract
      source-normal : (cpq ∙ A) =₂ (cq ∙ (cp ▷ q))
      source-normal = cancel-inverse-tail (cq ∙ (cp ▷ q)) A ∙
        isoComp-cong ((isoComp-assoc-at cq (cp ▷ q) (A ⁻¹)) ⁻¹ ∙
          (const-pre-compose b q p) ⁻¹) (idIso A)

      source-square : (δ₀ ∙ A) =₂ (cp ▷ q)
      source-square = isoComp-unitˡ-at (cp ▷ q) ∙
        isoComp-cong (isoComp-inverseˡ-at cq) (idIso (cp ▷ q)) ∙
        (isoComp-assoc-at (cq ⁻¹) cq (cp ▷ q)) ⁻¹ ∙
        isoComp-cong (idIso (cq ⁻¹)) source-normal ∙
        isoComp-assoc-at (cq ⁻¹) cpq A

    module Pairing = PairingChange.Along 𝒯 (const {P = D} b) (id D) p q
      cp (comp-unitˡ p) δ₀ δ₁ source-square (left-unitor-comp q p)
      using (family-comparison; base-comparison; comparison)

  relative-expression : MorphismExpression ((const b) ∘ q) (p ∘ q)
  relative-expression = retarget-expression V (cq ⁻¹) (idIso (p ∘ q))

  ordinary-expression : MorphismExpression ((const b) ∘ (p ∘ q)) (id D ∘ (p ∘ q))
  ordinary-expression = retarget-expression V (cpq ⁻¹) (upq ⁻¹)

  outer : Cone endpoints (pair (const b) p) Γ
  outer = H.cone q relative-expression

  ordinary : Cone endpoints (pair (const b) (id D)) Γ
  ordinary = K.cone (p ∘ q) ordinary-expression

  family-comparison = Pairing.family-comparison

  factor-cone : Cone (pair (const b) (id D)) endpoints Γ
  factor-cone = record { left = p ∘ q ; right = MorphismExpression.arrow V
    ; match = (Cone.match outer) ⁻¹ ∙ Pairing.base-comparison }

  private
    R = pair-pre (const {P = C} b) p q
    T = pair-pre (const {P = D} b) (id D) (p ∘ q)
    Δ = pair-cong δ₀ δ₁
    Ω = Pairing.base-comparison
    frames = pair-cong (MorphismExpression.source-frame ordinary-expression)
      (MorphismExpression.target-frame ordinary-expression)
    frames′ = pair-cong (MorphismExpression.source-frame relative-expression)
      (MorphismExpression.target-frame relative-expression)
    boundary = pair-pre ev₀ ev₁ (MorphismExpression.arrow V)

    abstract
      source-frame : (δ₀ ∙ (cpq ⁻¹ ∙ s)) =₂ (cq ⁻¹ ∙ s)
      source-frame = isoComp-cong (cancel-right cpq (cq ⁻¹)) (idIso s) ∙
        (isoComp-assoc-at δ₀ (cpq ⁻¹) s) ⁻¹

      target-frame : (δ₁ ∙ (upq ⁻¹ ∙ t)) =₂ (idIso (p ∘ q) ∙ t)
      target-frame = isoComp-cong (isoComp-inverseʳ-at upq) (idIso t) ∙
        (isoComp-assoc-at upq (upq ⁻¹) t) ⁻¹

      frame-comparison : (Δ ∙ frames) =₂ frames′
      frame-comparison = pair-cong-Iso₂ source-frame target-frame ∙
        (pair-cong-comp δ₀ (cpq ⁻¹ ∙ s) δ₁ (upq ⁻¹ ∙ t)) ⁻¹

      boundary-comparison : (R ⁻¹ ∙ Δ) =₂ (Ω ∙ T ⁻¹)
      boundary-comparison = move-square R Ω Δ T Pairing.comparison

      encoded-matching : Cone.match outer =₂ (Ω ∙ Cone.match ordinary)
      encoded-matching = isoComp-assoc-at Ω (T ⁻¹) (frames ∙ boundary) ∙
        isoComp-cong boundary-comparison (idIso (frames ∙ boundary)) ∙
        (isoComp-assoc-at (R ⁻¹) Δ (frames ∙ boundary)) ⁻¹ ∙
        isoComp-cong (idIso (R ⁻¹)) (isoComp-assoc-at Δ frames boundary) ∙
        isoComp-cong (idIso (R ⁻¹)) (isoComp-cong (frame-comparison ⁻¹) (idIso boundary))

      matching : Cone.match factor-cone =₂ Cone.match (coneSwap ordinary)
      matching = isoComp-unitˡ-at ((Cone.match ordinary) ⁻¹) ∙
        move-square (Cone.match outer) (idIso (endpoints ∘ MorphismExpression.arrow V))
          Ω (Cone.match ordinary) (encoded-matching ∙ isoComp-unitʳ-at (Cone.match outer))

  abstract
    comparison : ConeIso factor-cone (coneSwap ordinary)
    comparison = cone-match-change _ _ _ _ matching

    comparison-left : ConeIso.leftIso comparison =₂ idIso (p ∘ q)
    comparison-left = idIso _

    comparison-right : ConeIso.rightIso comparison =₂ idIso (MorphismExpression.arrow V)
    comparison-right = idIso _

  module Pullback (e : IsEquiv (H.lift q relative-expression)) where
    private
      module Change = BaseChange.Along 𝒯 P endpoints (pair (const b) (id D))
        (pullbackCone endpoints (pair (const b) (id D)))
        (pullbackCone-isPullback endpoints (pair (const b) (id D)))
        p family-comparison outer e using (module WithFactor)
    module WithFunctor (h : MAP Γ K.category)
      (Φ : ConeIso (conePre h (coneSwap (pullbackCone endpoints (pair (const b) (id D))))) factor-cone) where
      open Change.WithFactor h Φ public using (square; square-isPullback)
```
