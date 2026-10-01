# Recovering the interval and its endpoints

Following the paragraph after `axiom:C_Rezk_Axiom`, let Rezk identify
the given interval with the constant interval at `z`. Its endpoints
give `σ : z = x` and `τ : z = y`. The identification `τ ∙ σ ⁻¹`
recovers the original interval, including both endpoint frames.

We use `constant-identification`, whose constant interval is obtained
by applying `identityArrow` to `x`. This is the explicit functor form
of the constant-interval construction.
The endpoint-compatible comparison with Section 2.1's curried
`isomorphism-expression` gives `isomorphism-recovery` below.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section03.RezkRecovery
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I
  using (constant-frame; constant-frame-natural; constant-identification)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison 𝒯 M ℱ P I E
  using (constant-isomorphism-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Recover {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (w : IsoLift (MorphismExpression.arrow f)) where
  module F = MorphismExpression f
    using (arrow; source-frame; target-frame)
  module Found = Identify f w
    using (center; constant-comparison; identification; source-identification; target-identification)
  z = Found.center
  δ = Found.constant-comparison
  source-frame = constant-frame ev₀ identity-source z
  target-frame = constant-frame ev₁ identity-target z

  σ : z =₁ x
  σ = Found.source-identification

  τ : z =₁ y
  τ = Found.target-identification

  identification : x =₁ y
  identification = Found.identification

  interval-comparison : (identityArrow ∘ x) =₁ F.arrow
  interval-comparison = δ ∙ (identityArrow ◁ σ ⁻¹)

  center-equation : {u v w t : MAP Γ C}
    (frame : u =₁ v) (edge : u =₁ w) (finish : w =₁ t) →
    ((finish ∙ (edge ∙ frame ⁻¹)) ∙ frame) =₂ (finish ∙ edge)
  center-equation frame edge finish = isoComp-cong (idIso finish)
    (isoComp-unitʳ-at edge ∙
      (isoComp-cong (idIso edge) (isoComp-inverseˡ-at frame) ∙ isoComp-assoc-at edge (frame ⁻¹) frame)) ∙
    isoComp-assoc-at finish (edge ∙ frame ⁻¹) frame

  endpoint : (v : MAP (Ar C) C) (b : (v ∘ identityArrow) =₁ (id C))
    {t : MAP Γ C} (finish : (v ∘ F.arrow) =₁ t) →
    let center = finish ∙ ((v ◁ δ) ∙ (constant-frame v b z) ⁻¹)
    in (finish ∙ (v ◁ interval-comparison)) =₂
      ((center ∙ σ ⁻¹) ∙ constant-frame v b x)
  endpoint v b finish = (isoComp-assoc-at center (σ ⁻¹) (constant-frame v b x)) ⁻¹ ∙
    (isoComp-cong (idIso center) (constant-frame-natural v b (σ ⁻¹)) ∙
    (isoComp-assoc-at center (constant-frame v b z) (v ◁ (identityArrow ◁ σ ⁻¹)) ∙
    (isoComp-cong ((center-equation (constant-frame v b z) (v ◁ δ) finish) ⁻¹)
      (idIso (v ◁ (identityArrow ◁ σ ⁻¹))) ∙
    ((isoComp-assoc-at finish (v ◁ δ) (v ◁ (identityArrow ◁ σ ⁻¹))) ⁻¹ ∙
      isoComp-cong (idIso finish) (postWhisker-isoComp-at v δ (identityArrow ◁ σ ⁻¹))))))
    where center = finish ∙ ((v ◁ δ) ∙ (constant-frame v b z) ⁻¹)

  recovery : ExpressionIso (constant-identification identification) f
  recovery = record
    { comparison = interval-comparison
    ; source-compatible = isoComp-unitˡ-at (constant-frame ev₀ identity-source x) ∙
        (isoComp-cong (isoComp-inverseʳ-at σ) (idIso (constant-frame ev₀ identity-source x)) ∙
          endpoint ev₀ identity-source F.source-frame)
    ; target-compatible = endpoint ev₁ identity-target F.target-frame }

  isomorphism-recovery : ExpressionIso (isomorphism-expression identification) f
  isomorphism-recovery = expressionIso-compose recovery
    (expressionIso-inverse (constant-isomorphism-comparison identification))
```
