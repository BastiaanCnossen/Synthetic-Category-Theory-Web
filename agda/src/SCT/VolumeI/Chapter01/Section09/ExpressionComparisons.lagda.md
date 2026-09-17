# Recovering both endpoint equations

An isomorphism of endpoint-fiber cones with identity base component gives
an isomorphism of framed expressions. Pairing naturality and the product
comparison recover the source and target equations separately.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.ExpressionComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.EndpointFibers 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂; pair-cong-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; pair-pre-natural-substitution)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

pair-comparison-first : {Γ C D : CAT} {f f′ : MAP Γ C} {g g′ : MAP Γ D}
  {α α′ : =₁ f f′} {β β′ : =₁ g g′} →
  =₂ (pair-cong α β) (pair-cong α′ β′) → =₂ α α′
pair-comparison-first {f = f} {f′} {g} {g′} {α} {α′} {β} {β′} p =
  cancel-right-reflect (pair-β₁ f g)
    (pair-cong-triangle₁ α′ β′ ∙
      (isoComp-cong (idIso (pair-β₁ f′ g′)) (postWhisker pr₁ ◁ p) ∙
        invIso (pair-cong-triangle₁ α β)))

pair-comparison-second : {Γ C D : CAT} {f f′ : MAP Γ C} {g g′ : MAP Γ D}
  {α α′ : =₁ f f′} {β β′ : =₁ g g′} →
  =₂ (pair-cong α β) (pair-cong α′ β′) → =₂ β β′
pair-comparison-second {f = f} {f′} {g} {g′} {α} {α′} {β} {β′} p =
  cancel-right-reflect (pair-β₂ f g)
    (pair-cong-triangle₂ α′ β′ ∙
      (isoComp-cong (idIso (pair-β₂ f′ g′)) (postWhisker pr₂ ◁ p) ∙
        invIso (pair-cong-triangle₂ α β)))

module Decode {Γ B C : CAT} (u v : MAP B C) (y : MAP Γ B)
  (α β : MorphismExpression (u ∘ y) (v ∘ y))
  (Φ : ConeIso (EndpointFiber.cone u v y α) (EndpointFiber.cone u v y β))
  (base-identity : =₂ (ConeIso.rightIso Φ) (idIso y)) where
  module A = MorphismExpression α
  module R = MorphismExpression β
  δ = ConeIso.leftIso Φ
  before = pair-pre ev₀ ev₁ A.arrow
  after = pair-pre ev₀ ev₁ R.arrow
  p = pair-cong A.source-frame A.target-frame
  q = pair-cong R.source-frame R.target-frame
  r = invIso (pair-pre u v y)
  e = endpoints ◁ δ
  d = pair-cong (ev₀ ◁ δ) (ev₁ ◁ δ)

  abstract
    matching : =₂ ((r ∙ (q ∙ after)) ∙ e) (r ∙ (p ∙ before))
    matching = isoComp-unitˡ-at (r ∙ (p ∙ before)) ∙
      (isoComp-cong (postWhisker-idIso (pair u v) y ∙
        (postWhisker (pair u v) ◁ base-identity)) (idIso (r ∙ (p ∙ before))) ∙
        ConeIso.compatible Φ)

    paired : =₂
      (pair-cong (R.source-frame ∙ (ev₀ ◁ δ)) (R.target-frame ∙ (ev₁ ◁ δ))) p
    paired = cancel-right-reflect before
      (cancel-left-reflect r
        (matching ∙ invIso (isoComp-assoc-at r (q ∙ after) e)) ∙
      (invIso (isoComp-assoc-at q after e) ∙
      (isoComp-cong (idIso q) (pair-pre-natural-substitution ev₀ ev₁ δ) ∙
      (isoComp-assoc-at q d before ∙
        isoComp-cong (pair-cong-comp R.source-frame (ev₀ ◁ δ) R.target-frame (ev₁ ◁ δ)) (idIso before)))))

  comparison : ExpressionIso α β
  comparison = record
    { comparison = δ
    ; source-compatible = pair-comparison-first paired
    ; target-compatible = pair-comparison-second paired }

reflect-retarget-comparison : {Γ C : CAT} {f g f′ g′ : MAP Γ C}
  (α β : MorphismExpression f g) (p : =₁ f f′) (q : =₁ g g′) →
  ExpressionIso (retarget-expression α p q) (retarget-expression β p q) → ExpressionIso α β
reflect-retarget-comparison α β p q Φ = record
  { comparison = ExpressionIso.comparison Φ
  ; source-compatible = cancel-left-reflect p
      (ExpressionIso.source-compatible Φ ∙ invIso (isoComp-assoc-at p
        (MorphismExpression.source-frame β) (ev₀ ◁ ExpressionIso.comparison Φ)))
  ; target-compatible = cancel-left-reflect q
      (ExpressionIso.target-compatible Φ ∙ invIso (isoComp-assoc-at q
        (MorphismExpression.target-frame β) (ev₁ ◁ ExpressionIso.comparison Φ))) }
```


