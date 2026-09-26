# Composing paired projection frames

Pairing two composite projection frames agrees with composing their
paired frames. The comparison keeps the external associator. It follows
from the existing pairing assembly theorem and vertical cancellation.

This supplies the rectangle-coordinate assembly for square currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.PairedProjectionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (compose-base; Square)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (module PairingAssembly; cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; pair-pre-natural-substitution)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-id; pair-cong-comp; pair-cong-Iso₂)

abstract
  paired-square : {X Y A B : CAT} (f : MAP Y A) (g : MAP Y B)
    {r s : MAP X Y} {x : MAP X A} {y : MAP X B}
    (fr : (f ∘ r) =₁ x) (fs : (f ∘ s) =₁ x)
    (gr : (g ∘ r) =₁ y) (gs : (g ∘ s) =₁ y) (δ : r =₁ s) →
    Square f fr fs δ → Square g gr gs δ →
    Square (pair f g) (pair-cong fr gr ∙ pair-pre f g r) (pair-cong fs gs ∙ pair-pre f g s) δ
  paired-square f g {r} {s} fr fs gr gs δ first second =
    isoComp-cong (pair-cong-Iso₂ first second) (idIso (pair-pre f g r)) ∙
    isoComp-cong ((pair-cong-comp fs (f ◁ δ) gs (g ◁ δ)) ⁻¹) (idIso (pair-pre f g r)) ∙
    (isoComp-assoc-at (pair-cong fs gs) (pair-cong (f ◁ δ) (g ◁ δ)) (pair-pre f g r)) ⁻¹ ∙
    isoComp-cong (idIso (pair-cong fs gs)) ((pair-pre-natural-substitution f g δ) ⁻¹) ∙
    isoComp-assoc-at (pair-cong fs gs) (pair-pre f g s) (pair f g ◁ δ)

module At {Q R X A B : CAT} (f : MAP X A) (g : MAP X B) (r : MAP R X) (t : MAP Q R)
  {f₁ : MAP R A} {g₁ : MAP R B} {f₂ : MAP Q A} {g₂ : MAP Q B}
  (u : (f ∘ r) =₁ f₁) (v : (g ∘ r) =₁ g₁)
  (w : (f₁ ∘ t) =₁ f₂) (z : (g₁ ∘ t) =₁ g₂) where
  first = pair-cong u v ∙ pair-pre f g r
  second = pair-cong w z ∙ pair-pre f₁ g₁ t
  left = compose-base f r u t w
  right = compose-base g r v t z
  direct = pair-cong left right ∙ pair-pre f g (r ∘ t)
  composite = compose-base (pair f g) r first t second
  module Assemble = PairingAssembly f g r t (r ∘ t) (idIso (r ∘ t))
    u v w z left right (idIso f₂) (idIso g₂)
  A₀ = comp-assoc t r (pair f g)
  tail = first ▷ t

  abstract
    clear : {D : CAT} (h : MAP X D) {h₁ : MAP R D} {h₂ : MAP Q D}
      (b : (h ∘ r) =₁ h₁) (d : (h₁ ∘ t) =₁ h₂) →
      (compose-base h r b t d ∙ ((h ◁ idIso (r ∘ t)) ∙ comp-assoc t r h)) =₂
      (idIso h₂ ∙ (d ∙ (b ▷ t)))
    clear h b d = (isoComp-unitˡ-at (d ∙ (b ▷ t))) ⁻¹ ∙
      cancel-inverse-tail (d ∙ (b ▷ t)) (comp-assoc t r h) ∙
      isoComp-cong ((isoComp-assoc-at d (b ▷ t) ((comp-assoc t r h) ⁻¹)) ⁻¹)
        (idIso (comp-assoc t r h)) ∙
      isoComp-cong (idIso (compose-base h r b t d))
        (isoComp-unitˡ-at (comp-assoc t r h) ∙
          isoComp-cong (postWhisker-idIso h (r ∘ t)) (idIso (comp-assoc t r h)))

    short-normal : Assemble.short =₂ (direct ∙ A₀)
    short-normal = isoComp-cong (idIso direct)
      (isoComp-unitˡ-at A₀ ∙ isoComp-cong (postWhisker-idIso (pair f g) (r ∘ t)) (idIso A₀))
    long-normal : Assemble.long =₂ (second ∙ tail)
    long-normal = isoComp-unitˡ-at (second ∙ tail) ∙
      isoComp-cong (pair-cong-id f₂ g₂) (idIso (second ∙ tail))
    associated : (direct ∙ A₀) =₂ (second ∙ tail)
    associated = long-normal ∙ Assemble.assemble (clear f u w) (clear g v z) ∙ short-normal ⁻¹

    comparison : direct =₂ composite
    comparison = isoComp-assoc-at second tail (A₀ ⁻¹) ∙
      isoComp-cong associated (idIso (A₀ ⁻¹)) ∙ (cancel-right A₀ direct) ⁻¹
```
