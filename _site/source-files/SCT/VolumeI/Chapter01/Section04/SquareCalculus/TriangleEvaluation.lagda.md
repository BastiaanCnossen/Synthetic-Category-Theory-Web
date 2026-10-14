# Postcomposition of a pasted triangle

A triangle comparing two restrictions remains commutative after
postcomposition. The comparison retains the external associators in
both stages of restriction. This is a consequence of the existing
projection-square pasting calculus.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.TriangleEvaluation
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
module PS = Projection 𝒯

private
  cancel-tail : {X Y : CAT} {f g h : MAP X Y} (p : f =₁ h) (q : f =₁ g) → ((p ∙ q ⁻¹) ∙ q) =₂ p
  cancel-tail p q = isoComp-unitʳ-at p ∙
    isoComp-cong (idIso p) (isoComp-inverseˡ-at q) ∙ isoComp-assoc-at p (q ⁻¹) q

module At {X Y Z A B : CAT} (F : MAP A B) (π : MAP Z A)
  (r : MAP Y Z) (s : MAP X Y) (t : MAP X Z) (κ : (r ∘ s) =₁ t)
  {h : MAP Y A} {k : MAP X A} (u : (π ∘ r) =₁ h) (v : (h ∘ s) =₁ k)
  (w : (π ∘ t) =₁ k)
  (triangle : (w ∙ ((π ◁ κ) ∙ comp-assoc s r π)) =₂ (v ∙ (u ▷ s))) where
  before = PS.compose-base π r u s v
  A₀ = comp-assoc s r π
  A₁ = comp-assoc s r (F ∘ π)
  U = PS.lift-base F π r u
  V = PS.lift-base F h s v
  W = PS.lift-base F π t w

  abstract
    base-square : (w ∙ (π ◁ κ)) =₂ before
    base-square = cancel-right-reflect A₀
      ((cancel-tail (v ∙ (u ▷ s)) A₀ ∙
          isoComp-cong ((isoComp-assoc-at v (u ▷ s) (A₀ ⁻¹)) ⁻¹) (idIso A₀)) ⁻¹ ∙
        triangle ∙ isoComp-assoc-at w (π ◁ κ) A₀)

    comparison : (W ∙ (((F ∘ π) ◁ κ) ∙ A₁)) =₂ (V ∙ (U ▷ s))
    comparison = cancel-tail (V ∙ (U ▷ s)) A₁ ∙
      isoComp-cong ((isoComp-assoc-at V (U ▷ s) (A₁ ⁻¹)) ⁻¹) (idIso A₁) ∙
      isoComp-cong ((PS.lift-compose F π r s u v) ⁻¹) (idIso A₁) ∙
      isoComp-cong (PS.lift-square F π before w κ base-square) (idIso A₁) ∙
      (isoComp-assoc-at W ((F ∘ π) ◁ κ) A₁) ⁻¹
```
