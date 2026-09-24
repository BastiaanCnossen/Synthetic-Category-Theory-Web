# Removing the frames of a corner

A compatibility equation between framed edges determines the equation
between their routes through the common vertex. Both directions retain
the specified frames and the corner identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairUnits

module SCT.VolumeI.Chapter01.Section04.FramedCornerCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open PairUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

module At {X C : CAT} {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
  (A : a₀ =₁ a₁) (B : b₀ =₁ b₁) (L : a₀ =₁ l₀) (R : b₀ =₁ r₀)
  (nl : l₀ =₁ z) (nr : r₀ =₁ z) (δ : a₁ =₁ b₁)
  (compatible : ((nr ⁻¹ ∙ nl) ∙ L) =₂ (R ∙ (B ⁻¹ ∙ (δ ∙ A)))) where
  left = nl ∙ (L ∙ A ⁻¹)
  right = nr ∙ (R ∙ B ⁻¹)

  abstract
    attach-frame : (nl ∙ L) =₂ (nr ∙ (R ∙ (B ⁻¹ ∙ (δ ∙ A))))
    attach-frame = isoComp-cong (idIso nr) compatible ∙
      (isoComp-assoc-at nr (nr ⁻¹ ∙ nl) L ∙
        isoComp-cong ((cancel-inverse nr nl) ⁻¹) (idIso L))

    clear-left : (left ∙ A) =₂ (nl ∙ L)
    clear-left = isoComp-cong (idIso nl)
        (isoComp-unitʳ-at L ∙
          (isoComp-cong (idIso L) (isoComp-inverseˡ-at A) ∙ isoComp-assoc-at L (A ⁻¹) A)) ∙
      isoComp-assoc-at nl (L ∙ A ⁻¹) A

    expand-right : ((right ∙ δ) ∙ A) =₂ (nr ∙ (R ∙ (B ⁻¹ ∙ (δ ∙ A))))
    expand-right = isoComp-cong (idIso nr) (isoComp-assoc-at R (B ⁻¹) (δ ∙ A)) ∙
      (isoComp-assoc-at nr (R ∙ B ⁻¹) (δ ∙ A) ∙ isoComp-assoc-at right δ A)

    comparison : left =₂ (right ∙ δ)
    comparison = cancel-right-reflect A (expand-right ⁻¹ ∙ (attach-frame ∙ clear-left))

abstract
  reverse-shape : {X C D : CAT} {u v : MAP X C} (s : MAP C D)
    (δ : u =₁ v) {w : MAP X D}
    (L : (s ∘ u) =₁ w) (R : (s ∘ v) =₁ w) →
    L =₂ (R ∙ (s ◁ δ)) → R =₂ (L ∙ (s ◁ (δ ⁻¹)))
  reverse-shape s δ L R square = isoComp-cong (idIso L) ((post-inverse s δ) ⁻¹) ∙
    (cancel-right (s ◁ δ) R ∙ isoComp-cong square (idIso ((s ◁ δ) ⁻¹))) ⁻¹
```
