# Substitution along a section of a projection

Suppose `i` is equipped with an identification `π ∘ i = id`. Applying a
functor to that identification gives a specified evaluation along `i`.
The two lemmas below track that evaluation under substitution and under
composition of the applied functors. They apply to product insertion,
but their statements do not require products.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section04.SplitProjectionCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (Square; compose-base; lift-base; lift-compose; lift-square)
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (lift-assoc)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; right-unitor-comp)

section-image : {X K Y : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ (id X)) (h : MAP X Y) → ((h ∘ π) ∘ i) =₁ h
section-image π i b h = comp-unitʳ h ∙ lift-base h π i b

abstract
  section-pre : {X Y Z K : CAT} (π : MAP K Y) (i : MAP Y K)
    (b : (π ∘ i) =₁ (id Y)) (h : MAP X Y) (k : MAP Y Z) →
    (compose-base (k ∘ π) i (section-image π i b k) h (idIso (k ∘ h))) =₂
      (lift-base k π (i ∘ h) (compose-base π i b h (comp-unitˡ h)))
  section-pre π i b h k =
    let B = lift-base k π i b
        tail = (comp-assoc h i (k ∘ π)) ⁻¹
    in lift-compose k π i h b (comp-unitˡ h) ∙
    (isoComp-cong (triangle-whiskered h k) (idIso ((B ▷ h) ∙ tail)) ∙
    (isoComp-assoc-at (comp-unitʳ k ▷ h) (B ▷ h) tail ∙
    (isoComp-cong (preWhisker-isoComp-at (comp-unitʳ k) B h) (idIso tail) ∙
      isoComp-unitˡ-at (((section-image π i b k) ▷ h) ∙ tail))))

  section-comp : {X K Y Z : CAT} (π : MAP K X) (i : MAP X K)
    (b : (π ∘ i) =₁ (id X)) (h : MAP X Y) (k : MAP Y Z) →
    (section-image π i b (k ∘ h)) =₂
      (lift-base k (h ∘ π) i (section-image π i b h) ∙ (comp-assoc π h k ▷ i))
  section-comp π i b h k =
    isoComp-cong
      (isoComp-cong ((postWhisker-isoComp-at k (comp-unitʳ h) (lift-base h π i b)) ⁻¹)
          (idIso (comp-assoc i (h ∘ π) k)) ∙
        (isoComp-assoc-at (k ◁ comp-unitʳ h) (k ◁ lift-base h π i b)
          (comp-assoc i (h ∘ π) k)) ⁻¹)
      (idIso (comp-assoc π h k ▷ i)) ∙
    ((isoComp-assoc-at (k ◁ comp-unitʳ h)
      (lift-base k (h ∘ π) i (lift-base h π i b)) (comp-assoc π h k ▷ i)) ⁻¹ ∙
    (isoComp-cong (idIso (k ◁ comp-unitʳ h)) (lift-assoc π (id _) i b h k) ∙
    (isoComp-assoc-at (k ◁ comp-unitʳ h) (comp-assoc (id _) h k) (lift-base (k ∘ h) π i b) ∙
      isoComp-cong (right-unitor-comp h k) (idIso (lift-base (k ∘ h) π i b)))))
```

```agda
abstract
  section-lift-compose : {X Y Z W : CAT} (π : MAP Z X) (ρ : MAP Y X)
    (k : MAP Y Z) (i : MAP X Y) (bk : (π ∘ k) =₁ ρ)
    (bi : (ρ ∘ i) =₁ (id X)) (h : MAP X W) →
    (compose-base (h ∘ π) k (lift-base h π k bk) i (section-image ρ i bi h)) =₂
      (section-image π (k ∘ i) (compose-base π k bk i bi) h)
  section-lift-compose π ρ k i bk bi h =
    isoComp-cong (idIso (comp-unitʳ h)) (lift-compose h π k i bk bi) ∙
      isoComp-assoc-at (comp-unitʳ h) (lift-base h ρ i bi)
        ((lift-base h π k bk ▷ i) ∙ (comp-assoc i k (h ∘ π)) ⁻¹)

  section-square : {X K Y : CAT} (π : MAP K X)
    {f g : MAP X K} (bf : (π ∘ f) =₁ (id X)) (bg : (π ∘ g) =₁ (id X))
    (α : f =₁ g) (h : MAP X Y) → Square π bf bg α →
    Square (h ∘ π) (section-image π f bf h) (section-image π g bg h) α
  section-square π bf bg α h square =
    isoComp-cong (idIso (comp-unitʳ h)) (lift-square h π bf bg α square) ∙
      isoComp-assoc-at (comp-unitʳ h) (lift-base h π _ bg) ((h ∘ π) ◁ α)
```
