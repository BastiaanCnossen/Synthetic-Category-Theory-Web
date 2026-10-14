# Transporting a postcomposed boundary

This calculation retains both frames of a specified square. It separates
postcomposition of a decoded boundary from the change of its target frame.
The endpoint calculations for images of hom fibers use it with the product
projection normalizations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.Coordinates.BoundaryTransport
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (transport-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

abstract
  post-boundary-transport : {X Y Z : CAT} (F : MAP Y Z)
    {a₀ a₁ a′ : MAP X Y} {b₀ b₁ d₀ d r : MAP X Z}
    (k : a₀ =₁ a′) (z : a₀ =₁ a₁)
    (N₀ : b₀ =₁ (F ∘ a₀)) (N₁ : b₁ =₁ (F ∘ a₁))
    (L : b₀ =₁ d₀) (R : b₁ =₁ r) (h : d₀ =₁ d) (E : d =₁ (F ∘ a′))
    (P : b₀ =₁ b₁)
    → (E ⁻¹ ∙ ((F ◁ k) ∙ N₀)) =₂ (h ∙ L)
    → (N₁ ∙ P) =₂ ((F ◁ z) ∙ N₀)
    → ((R ∙ (P ∙ L ⁻¹)) ∙ h ⁻¹) =₂
        ((R ∙ N₁ ⁻¹) ∙ ((F ◁ (z ∙ k ⁻¹)) ∙ E))
  post-boundary-transport F {a₀} {a₁} {a′} {b₀} {b₁} {d₀} {d} {r} k z N₀ N₁ L R h E P left natural =
    cancel-right h B ∙ isoComp-cong (bk ⁻¹) (idIso (h ⁻¹))
    where
    I : a′ =₁ a₁
    I = z ∙ k ⁻¹
    B : d =₁ r
    B = (R ∙ N₁ ⁻¹) ∙ ((F ◁ I) ∙ E)
    cancel : (I ∙ k) =₂ z
    cancel = isoComp-unitʳ-at z ∙
      (isoComp-cong (idIso z) (isoComp-inverseˡ-at k) ∙ isoComp-assoc-at z (k ⁻¹) k)
    right : ((R ∙ N₁ ⁻¹) ∙ N₁) =₂ (idIso _ ∙ R)
    right = (isoComp-unitˡ-at R) ⁻¹ ∙
      (isoComp-unitʳ-at R ∙
        (isoComp-cong (idIso R) (isoComp-inverseˡ-at N₁) ∙ isoComp-assoc-at R (N₁ ⁻¹) N₁))
    middle : ((F ◁ I) ∙ ((F ◁ k) ∙ N₀)) =₂ (N₁ ∙ P)
    middle = natural ⁻¹ ∙
      (isoComp-cong ((postWhisker F ◁ cancel) ∙ (postWhisker-isoComp-at F I k) ⁻¹) (idIso N₀) ∙
        (isoComp-assoc-at (F ◁ I) (F ◁ k) N₀) ⁻¹)
    transported : (((R ∙ N₁ ⁻¹) ∙ ((F ◁ I) ∙ (E ⁻¹) ⁻¹)) ∙ h) =₂
      (idIso r ∙ (R ∙ (P ∙ L ⁻¹)))
    transported = transport-square L (E ⁻¹) R (R ∙ N₁ ⁻¹)
      P (F ◁ I) ((F ◁ k) ∙ N₀) N₁ h (idIso _) left right middle
    bk : (B ∙ h) =₂ (R ∙ (P ∙ L ⁻¹))
    bk = isoComp-unitˡ-at (R ∙ (P ∙ L ⁻¹)) ∙
      (transported ∙
        (isoComp-cong
          (isoComp-cong (idIso (R ∙ N₁ ⁻¹))
            (isoComp-cong (idIso (F ◁ I)) (inverse-inverse E)))
          (idIso h)) ⁻¹)
```
