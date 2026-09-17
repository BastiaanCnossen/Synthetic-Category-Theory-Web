# Removing a unit in a product coordinate

This form of the triangle comparison allows different source and target
projections. It is used when a parameter map is moved past a restriction
in the other product coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section08.ProductCoordinateUnits
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)

coordinate-inner-unit : {R K C D : CAT}
  (ρ : MAP R C) (π : MAP K C) (H : MAP R K)
  (b : NatIso (π ∘ H) (id C ∘ ρ)) (f : MAP C D) →
  Iso₂ ((comp-unitʳ f ▷ ρ) ∙ coordinate-comparison ρ (id C) π H b f)
    ((f ◁ (comp-unitˡ ρ ∙ b)) ∙ comp-assoc H π f)
coordinate-inner-unit ρ π H b f =
  let A = comp-assoc ρ (id _) f
      B = comp-assoc H π f
      L = comp-unitʳ f ▷ ρ
      first = cancel-right A (f ◁ comp-unitˡ ρ) ∙
        isoComp-cong (triangle-whiskered ρ f) (idIso (invIso A))
  in isoComp-cong (invIso (postWhisker-isoComp-at f (comp-unitˡ ρ) b)) (idIso B) ∙
    (invIso (isoComp-assoc-at (f ◁ comp-unitˡ ρ) (f ◁ b) B) ∙
    (isoComp-cong first (idIso ((f ◁ b) ∙ B)) ∙
      invIso (isoComp-assoc-at L (invIso A) ((f ◁ b) ∙ B))))
```

