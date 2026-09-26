# A cone with a lifted left leg

A specified factorization of the left leg produces a cone over the
composite cospan. Projecting that cone recovers the original cone, with
the prescribed comparison on the left and the identity on the right.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.LeftLifts
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Left {A B C D X : CAT} (f : MAP A B) (g : MAP B D) {p : MAP C D}
  (s : Cone g p X) (u : MAP X A) (β : (f ∘ u) =₁ Cone.left s) where
  value : Cone (g ∘ f) p X
  value = record { left = u ; right = Cone.right s
    ; match = Cone.match s ∙ ((g ◁ β) ∙ comp-assoc u f g) }
  abstract
    matching : Cone.match (compositeCone f g value) =₂ (Cone.match s ∙ (g ◁ β))
    matching = cancel-right (comp-assoc u f g) (Cone.match s ∙ (g ◁ β)) ∙
      isoComp-cong ((isoComp-assoc-at (Cone.match s) (g ◁ β) (comp-assoc u f g)) ⁻¹)
        (idIso ((comp-assoc u f g) ⁻¹))

  comparison : ConeIso (compositeCone f g value) s
  comparison = record { leftIso = β ; rightIso = idIso (Cone.right s)
    ; compatible = isoComp-cong ((postWhisker-idIso p (Cone.right s)) ⁻¹)
        (idIso (Cone.match (compositeCone f g value))) ∙
      ((isoComp-unitˡ-at (Cone.match (compositeCone f g value))) ⁻¹ ∙ matching ⁻¹) }
```
