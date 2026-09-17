# Cocones on a composite

An outer cocone restricts to the left span. Its matching includes the
associator of the composite top arrow. Comparisons can be checked after
this restriction provided their original two legs are specified.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU

module SCT.VolumeI.Chapter01.Section08.CompositeCocones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 public
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

compositeCocone : {A B C D E : CAT} (f : MAP A B) (g : MAP B C) {h : MAP A D} →
  Cocone (g ∘ f) h E → Cocone f h E
compositeCocone f g s = record
  { left = Cocone.left s ∘ g ; right = Cocone.right s
  ; match = Cocone.match s ∙ comp-assoc f g (Cocone.left s) }

compositeCoconeIso : {A B C D E : CAT} (f : MAP A B) (g : MAP B C) {h : MAP A D}
  {s t : Cocone (g ∘ f) h E} → CoconeIso s t →
  CoconeIso (compositeCocone f g s) (compositeCocone f g t)
compositeCoconeIso f g {h} {s} {t} Φ = record
  { leftIso = α ▷ g ; rightIso = β
  ; compatible = paste-squares As At (Cocone.match s) (Cocone.match t)
      ((α ▷ g) ▷ f) (α ▷ (g ∘ f)) (β ▷ h)
      (preWhisker-comp-at α g f) (CoconeIso.compatible Φ) }
  where
  α = CoconeIso.leftIso Φ
  β = CoconeIso.rightIso Φ
  As = comp-assoc f g (Cocone.left s)
  At = comp-assoc f g (Cocone.left t)

compositeCocone-compatible : {A B C D E : CAT} (f : MAP A B) (g : MAP B C) {h : MAP A D}
  (s t : Cocone (g ∘ f) h E)
  (α : NatIso (Cocone.left s) (Cocone.left t))
  (β : NatIso (Cocone.right s) (Cocone.right t)) →
  Iso₂ (Cocone.match (compositeCocone f g t) ∙ ((α ▷ g) ▷ f))
    ((β ▷ h) ∙ Cocone.match (compositeCocone f g s)) → CoconeIso s t
compositeCocone-compatible f g {h} s t α β κ = record
  { leftIso = α ; rightIso = β
  ; compatible = cancel-right-reflect As
      (invIso (isoComp-assoc-at (β ▷ h) (Cocone.match s) As) ∙
      (κ ∙
      (invIso (isoComp-assoc-at (Cocone.match t) At ((α ▷ g) ▷ f)) ∙
      (isoComp-cong (idIso (Cocone.match t)) (invIso (preWhisker-comp-at α g f)) ∙
        isoComp-assoc-at (Cocone.match t) (α ▷ (g ∘ f)) As)))) }
  where
  As = comp-assoc f g (Cocone.left s)
  At = comp-assoc f g (Cocone.left t)
```
