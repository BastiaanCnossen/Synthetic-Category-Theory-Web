# Recovering compatibility after restriction

The associators in a restricted cone can be removed from its compatibility
square. This lets a comparison be checked on coproduct summands without
forgetting their matching isomorphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section05.ConeCompatibilityRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at)

cone-pre-compatible : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP S T) (s t : Cone f g T)
  (α : =₁ (Cone.left s) (Cone.left t))
  (β : =₁ (Cone.right s) (Cone.right t))
  → =₂ (Cone.match (conePre r t) ∙ (f ◁ (α ▷ r)))
      ((g ◁ (β ▷ r)) ∙ Cone.match (conePre r s))
  → =₂ ((Cone.match t ∙ (f ◁ α)) ▷ r) (((g ◁ β) ∙ Cone.match s) ▷ r)
cone-pre-compatible {f = f} {g} r s t α β p =
  invIso (preWhisker-isoComp-at (g ◁ β) (Cone.match s) r) ∙
  (reflect-transport-square
    (comp-assoc r (Cone.left s) f) (comp-assoc r (Cone.left t) f)
    (comp-assoc r (Cone.right s) g) (comp-assoc r (Cone.right t) g)
    (Cone.match s ▷ r) (Cone.match t ▷ r)
    ((f ◁ α) ▷ r) ((g ◁ β) ▷ r) (f ◁ (α ▷ r)) (g ◁ (β ▷ r))
    (whisker-mixed-at α r f) (whisker-mixed-at β r g) p ∙
    preWhisker-isoComp-at (Cone.match t) (f ◁ α) r)
```
