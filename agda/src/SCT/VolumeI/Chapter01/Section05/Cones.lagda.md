# Cone diagrams and their comparisons

This follows `def:Cone_Diagram_On`. A comparison retains the two leg
isomorphisms and their matching compatibility. Comparing such comparisons
also retains the next compatibility, as an `Iso₃`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.Cones
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯

record Cone {C D E : CAT} (f : MAP C E) (g : MAP D E) (T : CAT) : Set m where
  field
    left : MAP T C
    right : MAP T D
    match : NatIso (f ∘ left) (g ∘ right)

record ConeIso {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) : Set m where
  field
    leftIso : NatIso (Cone.left s) (Cone.left t)
    rightIso : NatIso (Cone.right s) (Cone.right t)
    compatible : Iso₂ (Cone.match t ∙ (f ◁ leftIso)) ((g ◁ rightIso) ∙ Cone.match s)

record ConeIso₂ {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} (Φ Ψ : ConeIso s t) : Set m where
  field
    leftId : Iso₂ (ConeIso.leftIso Φ) (ConeIso.leftIso Ψ)
    rightId : Iso₂ (ConeIso.rightIso Φ) (ConeIso.rightIso Ψ)

  leftBoundary = isoComp-cong (idIso (Cone.match t)) (postWhisker f ◁ leftId)
  rightBoundary = isoComp-cong (postWhisker g ◁ rightId) (idIso (Cone.match s))

  field
    compatible : Iso₃ (ConeIso.compatible Ψ ∙ leftBoundary)
      (rightBoundary ∙ ConeIso.compatible Φ)

conePre : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  → MAP S T → Cone f g T → Cone f g S
conePre {f = f} {g} u s = record
  { left = Cone.left s ∘ u
  ; right = Cone.right s ∘ u
  ; match = comp-assoc u (Cone.right s) g ∙
      ((Cone.match s ▷ u) ∙ invIso (comp-assoc u (Cone.left s) f)) }

coneIso-id : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → ConeIso s s
coneIso-id {f = f} {g} s = record
  { leftIso = idIso (Cone.left s)
  ; rightIso = idIso (Cone.right s)
  ; compatible = invIso (isoComp-cong (postWhisker-idIso g (Cone.right s)) (idIso (Cone.match s))) ∙
      (invIso (isoComp-unitˡ-at (Cone.match s)) ∙
      (isoComp-unitʳ-at (Cone.match s) ∙
        isoComp-cong (idIso (Cone.match s)) (postWhisker-idIso f (Cone.left s)))) }
```
