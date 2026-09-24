# Cone diagrams and their comparisons

Following `def:Cone_Diagram_On`, `Cone f g T` is a cone with vertex `T`
on the cospan given by `f` and `g`. It records `left`, `right`, and a
natural isomorphism `match` between their composites into the base.

`ConeIso s t` compares the two legs and retains their compatibility with
`match` as an `_=₂_`. `ConeIso₂` compares those comparisons and retains
the next compatibility as an `_=₃_`. These are records of data, not a
construction of a category of all cones.

`conePre u s` changes the vertex by precomposing with `u`; the associators
in its definition transport the matching to the new legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section06.Cones
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯

record Cone {C D E : CAT} (f : MAP C E) (g : MAP D E) (T : CAT) : Set m where
  field
    left : MAP T C
    right : MAP T D
    match : (f ∘ left) =₁ (g ∘ right)

record ConeIso {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) : Set m where
  field
    leftIso : (Cone.left s) =₁ (Cone.left t)
    rightIso : (Cone.right s) =₁ (Cone.right t)
    compatible : (Cone.match t ∙ (f ◁ leftIso)) =₂ ((g ◁ rightIso) ∙ Cone.match s)

record ConeIso₂ {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} (Φ Ψ : ConeIso s t) : Set m where
  field
    leftId : (ConeIso.leftIso Φ) =₂ (ConeIso.leftIso Ψ)
    rightId : (ConeIso.rightIso Φ) =₂ (ConeIso.rightIso Ψ)

  leftBoundary = isoComp-cong (idIso (Cone.match t)) (postWhisker f ◁ leftId)
  rightBoundary = isoComp-cong (postWhisker g ◁ rightId) (idIso (Cone.match s))

  field
    compatible : (ConeIso.compatible Ψ ∙ leftBoundary) =₃
      (rightBoundary ∙ ConeIso.compatible Φ)

conePre : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  → MAP S T → Cone f g T → Cone f g S
conePre {f = f} {g} u s = record
  { left = Cone.left s ∘ u
  ; right = Cone.right s ∘ u
  ; match = comp-assoc u (Cone.right s) g ∙
      ((Cone.match s ▷ u) ∙ (comp-assoc u (Cone.left s) f) ⁻¹) }

coneIso-id : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → ConeIso s s
coneIso-id {f = f} {g} s = record
  { leftIso = idIso (Cone.left s)
  ; rightIso = idIso (Cone.right s)
  ; compatible = (isoComp-cong (postWhisker-idIso g (Cone.right s)) (idIso (Cone.match s))) ⁻¹ ∙
      ((isoComp-unitˡ-at (Cone.match s)) ⁻¹ ∙
      (isoComp-unitʳ-at (Cone.match s) ∙
        isoComp-cong (idIso (Cone.match s)) (postWhisker-idIso f (Cone.left s)))) }
```
