# Pairing and identity substitution

The identity substitution comparison agrees with the external right unitor.
The prerequisite compatibility of that unitor with composition is derived
from the primitive pentagon and triangle, rather than imposed separately.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.PairingUnits
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.PentagonTriangleCoherence PT
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open PairingCoherence V T P PL S VC W
open PairingNaturality V T P PL S VC W using
  (cancel-left-reflect; cancel-right; project-composite)
open Structural V T P PL S W
open IteratedPairing V T P PL S VC W PT using
  (hcomp-idOuter; hcomp-idInner; pentagon-whiskered)

cancel-right-reflect : {X C : CAT} {f g h : MAP X C}
  (a : f =₁ g) {α β : g =₁ h}
  → (α ∙ a) =₂ (β ∙ a) → α =₂ β
cancel-right-reflect a {α} {β} p = cancel-right a β ∙
  (isoComp-cong p (idIso (a ⁻¹)) ∙ (cancel-right a α) ⁻¹)

preWhisker-id-reflect : {X C : CAT} {f g : MAP X C} {α β : f =₁ g}
  → (α ▷ id X) =₂ (β ▷ id X) → α =₂ β
preWhisker-id-reflect {f = f} {g} {α} {β} p =
  cancel-right-reflect (comp-unitʳ f)
    (preWhisker-id-at β ∙
      (isoComp-cong (idIso (comp-unitʳ g)) p ∙ (preWhisker-id-at α) ⁻¹))

triangle-whiskered : {X C D : CAT} (f : MAP X C) (g : MAP C D)
  → (comp-unitʳ g ▷ f) =₂
      ((g ◁ comp-unitˡ f) ∙ comp-assoc f (id C) g)
triangle-whiskered f g =
  isoComp-cong (hcomp-idOuter g (comp-unitˡ f)) (idIso (comp-assoc f (id _) g)) ∙
    (comp-triangle f g ∙ (hcomp-idInner (comp-unitʳ g) f) ⁻¹)

right-unitor-comp : {X K C : CAT} (h : MAP X K) (π : MAP K C)
  → (comp-unitʳ (π ∘ h)) =₂
      ((π ◁ comp-unitʳ h) ∙ comp-assoc (id X) h π)
right-unitor-comp {X} h π =
  let I = id X
      A = comp-assoc I h π
      B = comp-assoc I I (π ∘ h)
      C′ = comp-assoc (I ∘ I) h π
      D′ = comp-assoc I (h ∘ I) π
      E = A ▷ I
      L = comp-unitˡ I
      q = (π ∘ h) ◁ L
      t = π ◁ (h ◁ L)
      s = π ◁ comp-assoc I I h
      u = comp-unitʳ (π ∘ h)
      v = (π ◁ comp-unitʳ h) ∙ A
      left-normal = isoComp-assoc-at t C′ B ∙
        (isoComp-cong (postWhisker-comp-at L h π) (idIso B) ∙
        ((isoComp-assoc-at A q B) ⁻¹ ∙
          isoComp-cong (idIso A) (triangle-whiskered I (π ∘ h))))
      triangle-h = postWhisker-isoComp-at π (h ◁ L) (comp-assoc I I h) ∙
        (postWhisker π ◁ triangle-whiskered I h)
      right-normal = isoComp-cong (idIso t) ((pentagon-whiskered I I h π) ⁻¹) ∙
        (isoComp-assoc-at t s (D′ ∙ E) ∙
        (isoComp-cong triangle-h (idIso (D′ ∙ E)) ∙
        (isoComp-assoc-at (π ◁ (comp-unitʳ h ▷ I)) D′ E ∙
        (isoComp-cong (whisker-mixed-at (comp-unitʳ h) I π) (idIso E) ∙
        ((isoComp-assoc-at A ((π ◁ comp-unitʳ h) ▷ I) E) ⁻¹ ∙
          isoComp-cong (idIso A) (preWhisker-isoComp-at (π ◁ comp-unitʳ h) A I))))))
  in preWhisker-id-reflect (cancel-left-reflect A (right-normal ⁻¹ ∙ left-normal))
```

After projecting the pairing comparison, its defining triangles reduce the
claim to naturality of the right unitor and the compatibility just proved.

```agda
unit-square-projection : {X K C : CAT} (π : MAP K C)
  (h : MAP X K) (f : MAP X C) (b : (π ∘ h) =₁ f)
  →
      (comp-unitʳ f ∙ ((b ▷ id X) ∙ (comp-assoc (id X) h π) ⁻¹)) =₂
      (b ∙ (π ◁ comp-unitʳ h))
unit-square-projection {X} π h f b =
  let A = comp-assoc (id X) h π
      normalize = cancel-right A (π ◁ comp-unitʳ h) ∙
        isoComp-cong (right-unitor-comp h π) (idIso (A ⁻¹))
  in isoComp-cong (idIso b) normalize ∙
    (isoComp-assoc-at b (comp-unitʳ (π ∘ h)) (A ⁻¹) ∙
    (isoComp-cong (preWhisker-id-at b) (idIso (A ⁻¹)) ∙
      (isoComp-assoc-at (comp-unitʳ f) (b ▷ id X) (A ⁻¹)) ⁻¹))

unit-projection : {X K C : CAT} (π : MAP K C)
  (h h′ : MAP X K) (f : MAP X C)
  (b : (π ∘ h) =₁ f) (c′ : (π ∘ h′) =₁ (f ∘ id X))
  (ρ : h′ =₁ h) (τ : (h ∘ id X) =₁ h′)
  → (b ∙ (π ◁ ρ)) =₂ (comp-unitʳ f ∙ c′)
  → (c′ ∙ (π ◁ τ)) =₂ ((b ▷ id X) ∙ (comp-assoc (id X) h π) ⁻¹)
  → (π ◁ (ρ ∙ τ)) =₂ (π ◁ comp-unitʳ h)
unit-projection π h h′ f b c′ ρ τ top bottom =
  cancel-left-reflect b
    (unit-square-projection π h f b ∙
    (isoComp-cong (idIso (comp-unitʳ f)) bottom ∙
    (isoComp-assoc-at (comp-unitʳ f) c′ (π ◁ τ) ∙
    (isoComp-cong top (idIso (π ◁ τ)) ∙ project-composite π ρ τ b))))

pair-pre-id : {X C D : CAT} (f : MAP X C) (g : MAP X D)
  →
      (pair-cong (comp-unitʳ f) (comp-unitʳ g) ∙ pair-pre f g (id X)) =₂
      (comp-unitʳ (pair f g))
pair-pre-id {X} f g =
  let h = pair f g
      h′ = pair (f ∘ id X) (g ∘ id X)
      ρ = pair-cong (comp-unitʳ f) (comp-unitʳ g)
      τ = pair-pre f g (id X)
  in pair-iso-extensionality
    (unit-projection pr₁ h h′ f (pair-β₁ f g) (pair-β₁ (f ∘ id X) (g ∘ id X)) ρ τ
      (pair-cong-triangle₁ (comp-unitʳ f) (comp-unitʳ g)) (pair-pre-triangle₁ f g (id X)))
    (unit-projection pr₂ h h′ g (pair-β₂ f g) (pair-β₂ (f ∘ id X) (g ∘ id X)) ρ τ
      (pair-cong-triangle₂ (comp-unitʳ f) (comp-unitʳ g)) (pair-pre-triangle₂ f g (id X)))
```
