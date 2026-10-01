# Restoring the boundary of a reflected identification

Suppose an identification was reflected after changing its two endpoints.
Its image comes with the specified comparison to the changed identification.
Restoring the endpoints then gives the original identification. This is a
vertical calculation; it uses neither whiskering nor a reflection operation.
The proof remains transparent to retain the chosen higher witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.BoundaryTransport
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S hiding (module Whiskering)
open Specialization.Units V T P PL S VC

open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses V T P PL S VC using (cancel-right)

restore-boundaries : {X C : CAT} {f f′ g g′ : MAP X C}
  (left : f′ =₁ f) (right : g′ =₁ g) (desired : f =₁ g)
  (image : f′ =₁ g′) → image =₂ (right ⁻¹ ∙ (desired ∙ left)) →
  (right ∙ (image ∙ left ⁻¹)) =₂ desired
restore-boundaries left right desired image β = cancel-right left desired ∙
  (isoComp-cong cancellation (idIso (left ⁻¹)) ∙
    ((isoComp-assoc-at right (right ⁻¹ ∙ (desired ∙ left)) (left ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso right) (isoComp-cong β (idIso (left ⁻¹)))))
  where
  cancellation : (right ∙ (right ⁻¹ ∙ (desired ∙ left))) =₂ (desired ∙ left)
  cancellation = isoComp-unitˡ-at (desired ∙ left) ∙
    (isoComp-cong (isoComp-inverseʳ-at right) (idIso (desired ∙ left)) ∙
      (isoComp-assoc-at right (right ⁻¹) (desired ∙ left)) ⁻¹)
```
