# Squares and their specified commutativity

The square in `def:Pushout_Square` includes its natural isomorphism.
We use the book's orientation: `u` is the top arrow, `v` the bottom
arrow, and the comparison goes from the top-right route to the
bottom-left route. No pushout object is postulated.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section08.Squares
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯

record Square {A B C D : CAT}
  (u : MAP A B) (l : MAP A C) (r : MAP B D) (v : MAP C D) : Set m where
  field
    commute : NatIso (r ∘ u) (v ∘ l)

module PastedSquare {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) where

  outer : Square (g₂ ∘ g₁) f₁ f₃ (h₂ ∘ h₁)
  outer = record { commute =
    invIso (comp-assoc f₁ h₁ h₂) ∙
      ((h₂ ◁ Square.commute left) ∙
      (comp-assoc g₁ f₂ h₂ ∙
      ((Square.commute right ▷ g₁) ∙ invIso (comp-assoc g₁ g₂ f₃)))) }
```
