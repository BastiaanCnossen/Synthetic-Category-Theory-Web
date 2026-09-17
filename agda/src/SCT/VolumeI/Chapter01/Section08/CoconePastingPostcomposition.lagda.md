# Postcomposition of a pasted square

Flattening the postcomposed right square agrees with postcomposition of
the specified outer square. The right comparison is the associator.
The compatibility is an instance of the previously proved coordinate
associativity calculation, including the book's chosen bracketing.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU

module SCT.VolumeI.Chapter01.Section08.CoconePastingPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste-factor)
open import SCT.VolumeI.Chapter01.Section08.ProductCompositionAssociativity 𝒯 M using (module CoordinateAssociativity)
open import SCT.VolumeI.Chapter01.Section08.CoconePasting 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module PastedPostcomposition {A₁ A₂ A₃ B₁ B₂ B₃ E : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) (z : MAP B₃ E) where

  module Paste = PasteCocones g₁ g₂ left
  outer : Square (g₂ ∘ g₁) f₁ f₃ (h₂ ∘ h₁)
  outer = PastedSquare.outer left right
  R : Cocone g₂ f₂ E
  R = coconePost z (squareCocone right)
  O : Cocone (g₂ ∘ g₁) f₁ E
  O = coconePost z (squareCocone outer)
  D = Cocone.match O
  A = comp-assoc g₁ g₂ (z ∘ f₃)
  J = comp-assoc h₁ h₂ z ▷ f₁
  τ = Cocone.match (Paste.flatten R)
  module Coordinate = CoordinateAssociativity f₁ f₂ f₃ h₁ h₂ z
    g₂ g₁ (g₂ ∘ g₁) (idIso (g₂ ∘ g₁))
    (Square.commute right) (Square.commute left) (Square.commute outer)

  abstract
    projection : Iso₂ (Square.commute outer ∙ (f₃ ◁ idIso (g₂ ∘ g₁)))
      (Coordinate.middle ∙ ((Square.commute right ▷ g₁) ∙ invIso (comp-assoc g₁ g₂ f₃)))
    projection = paste-factor (Square.commute right) (Square.commute left) ∙
      (isoComp-unitʳ-at (Square.commute outer) ∙
        isoComp-cong (idIso (Square.commute outer)) (postWhisker-idIso f₃ (g₂ ∘ g₁)))

    short-normal : Iso₂ Coordinate.short (D ∙ A)
    short-normal = isoComp-cong (idIso D)
      (isoComp-unitˡ-at A ∙
        isoComp-cong (postWhisker-idIso (z ∘ f₃) (g₂ ∘ g₁)) (idIso A))

    long-normal : Iso₂ ((J ∙ τ) ∙ A) Coordinate.long
    long-normal = isoComp-cong (idIso J) (Paste.flatten-match R) ∙ isoComp-assoc-at J τ A

    matching : Iso₂ D (J ∙ τ)
    matching = cancel-right-reflect A
      (invIso long-normal ∙ (Coordinate.comparison projection ∙ invIso short-normal))

  comparison : CoconeIso (Paste.flatten R) O
  comparison = record
    { leftIso = idIso (z ∘ f₃) ; rightIso = comp-assoc h₁ h₂ z
    ; compatible = matching ∙
        (isoComp-unitʳ-at D ∙ isoComp-cong (idIso D) (preWhisker-idIso (z ∘ f₃) (g₂ ∘ g₁))) }
```
