# Transporting a cocone universal property

A whole cocone comparison transports extension and reflection. A
specified change of the top span arrow does the same, with the matching
transported by that identification. These operations keep the data
needed by the subsequent pushout-pasting arguments.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoconeUniversalTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯
  using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout; module PastedSquare)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.PushoutExtensions 𝒯 M P using (pushout-extension-property)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeArrowRestriction as ArrowRestriction
module Arrow = ArrowRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePasting 𝒯 using (module PasteCocones)

module Invariant {A B C D : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cocone u v D} (Φ : CoconeIso s t) (universal : CoconeExtensionProperty s) where
  module Original = CoconeExtensionProperty universal
  abstract
    extensions : CoconeExtensionProperty t
    extensions = record
      { factor = Original.factor
      ; factor-β = λ E q → coconeIso-compose (Original.factor-β E q)
          (coconeIso-post (Original.factor E q) (coconeIso-inverse Φ))
      ; reflect = λ E f g Ψ → Original.reflect E f g
          (coconeIso-compose (coconeIso-post g (coconeIso-inverse Φ))
            (coconeIso-compose Ψ (coconeIso-post f Φ))) }

module ChangeTop {A B C D : CAT} {u u′ : MAP A B} {v : MAP A C}
  (α : u =₁ u′) (s : Cocone u′ v D) (universal : CoconeExtensionProperty s) where
  module Original = CoconeExtensionProperty universal
  value = Arrow.restrict α s
  module RoundTrip {E : CAT} (t : Cocone u v E) where
    r = Cocone.left t
    τ = Cocone.match t
    d = r ◁ α
    abstract
      matching : Cocone.match (Arrow.restrict α (Arrow.restrict (α ⁻¹) t)) =₂ τ
      matching = isoComp-unitʳ-at τ ∙
        (isoComp-cong (idIso τ) (isoComp-inverseˡ-at d) ∙
          (isoComp-assoc-at τ (d ⁻¹) d ∙
            isoComp-cong (isoComp-cong (idIso τ) (post-inverse r α)) (idIso d)))
      comparison : CoconeIso (Arrow.restrict α (Arrow.restrict (α ⁻¹) t)) t
      comparison = cocone-match-change _ _ _ _ matching
  abstract
    extensions : CoconeExtensionProperty value
    extensions = record
      { factor = λ E t → Original.factor E (Arrow.restrict (α ⁻¹) t)
      ; factor-β = λ E t → coconeIso-compose (RoundTrip.comparison t)
          (coconeIso-compose (Arrow.restrict-iso α (Original.factor-β E (Arrow.restrict (α ⁻¹) t)))
            (coconeIso-inverse (Arrow.postcomparison α (Original.factor E (Arrow.restrict (α ⁻¹) t)) s)))
      ; reflect = λ E f g Φ → Original.reflect E f g
          (Arrow.reflect-iso α (coconePost f s) (coconePost g s)
            (coconeIso-compose (coconeIso-inverse (Arrow.postcomparison α g s))
              (coconeIso-compose Φ (Arrow.postcomparison α f s)))) }


module Pasted {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃} {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) where
  module Paste = PasteCocones g₁ g₂ left
  outer = PastedSquare.outer left right
  lower = (comp-assoc f₁ h₁ h₂) ⁻¹
  middle = h₂ ◁ Square.commute left
  next = comp-assoc g₁ f₂ h₂
  tail = (Square.commute right ▷ g₁) ∙ (comp-assoc g₁ g₂ f₃) ⁻¹
  abstract
    matching : Cocone.match (Paste.flatten (squareCocone right)) =₂ Square.commute outer
    matching = isoComp-cong (idIso lower) (isoComp-assoc-at middle next tail) ∙
      isoComp-assoc-at lower (middle ∙ next) tail
    comparison : CoconeIso (Paste.flatten (squareCocone right)) (squareCocone outer)
    comparison = cocone-match-change _ _ _ _ matching
```
