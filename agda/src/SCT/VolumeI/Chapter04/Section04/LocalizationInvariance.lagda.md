# Bousfield localization is invariant under identification

The square with identity horizontal functors and a specified
identification as its matching is a pullback. Adjoint-section base
change transports either Bousfield-localization structure along that
identification. No comparison of animae of structure witnesses is
asserted.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.LocalizationInvariance
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as Change

module Along {C D : CAT} {f g : MAP C D} (α : f =₁ g) where
  square : Cone f (id D) C
  square = record { left = id C ; right = g
    ; match = (comp-unitˡ g) ⁻¹ ∙ (α ∙ comp-unitʳ f) }
  abstract
    is-pullback : IsPullback square
    is-pullback = degenerate-pullback (id-isEquiv D) square (id-isEquiv C)

  private
    module TransportRight (w : RightBousfieldLocalization f) where
      module Changed = Change.Left 𝒯 M ℱ P I E S Q R
        (RightBousfieldLocalization.left-adjoint-section w) (id D) square is-pullback
        using (section; value; original-section)
      abstract
        value : RightBousfieldLocalization g
        value = record { section = Changed.section ; left-adjoint-section = Changed.value }
        comparison : RightBousfieldLocalization.section value =₁ RightBousfieldLocalization.section w
        comparison = comp-unitʳ (RightBousfieldLocalization.section w) ∙
          (Changed.original-section ∙ (comp-unitˡ Changed.section) ⁻¹)

    module TransportLeft (w : LeftBousfieldLocalization f) where
      module Changed = Change.Right 𝒯 M ℱ P I E S Q R
        (LeftBousfieldLocalization.right-adjoint-section w) (id D) square is-pullback
        using (section; value; original-section)
      abstract
        value : LeftBousfieldLocalization g
        value = record { section = Changed.section ; right-adjoint-section = Changed.value }
        comparison : LeftBousfieldLocalization.section value =₁ LeftBousfieldLocalization.section w
        comparison = comp-unitʳ (LeftBousfieldLocalization.section w) ∙
          (Changed.original-section ∙ (comp-unitˡ Changed.section) ⁻¹)

  right : RightBousfieldLocalization f → RightBousfieldLocalization g
  right = TransportRight.value
  left : LeftBousfieldLocalization f → LeftBousfieldLocalization g
  left = TransportLeft.value

  right-section : (w : RightBousfieldLocalization f) →
    RightBousfieldLocalization.section (right w) =₁ RightBousfieldLocalization.section w
  right-section = TransportRight.comparison

  left-section : (w : LeftBousfieldLocalization f) →
    LeftBousfieldLocalization.section (left w) =₁ LeftBousfieldLocalization.section w
  left-section = TransportLeft.comparison
```
