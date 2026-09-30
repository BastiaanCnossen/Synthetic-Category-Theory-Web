# Replacing the projection categories of a pullback square

Equivalences over the two projection bases replace the upper-left and
upper-right vertices of a pullback square. The new right leg is the
specified projection. Its matching is transported from the original
square, and the complete comparison before retargeting is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackReindexing
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Cospans

module Along {A A′ B D T T′ : CAT} {f : MAP A B} {g : MAP D B}
  (s : Cone f g T) (es : IsPullback s)
  (f′ : MAP A′ B) (u : MAP A A′) (eu : IsEquiv u) (α : (f′ ∘ u) =₁ f)
  (p′ : MAP T′ D) (v : MAP T T′) (ev : IsEquiv v) (β : (p′ ∘ v) =₁ Cone.right s) where
  private
    J = IsEquiv.inverse ev

  cospan : CospanMap f g f′ g
  cospan = record { left = u ; right = id D ; base = id B
    ; leftSquare = (comp-unitˡ f) ⁻¹ ∙ α
    ; rightSquare = (comp-unitˡ g) ⁻¹ ∙ comp-unitʳ g }

  mapped = CospanMap.mapCone cospan s
  restricted = conePre J mapped

  inverse-projection : (Cone.right s ∘ J) =₁ p′
  inverse-projection = comp-unitʳ p′ ∙
    ((p′ ◁ (IsEquiv.retractionIso ev) ⁻¹) ∙
    (comp-assoc J v p′ ∙ (β ▷ J) ⁻¹))

  private
    right-frame : Cone.right restricted =₁ p′
    right-frame = inverse-projection ∙
      (comp-unitˡ (Cone.right s ∘ J) ∙ comp-assoc J (Cone.right s) (id D))
    module Preserved = Cospans.Mapped 𝒯 P cospan
      (degenerate-pullback (id-isEquiv B) (Cospans.rightSquareOf 𝒯 P cospan) (id-isEquiv D))
      s es using (isPullback)
    abstract
      inverse-isEquiv : IsEquiv J
      inverse-isEquiv = record { inverse = v
        ; sectionIso = IsEquiv.retractionIso ev ; retractionIso = IsEquiv.sectionIso ev }

  square : Cone f′ g T′
  square = coneRetarget restricted (Cone.left restricted) p′ (idIso (Cone.left restricted)) right-frame

  abstract
    computation : ConeIso restricted square
    computation = coneRetarget-β restricted (Cone.left restricted) p′ (idIso (Cone.left restricted)) right-frame

    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant computation
      (pullback-restrict-equivalence mapped J (Preserved.isPullback eu) inverse-isEquiv)
```
