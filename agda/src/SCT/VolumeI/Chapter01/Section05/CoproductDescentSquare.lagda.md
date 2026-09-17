# The coproduct descent square

The direct square copairs the two universal pullback matchings. We compare
it with the square inherited from the descent equivalence, including an
explicit identification of their matchings after the projection comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section05.CoproductDescentSquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.CoproductDescent 𝒯 M B P U using (module Descent)
open import SCT.VolumeI.Chapter01.Section05.BaseChangeInclusion 𝒯 P using (module Inclusion)
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯 using (coneRetarget-match)
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯 using (coneIso-compose; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section05.CoproductCones 𝒯 M B using (module CopairComparison)
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
  using (IsPullback; pbCone-isPullback; pullback-cone-invariant; pullback-restrict-equivalence)

module DescentSquare {C D Γ Γ′ : CAT} (f : MAP C Γ) (g : MAP D Γ) (φ : MAP Γ′ Γ) where
  module Dsc = Descent f g φ
  module Left = Inclusion in₁ (copair f g) φ (invIso (copair-β₁ f g))
  module Right = Inclusion in₂ (copair f g) φ (invIso (copair-β₂ f g))
  original = conePre Dsc.descent (pbCone (copair f g) φ)
  left = copair (in₁ ∘ pb₁ {f = f} {φ}) (in₂ ∘ pb₁ {f = g} {φ})
  right = copair (pb₂ {f = f} {φ}) (pb₂ {f = g} {φ})

  opaque
    restriction₁ : ConeIso (conePre in₁ original) Left.directCone
    restriction₁ = coneIso-compose Left.include-comparison
      (coneIso-compose (cone-action (pbCone (copair f g) φ) (copair-β₁ Dsc.include₁ Dsc.include₂))
        (conePre-assoc in₁ Dsc.descent (pbCone (copair f g) φ)))

    restriction₂ : ConeIso (conePre in₂ original) Right.directCone
    restriction₂ = coneIso-compose Right.include-comparison
      (coneIso-compose (cone-action (pbCone (copair f g) φ) (copair-β₂ Dsc.include₁ Dsc.include₂))
        (conePre-assoc in₂ Dsc.descent (pbCone (copair f g) φ)))

  module Copaired = CopairComparison original Left.directCone Right.directCone restriction₁ restriction₂
  left-comparison = ConeIso.leftIso Copaired.comparison
  right-comparison = ConeIso.rightIso Copaired.comparison

  direct-square : Cone (copair f g) φ (Pullback f φ ⊔ Pullback g φ)
  direct-square = Copaired.Copair.value

  square : Cone (copair f g) φ (Pullback f φ ⊔ Pullback g φ)
  square = coneRetarget original left right left-comparison right-comparison

  matching-comparison : Iso₂ (Cone.match square) (Cone.match direct-square)
  matching-comparison = coneRetarget-match Copaired.comparison

  direct-square-isPullback : IsPullback direct-square
  direct-square-isPullback = pullback-cone-invariant Copaired.comparison
    (pullback-restrict-equivalence (pbCone (copair f g) φ) Dsc.descent (pbCone-isPullback (copair f g) φ) Dsc.descent-isEquiv)

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant (coneRetarget-β original left right left-comparison right-comparison)
    (pullback-restrict-equivalence (pbCone (copair f g) φ) Dsc.descent (pbCone-isPullback (copair f g) φ) Dsc.descent-isEquiv)
```
