# Retaining the common diagonal when gluing

The gluing identification is the quotient of the two specified maps to
the diagonal. Restriction preserves this quotient, so both restricted
triangles give the same comparison with the diagonal edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionIdentificationComposition as Identifications
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.CommonRestrictionDiagonal
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-right; cancel-left-reflect)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

module At {A K B C : CAT} (d : MAP A K) (j k : MAP K B) (r : MAP A B)
  (α : (j ∘ d) =₁ r) (β : (k ∘ d) =₁ r) where
  p = preComp {E = C} d j
  q = preComp {E = C} d k
  u = preCong {E = C} α
  v = preCong {E = C} β
  t = preCong {E = C} (β ⁻¹ ∙ α)
  matching = q ⁻¹ ∙ (t ∙ p)
  first = u ∙ p
  second = v ∙ q
  first-back = p ⁻¹ ∙ u ⁻¹
  second-back = q ⁻¹ ∙ v ⁻¹

  abstract
    forward : (second ∙ matching) =₂ first
    forward = isoComp-cong
        (Identifications.At.triangle 𝒯 M ℱ P β (β ⁻¹ ∙ α) α (cancel-inverse β α)) (idIso p) ∙
      (isoComp-assoc-at v t p) ⁻¹ ∙
      isoComp-cong (idIso v) (cancel-inverse q (t ∙ p)) ∙
      isoComp-assoc-at v q matching

    backward : (matching ∙ first-back) =₂ second-back
    backward = inverse-composite v q ∙
      cancel-left-reflect second
        ((isoComp-inverseʳ-at second) ⁻¹ ∙
        isoComp-inverseʳ-at first ∙
        isoComp-cong forward (idIso (first ⁻¹)) ∙
        (isoComp-assoc-at second matching (first ⁻¹)) ⁻¹) ∙
      isoComp-cong (idIso matching) ((inverse-composite u p) ⁻¹)

  module Family {Γ : CAT} (W : MAP Γ (Fun B C)) where
    aL = comp-assoc W (funPre j) (funPre d)
    aR = comp-assoc W (funPre k) (funPre d)
    specified = aR ∙ ((matching ▷ W) ∙ aL ⁻¹)
    left = aL ∙ ((p ▷ W) ⁻¹ ∙ (u ▷ W) ⁻¹)
    right = aR ∙ ((q ▷ W) ⁻¹ ∙ (v ▷ W) ⁻¹)

    abstract
      left-image : (first-back ▷ W) =₂ ((p ▷ W) ⁻¹ ∙ (u ▷ W) ⁻¹)
      left-image = isoComp-cong (pre-inverse p W) (pre-inverse u W) ∙
        preWhisker-isoComp-at (p ⁻¹) (u ⁻¹) W
      right-image : (second-back ▷ W) =₂ ((q ▷ W) ⁻¹ ∙ (v ▷ W) ⁻¹)
      right-image = isoComp-cong (pre-inverse q W) (pre-inverse v W) ∙
        preWhisker-isoComp-at (q ⁻¹) (v ⁻¹) W
      comparison : (specified ∙ left) =₂ right
      comparison = isoComp-cong (idIso aR)
          (right-image ∙ (preWhisker W ◁ backward) ∙
            (preWhisker-isoComp-at matching first-back W) ⁻¹) ∙
        isoComp-cong (idIso aR)
          (isoComp-cong (idIso (matching ▷ W)) (cancel-left aL (first-back ▷ W)) ∙
            isoComp-assoc-at (matching ▷ W) (aL ⁻¹) (aL ∙ (first-back ▷ W))) ∙
        isoComp-assoc-at aR ((matching ▷ W) ∙ aL ⁻¹) (aL ∙ (first-back ▷ W)) ∙
        isoComp-cong (idIso specified) (isoComp-cong (idIso aL) (left-image ⁻¹))
```
