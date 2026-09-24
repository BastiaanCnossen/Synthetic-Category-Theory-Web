# Intersecting two inverse conditions

Suppose a category is the pullback of two categories of witnesses. If each
kind of witness is unique over its common underlying arrow, then the
combined witness is unique too. The proof only uses nested pullbacks,
including their specified matching identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section03.IntersectionEmbedding
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks 𝒯 P using (module Nested)
import SCT.VolumeI.Chapter01.Section06.UniversalNestedPullbacks as UniversalNested

swap-projection : {A B E : CAT} (f : MAP A E) (g : MAP B E) →
  IsEquiv (pullback₂ {f = f} {g}) → IsEquiv (pullback₁ {f = g} {f})
swap-projection f g e = equiv-cancel-right (pullbackSwap f g) pullback₁
  (pullbackSwap-isEquiv f g)
  (equiv-transport ((pullbackLift-β₁ (coneSwap (pullbackCone f g))) ⁻¹) e)

change-right-projection : {A B E : CAT} (f : MAP A E) {g h : MAP B E} →
  g =₁ h → IsEquiv (pullback₂ {f = f} {h}) → IsEquiv (pullback₂ {f = f} {g})
change-right-projection f {g} {h} α e = equiv-cancel-right (pullbackSwap g f) pullback₂
  (pullbackSwap-isEquiv g f)
  (equiv-transport ((pullbackLift-β₂ (coneSwap (pullbackCone g f))) ⁻¹)
    (equiv-transport (pullbackLift-β₁ (changeLeft α (pullbackCone g f)))
      (equiv-compose Change.forward pullback₁ Change.forward-isEquiv (swap-projection f h e))))
  where module Change = ChangeLeft α f

module Intersection {R L A I : CAT} (r : MAP R A) (l : MAP L A)
  (s : Cone r l I) (es : IsPullback s) where

  p = Cone.left s
  i = r ∘ p
  K = Pullback r i
  u : MAP K R
  u = pullback₁
  v : MAP K I
  v = pullback₂

  module Boundary = ChangeLeft (pullbackMatch {f = r} {i}) l
  module Inner = UniversalNested.Nested 𝒯 P u r l s es
  module Outer = Nested p r i

  embedding : IsEquiv (pullback₂ {f = r} {i}) →
    IsEquiv (pullback₂ {f = l} {i}) → IsEmbedding i
  embedding er el = projection-embedding i
    (swap-projection i i self-second)
    where
    other-first = swap-projection l i el
    restricted-first = nested-projection v i l other-first
    changed-first = equiv-transport
      (pullbackLift-β₁ (changeLeft (pullbackMatch {f = r} {i}) (pullbackCone (r ∘ u) l)))
      (equiv-compose Boundary.forward pullback₁ Boundary.forward-isEquiv restricted-first)
    inner-first = equiv-transport (pullbackLift-β₁ Inner.flatCone)
      (equiv-compose Inner.flatten pullback₁ Inner.flatten-isEquiv changed-first)
    outer-second = equiv-cancel-right (pullbackSwap u p) pullback₂
      (pullbackSwap-isEquiv u p)
      (equiv-transport ((pullbackLift-β₂ (coneSwap (pullbackCone u p))) ⁻¹) inner-first)
    self-second = equiv-cancel-right Outer.flatten pullback₂ Outer.flatten-isEquiv
      (equiv-transport ((pullbackLift-β₂ Outer.flatCone) ⁻¹)
        (equiv-compose pullback₂ v outer-second er))
```
