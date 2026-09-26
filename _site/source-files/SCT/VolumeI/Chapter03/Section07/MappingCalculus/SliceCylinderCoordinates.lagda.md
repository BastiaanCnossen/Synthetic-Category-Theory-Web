# Cylinder coordinates for slices

The slice definition places the interval before `Y`; the join pushout
places it after `X × Y`. Product symmetry and reassociation identify
these cylinders and preserve both endpoint insertions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section07.MappingCalculus.SliceCylinderCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
insert : {X : CAT} → Obj-abs [1] → MAP X (X × [1])
insert {X} e = pair (id X) (const e)

module Coordinates (X Y : CAT) where
  switch = productMap (id X) (swap {[1]} {Y})
  regroup = Associativity.backward X Y [1]
  reorder : MAP (X × ([1] × Y)) ((X × Y) × [1])
  reorder = regroup ∘ switch
  abstract
    reorder-isEquiv : IsEquiv reorder
    reorder-isEquiv = equiv-compose switch regroup
      (productMap-isEquiv (id X) (swap {[1]} {Y}) (id-isEquiv X) (swap-isEquiv [1] Y))
      (equiv-inverse (Associativity.forward-isEquiv X Y [1]))
  module Endpoint (e : Obj-abs [1]) where
    endpoint : MAP Y ([1] × Y)
    endpoint = pair (const e) (id Y)
    insertion : MAP (X × Y) (X × ([1] × Y))
    insertion = productMap (id X) endpoint
    H = productMap (id X) (insert {X = Y} e)
    abstract
      swapped : (swap ∘ endpoint) =₁ insert e
      swapped = pair-cong (pair-β₂ (const e) (id Y)) (pair-β₁ (const e) (id Y)) ∙
        pair-pre pr₂ pr₁ endpoint
      first : (pr₁ ∘ H) =₁ pr₁
      first = comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (insert e ∘ pr₂)
      second : ((pr₁ ∘ pr₂) ∘ H) =₁ pr₂
      second = comp-unitˡ pr₂ ∙ (project-pair₁ (id Y) (const e) pr₂ ∙
        ((pr₁ ◁ pair-β₂ (id X ∘ pr₁) (insert e ∘ pr₂)) ∙ comp-assoc H pr₂ pr₁))
      third : ((pr₂ ∘ pr₂) ∘ H) =₁ const e
      third = (e ◁ terminal-iso (terminate Y ∘ pr₂) (terminate (X × Y))) ∙
        (comp-assoc pr₂ (terminate Y) e ∙
          (project-pair₂ (id Y) (const e) pr₂ ∙
            ((pr₂ ◁ pair-β₂ (id X ∘ pr₁) (insert e ∘ pr₂)) ∙ comp-assoc H pr₂ pr₂)))
      regrouped : (regroup ∘ H) =₁ insert e
      regrouped = pair-cong
        (pair-projections ∙ (pair-cong first second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) H)) third ∙
        pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) H
      comparison : (reorder ∘ insertion) =₁ insert e
      comparison = regrouped ∙
        ((regroup ◁ (productMap-cong (comp-unitˡ (id X)) swapped ∙
          productMap-comp (id X) (id X) endpoint (swap {[1]} {Y}))) ∙
          comp-assoc insertion switch regroup)

      inverse-comparison : (IsEquiv.inverse reorder-isEquiv ∘ insert e) =₁ insertion
      inverse-comparison = equiv-reflect reorder-isEquiv _ insertion
        (comparison ⁻¹ ∙ (comp-unitˡ (insert e) ∙
          (((IsEquiv.retractionIso reorder-isEquiv) ⁻¹ ▷ insert e) ∙
            (comp-assoc (insert e) (IsEquiv.inverse reorder-isEquiv) reorder) ⁻¹)))
```
