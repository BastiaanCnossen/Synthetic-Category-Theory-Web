# Reducing the terminal coordinate after postcomposition

Decoding a named functor removes its terminal coordinate. The reduction
commutes with postcomposition, using the specified associator, unitor,
and retraction. This is the structural part of the naming coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnitLaws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointReductionCoherence
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pentagon-whiskered)
open PairingUnitLaws vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (right-unitor-comp)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (reassociateFour)

module Reduction {B X : CAT} (i : MAP B X) (r : MAP X B) (e : (r ∘ i) =₁ id B) where
  reduce : {C : CAT} (h : MAP B C) → ((h ∘ r) ∘ i) =₁ h
  reduce h = comp-unitʳ h ∙ ((h ◁ e) ∙ comp-assoc i r h)

  module Post {C D : CAT} (h : MAP B C) (g : MAP C D) where
    A₀ : ((g ∘ h) ∘ id B) =₁ (g ∘ (h ∘ id B))
    A₀ = comp-assoc (id B) h g
    A₁ : (((g ∘ h) ∘ r) ∘ i) =₁ ((g ∘ (h ∘ r)) ∘ i)
    A₁ = comp-assoc r h g ▷ i
    A₂ : ((g ∘ (h ∘ r)) ∘ i) =₁ (g ∘ ((h ∘ r) ∘ i))
    A₂ = comp-assoc i (h ∘ r) g
    A₃ : ((h ∘ r) ∘ i) =₁ (h ∘ (r ∘ i))
    A₃ = comp-assoc i r h
    A₄ : ((g ∘ h) ∘ (r ∘ i)) =₁ (g ∘ (h ∘ (r ∘ i)))
    A₄ = comp-assoc (r ∘ i) h g
    A₅ : (((g ∘ h) ∘ r) ∘ i) =₁ ((g ∘ h) ∘ (r ∘ i))
    A₅ = comp-assoc i r (g ∘ h)
    ρ : (h ∘ id B) =₁ h
    ρ = comp-unitʳ h

    abstract
      merge : ((g ◁ ρ) ∙ ((g ◁ (h ◁ e)) ∙ (g ◁ A₃))) =₂ (g ◁ reduce h)
      merge = (postWhisker-isoComp-at g ρ ((h ◁ e) ∙ A₃)) ⁻¹ ∙
        isoComp-cong (idIso (g ◁ ρ)) ((postWhisker-isoComp-at g (h ◁ e) A₃) ⁻¹)

      composition-comparison : reduce (g ∘ h) =₂ ((g ◁ reduce h) ∙ (A₂ ∙ A₁))
      composition-comparison = isoComp-cong merge (idIso (A₂ ∙ A₁)) ∙
        ((isoComp-assoc-at (g ◁ ρ) ((g ◁ (h ◁ e)) ∙ (g ◁ A₃)) (A₂ ∙ A₁)) ⁻¹ ∙
          (isoComp-cong (idIso (g ◁ ρ)) ((isoComp-assoc-at (g ◁ (h ◁ e)) (g ◁ A₃) (A₂ ∙ A₁)) ⁻¹) ∙
            (isoComp-cong (idIso (g ◁ ρ)) (isoComp-cong (idIso (g ◁ (h ◁ e))) (pentagon-whiskered i r h g)) ∙
              (isoComp-cong (idIso (g ◁ ρ)) (isoComp-assoc-at (g ◁ (h ◁ e)) A₄ A₅) ∙
                (isoComp-cong (idIso (g ◁ ρ)) (isoComp-cong (postWhisker-comp-at e h g) (idIso A₅)) ∙
                  (reassociateFour (g ◁ ρ) A₀ ((g ∘ h) ◁ e) A₅ ∙
                    isoComp-cong (right-unitor-comp h g) (idIso (((g ∘ h) ◁ e) ∙ A₅))))))))

      cancel-associator : (reduce (g ∘ h) ∙ (comp-assoc r h g ⁻¹ ▷ i)) =₂
        ((g ◁ reduce h) ∙ A₂)
      cancel-associator = cancel-right A₁ ((g ◁ reduce h) ∙ A₂) ∙
        isoComp-cong ((isoComp-assoc-at (g ◁ reduce h) A₂ A₁) ⁻¹ ∙ composition-comparison)
          (pre-inverse (comp-assoc r h g) i)
```
