# Evaluating a pair along a section

If a projection has a specified section, evaluating a pair along that
section agrees with evaluating its two coordinates. This lemma packages
the pairing unit, substitution naturality, and substitution composition
into one comparison with all boundary identifications retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.PairSectionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.IsomorphismReasoning 𝒯
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp)
open Naturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-substitution; pair-pre-natural-inputs)
open PairUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-id)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated)

module At {X K A B : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ (id X)) (u : MAP X A) (v : MAP X B) where
  j = pair u v
  ru = comp-unitʳ u
  rv = comp-unitʳ v
  units = pair-cong ru rv
  inputs = pair-cong (u ◁ b) (v ◁ b)
  au = comp-assoc i π u
  av = comp-assoc i π v
  assoc = comp-assoc i π j
  associators = pair-cong au av
  before = pair-pre u v (π ∘ i)
  after = pair-pre u v (id X)
  inner = pair-pre (u ∘ π) (v ∘ π) i
  outer = pair-pre u v π ▷ i
  coordinates = pair-cong (section-image π i b u) (section-image π i b v)

  abstract
    expand-unit : section-image π i b j =₂
      (units ∙ (after ∙ ((j ◁ b) ∙ assoc)))
    expand-unit = isoComp-assoc-at units after ((j ◁ b) ∙ assoc) ∙
      isoComp-cong ((pair-pre-id u v) ⁻¹) (idIso ((j ◁ b) ∙ assoc))

    change-input : (units ∙ (after ∙ ((j ◁ b) ∙ assoc))) =₂
      (units ∙ (inputs ∙ (before ∙ assoc)))
    change-input = isoComp-cong (idIso units)
      (isoComp-assoc-at inputs before assoc ∙
      (isoComp-cong ((pair-pre-natural-substitution u v b) ⁻¹) (idIso assoc) ∙
        (isoComp-assoc-at after (j ◁ b) assoc) ⁻¹))

    compose-inputs : (units ∙ (inputs ∙ (before ∙ assoc))) =₂
      (units ∙ (inputs ∙ (associators ∙ (inner ∙ outer))))
    compose-inputs = isoComp-cong (idIso units)
      (isoComp-cong (idIso inputs) (pair-pre-iterated u v π i))

    collect-coordinates : (units ∙ (inputs ∙ associators)) =₂ coordinates
    collect-coordinates = (pair-cong-comp ru ((u ◁ b) ∙ au) rv ((v ◁ b) ∙ av)) ⁻¹ ∙
      isoComp-cong (idIso units) ((pair-cong-comp (u ◁ b) au (v ◁ b) av) ⁻¹)

    finish : (units ∙ (inputs ∙ (associators ∙ (inner ∙ outer)))) =₂
      (coordinates ∙ (inner ∙ outer))
    finish = isoComp-cong collect-coordinates (idIso (inner ∙ outer)) ∙
      ((isoComp-assoc-at units (inputs ∙ associators) (inner ∙ outer)) ⁻¹ ∙
        isoComp-cong (idIso units) ((isoComp-assoc-at inputs associators (inner ∙ outer)) ⁻¹))

    comparison : section-image π i b (pair u v) =₂
      (pair-cong (section-image π i b u) (section-image π i b v) ∙
        (pair-pre (u ∘ π) (v ∘ π) i ∙ (pair-pre u v π ▷ i)))
    comparison = begin₂
      section-image π i b j =₂⟨ expand-unit ⟩
      (units ∙ (after ∙ ((j ◁ b) ∙ assoc))) =₂⟨ change-input ⟩
      (units ∙ (inputs ∙ (before ∙ assoc))) =₂⟨ compose-inputs ⟩
      (units ∙ (inputs ∙ (associators ∙ (inner ∙ outer)))) =₂⟨ finish ⟩
      (coordinates ∙ (inner ∙ outer)) ∎₂
```

A comparison into the pair may be supplied before evaluating the section.
Its two coordinate comparisons are then retained in the result.

```agda
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module ComparedInputs {X K A B : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ (id X)) (u : MAP X A) (v : MAP X B)
  {f : MAP K A} {g : MAP K B} (α : f =₁ (u ∘ π)) (β : g =₁ (v ∘ π)) where
  module Base = At π i b u v
  input = pair-cong α β
  before = pair-pre u v π
  after = pair-pre (u ∘ π) (v ∘ π) i
  out = before ⁻¹ ∙ input
  image = input ▷ i
  step = pair-pre f g i
  cu = section-image π i b u
  cv = section-image π i b v
  coordinates = pair-cong cu cv
  changed = pair-cong (α ▷ i) (β ▷ i)

  abstract
    restricted : (out ▷ i) =₂ ((before ▷ i) ⁻¹ ∙ image)
    restricted = isoComp-cong (pre-inverse before i) (idIso image) ∙
      preWhisker-isoComp-at (before ⁻¹) input i

    cancel-comparison :
      ((coordinates ∙ (after ∙ (before ▷ i))) ∙ ((before ▷ i) ⁻¹ ∙ image)) =₂
      (coordinates ∙ (after ∙ image))
    cancel-comparison = isoComp-cong (idIso coordinates)
        (isoComp-cong (idIso after) (cancel-inverse (before ▷ i) image) ∙
          isoComp-assoc-at after (before ▷ i) ((before ▷ i) ⁻¹ ∙ image)) ∙
      isoComp-assoc-at coordinates (after ∙ (before ▷ i)) ((before ▷ i) ⁻¹ ∙ image)

    comparison : (section-image π i b (pair u v) ∙ (out ▷ i)) =₂
      (pair-cong (cu ∙ (α ▷ i)) (cv ∙ (β ▷ i)) ∙ pair-pre f g i)
    comparison = isoComp-cong ((pair-cong-comp cu (α ▷ i) cv (β ▷ i)) ⁻¹) (idIso step) ∙
      ((isoComp-assoc-at coordinates changed step) ⁻¹ ∙
      (isoComp-cong (idIso coordinates) ((pair-pre-natural-inputs α β i) ⁻¹) ∙
      (cancel-comparison ∙ isoComp-cong Base.comparison restricted)))
```
