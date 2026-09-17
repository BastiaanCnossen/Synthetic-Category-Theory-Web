# Constant diagrams and composition

The pentagon and unit coherence identify the endpoint comparison for the
constant diagram of a composite with the composite endpoint comparison.
This is the boundary calculation for preservation of identity morphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.IdentityBoundaries
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairUnits
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
open Structural vocabulary terminal products productLaws composition whiskering
open PairUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (right-unitor-comp)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

evaluate-boundary : {Γ W C : CAT} (i : MAP Γ W) (p : MAP W Γ) →
  =₁ (p ∘ i) (id Γ) → (f : MAP Γ C) → =₁ ((f ∘ p) ∘ i) f
evaluate-boundary i p b f = comp-unitʳ f ∙ ((f ◁ b) ∙ comp-assoc i p f)
module EvaluationBoundary {Γ W C D : CAT} (i : MAP Γ W) (p : MAP W Γ)
  (b : =₁ (p ∘ i) (id Γ)) (F : MAP C D) (f : MAP Γ C) where
  u = comp-unitʳ f
  v = f ◁ b
  w = comp-assoc i p f
  t = comp-assoc i (f ∘ p) F
  z = comp-assoc p f F ▷ i
  A₀ = comp-assoc i p (F ∘ f)
  A₁ = comp-assoc (id Γ) f F
  A₂ = comp-assoc (p ∘ i) f F

  abstract
    prefix : =₂ (evaluate-boundary i p b (F ∘ f))
      ((F ◁ u) ∙ ((F ◁ v) ∙ (A₂ ∙ A₀)))
    prefix = isoComp-cong (idIso (F ◁ u)) (isoComp-assoc-at (F ◁ v) A₂ A₀) ∙
      (isoComp-cong (idIso (F ◁ u))
        (isoComp-cong (postWhisker-comp-at b f F) (idIso A₀)) ∙
      (isoComp-cong (idIso (F ◁ u)) (invIso (isoComp-assoc-at A₁ ((F ∘ f) ◁ b) A₀)) ∙
      (isoComp-assoc-at (F ◁ u) A₁ (((F ∘ f) ◁ b) ∙ A₀) ∙
        isoComp-cong (right-unitor-comp f F) (idIso (((F ∘ f) ◁ b) ∙ A₀)))))

    forward : =₂ (evaluate-boundary i p b (F ∘ f)) (((F ◁ evaluate-boundary i p b f) ∙ t) ∙ z)
    forward = invIso (isoComp-assoc-at (F ◁ evaluate-boundary i p b f) t z) ∙
      (isoComp-cong (invIso (postWhisker-isoComp-at F u (v ∙ w))) (idIso (t ∙ z)) ∙
      (isoComp-cong (isoComp-cong (idIso (F ◁ u)) (invIso (postWhisker-isoComp-at F v w))) (idIso (t ∙ z)) ∙
      (invIso (isoComp-assoc-at (F ◁ u) ((F ◁ v) ∙ (F ◁ w)) (t ∙ z)) ∙
      (isoComp-cong (idIso (F ◁ u)) (invIso (isoComp-assoc-at (F ◁ v) (F ◁ w) (t ∙ z))) ∙
      (isoComp-cong (idIso (F ◁ u)) (isoComp-cong (idIso (F ◁ v)) (pentagon-whiskered i p f F)) ∙
        prefix)))))

    comparison : =₂ (evaluate-boundary i p b (F ∘ f) ∙ (invIso (comp-assoc p f F) ▷ i))
      ((F ◁ evaluate-boundary i p b f) ∙ comp-assoc i (f ∘ p) F)
    comparison = cancel-right z ((F ◁ evaluate-boundary i p b f) ∙ t) ∙
      isoComp-cong forward (pre-inverse (comp-assoc p f F) i)
module Boundary {Γ C D : CAT} (x : Obj-abs [1]) (F : MAP C D) (f : MAP Γ C) =
  EvaluationBoundary (insert x) pr₁ (pair-β₁ (id Γ) (const x)) F f
```
