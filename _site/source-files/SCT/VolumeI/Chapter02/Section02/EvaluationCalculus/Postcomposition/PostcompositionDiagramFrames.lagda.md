# Endpoint frames for successive postcomposition

The pentagon compares the endpoint frames of a diagram postcomposed
twice. Naturality then allows an identification of the composite functor.
These are scalar pasting calculations, independent of the Segal axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.PostcompositionDiagramFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; preWhisker-comp-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {Γ W B A D : CAT} (i : MAP Γ W) (H : MAP W B)
  (r : MAP B A) (s : MAP A D) (t : MAP B D) (η : (s ∘ r) =₁ t)
  {x : MAP Γ B} (p : (H ∘ i) =₁ x) where
  inner = (r ◁ p) ∙ comp-assoc i H r
  twice = (s ◁ inner) ∙ comp-assoc i (r ∘ H) s
  composite = ((s ∘ r) ◁ p) ∙ comp-assoc i H (s ∘ r)
  output = (t ◁ p) ∙ comp-assoc i H t
  aH = comp-assoc H r s
  ax = comp-assoc x r s
  ai = comp-assoc (H ∘ i) r s
  b = comp-assoc i H r
  d = comp-assoc i (r ∘ H) s
  e = comp-assoc i H (s ∘ r)
  N = s ◁ (r ◁ p)
  L = (s ◁ b) ∙ d
  change = (η ▷ x) ∙ ax ⁻¹
  diagram = (η ▷ H) ∙ aH ⁻¹

  abstract
    normalize : twice =₂ (N ∙ L)
    normalize = isoComp-assoc-at N (s ◁ b) d ∙
      isoComp-cong (postWhisker-isoComp-at s (r ◁ p) b) (idIso d)

    associativity : (twice ∙ (aH ▷ i)) =₂ (ax ∙ composite)
    associativity = paste-squares e L ((s ∘ r) ◁ p) N (aH ▷ i) ai ax
      ((pentagon-whiskered i H r s) ⁻¹ ∙ isoComp-assoc-at (s ◁ b) d (aH ▷ i))
      ((postWhisker-comp-at p r s) ⁻¹) ∙
      isoComp-cong normalize (idIso (aH ▷ i))

    naturality : (output ∙ ((η ▷ H) ▷ i)) =₂ ((η ▷ x) ∙ composite)
    naturality = paste-squares e (comp-assoc i H t) ((s ∘ r) ◁ p) (t ◁ p)
      ((η ▷ H) ▷ i) (η ▷ (H ∘ i)) (η ▷ x)
      (preWhisker-comp-at η H i) ((interchange-at η p) ⁻¹)

    comparison : (output ∙ (diagram ▷ i)) =₂ (change ∙ twice)
    comparison = (isoComp-assoc-at (η ▷ x) (ax ⁻¹) twice) ⁻¹ ∙
      isoComp-cong (idIso (η ▷ x))
        ((move-square ax composite twice (aH ▷ i) (associativity ⁻¹)) ⁻¹) ∙
      isoComp-assoc-at (η ▷ x) composite ((aH ▷ i) ⁻¹) ∙
      isoComp-cong naturality (idIso ((aH ▷ i) ⁻¹)) ∙
      (isoComp-assoc-at output ((η ▷ H) ▷ i) ((aH ▷ i) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso output)
        (isoComp-cong (idIso ((η ▷ H) ▷ i)) (pre-inverse aH i) ∙
          preWhisker-isoComp-at (η ▷ H) (aH ⁻¹) i)
```
