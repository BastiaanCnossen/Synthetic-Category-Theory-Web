# Evaluation after a change of parameters

This finite calculation combines naturality of an evaluation comparison
with the pentagon. It is used to substitute into an uncurried cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IP
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.EvaluationSubstitution
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-at; preWhisker-comp-at)
open IP vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)

module Evaluation {X Y Z C D : CAT} (e : MAP Z C) (f : MAP C D)
  (A : MAP Z D) (β : A =₁ (f ∘ e)) (s : MAP Y Z) (t : MAP X Y)
  (q : MAP X Z) (κ : (s ∘ t) =₁ q) where

  N : {W : CAT} (z : MAP W Z) → (A ∘ z) =₁ (f ∘ (e ∘ z))
  N z = comp-assoc z e f ∙ (β ▷ z)

  natural : (N q ∙ (A ◁ κ)) =₂ ((f ◁ (e ◁ κ)) ∙ N (s ∘ t))
  natural = isoComp-assoc-at (f ◁ (e ◁ κ)) (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) ∙
    (isoComp-cong (postWhisker-comp-at κ e f) (idIso (β ▷ (s ∘ t))) ∙
    ((isoComp-assoc-at (comp-assoc q e f) ((f ∘ e) ◁ κ) (β ▷ (s ∘ t))) ⁻¹ ∙
    (isoComp-cong (idIso (comp-assoc q e f)) (interchange-at β κ) ∙
      isoComp-assoc-at (comp-assoc q e f) (β ▷ q) (A ◁ κ))))

  iterated : (N (s ∘ t) ∙ comp-assoc t s A) =₂
    ((f ◁ comp-assoc t s e) ∙ (comp-assoc t (e ∘ s) f ∙ (N s ▷ t)))
  iterated = isoComp-cong (idIso (f ◁ comp-assoc t s e))
      (isoComp-cong (idIso (comp-assoc t (e ∘ s) f))
        ((preWhisker-isoComp-at (comp-assoc s e f) (β ▷ s) t) ⁻¹)) ∙
    (isoComp-assoc-at (f ◁ comp-assoc t s e) (comp-assoc t (e ∘ s) f)
      ((comp-assoc s e f ▷ t) ∙ ((β ▷ s) ▷ t)) ∙
    (isoComp-cong (idIso ((f ◁ comp-assoc t s e) ∙ comp-assoc t (e ∘ s) f))
      (idIso ((comp-assoc s e f ▷ t) ∙ ((β ▷ s) ▷ t))) ∙
    (isoComp-assoc-at ((f ◁ comp-assoc t s e) ∙ comp-assoc t (e ∘ s) f)
      (comp-assoc s e f ▷ t) ((β ▷ s) ▷ t) ∙
    (isoComp-cong ((isoComp-assoc-at (f ◁ comp-assoc t s e)
        (comp-assoc t (e ∘ s) f) (comp-assoc s e f ▷ t)) ⁻¹ ∙ pentagon-whiskered t s e f)
      (idIso ((β ▷ s) ▷ t)) ∙
    ((isoComp-assoc-at (comp-assoc (s ∘ t) e f) (comp-assoc t s (f ∘ e)) ((β ▷ s) ▷ t)) ⁻¹ ∙
    (isoComp-cong (idIso (comp-assoc (s ∘ t) e f)) ((preWhisker-comp-at β s t) ⁻¹) ∙
      isoComp-assoc-at (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) (comp-assoc t s A)))))))

  V : (e ∘ q) =₁ ((e ∘ s) ∘ t)
  V = (comp-assoc t s e) ⁻¹ ∙ (e ◁ κ ⁻¹)

  transport :
    ((f ◁ V) ∙ (N q ∙ ((A ◁ κ) ∙ comp-assoc t s A))) =₂
    (comp-assoc t (e ∘ s) f ∙ (N s ▷ t))
  transport = cancel-left fa result ∙
    (isoComp-cong (idIso (fa ⁻¹)) (cancel-left fk (fa ∙ result)) ∙
    (isoComp-assoc-at (fa ⁻¹) (fk ⁻¹) (fk ∙ (fa ∙ result)) ∙
    (isoComp-cong inverseV expanded)))
    where
    fa = f ◁ comp-assoc t s e
    fk = f ◁ (e ◁ κ)
    result = comp-assoc t (e ∘ s) f ∙ (N s ▷ t)
    inverseV = isoComp-cong (post-inverse f (comp-assoc t s e))
      (post-inverse f (e ◁ κ) ∙ (postWhisker f ◁ post-inverse e κ)) ∙ postWhisker-isoComp-at f ((comp-assoc t s e) ⁻¹) (e ◁ κ ⁻¹)
    expanded = isoComp-cong (idIso fk) iterated ∙
      (isoComp-assoc-at fk (N (s ∘ t)) (comp-assoc t s A) ∙
      (isoComp-cong natural (idIso (comp-assoc t s A)) ∙
        (isoComp-assoc-at (N q) (A ◁ κ) (comp-assoc t s A)) ⁻¹))
```
