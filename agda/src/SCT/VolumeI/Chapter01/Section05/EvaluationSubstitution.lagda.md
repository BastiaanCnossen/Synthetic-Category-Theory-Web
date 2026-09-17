# Evaluation after a change of parameters

This finite calculation combines naturality of an evaluation comparison
with the pentagon. It is used to substitute into an uncurried cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IP
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.EvaluationSubstitution
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-at; preWhisker-comp-at)
open IP vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)

module Evaluation {X Y Z C D : CAT} (e : MAP Z C) (f : MAP C D)
  (A : MAP Z D) (β : NatIso A (f ∘ e)) (s : MAP Y Z) (t : MAP X Y)
  (q : MAP X Z) (κ : NatIso (s ∘ t) q) where

  N : {W : CAT} (z : MAP W Z) → NatIso (A ∘ z) (f ∘ (e ∘ z))
  N z = comp-assoc z e f ∙ (β ▷ z)

  natural : Iso₂ (N q ∙ (A ◁ κ)) ((f ◁ (e ◁ κ)) ∙ N (s ∘ t))
  natural = isoComp-assoc-at (f ◁ (e ◁ κ)) (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) ∙
    (isoComp-cong (postWhisker-comp-at κ e f) (idIso (β ▷ (s ∘ t))) ∙
    (invIso (isoComp-assoc-at (comp-assoc q e f) ((f ∘ e) ◁ κ) (β ▷ (s ∘ t))) ∙
    (isoComp-cong (idIso (comp-assoc q e f)) (interchange-at β κ) ∙
      isoComp-assoc-at (comp-assoc q e f) (β ▷ q) (A ◁ κ))))

  iterated : Iso₂ (N (s ∘ t) ∙ comp-assoc t s A)
    ((f ◁ comp-assoc t s e) ∙ (comp-assoc t (e ∘ s) f ∙ (N s ▷ t)))
  iterated = isoComp-cong (idIso (f ◁ comp-assoc t s e))
      (isoComp-cong (idIso (comp-assoc t (e ∘ s) f))
        (invIso (preWhisker-isoComp-at (comp-assoc s e f) (β ▷ s) t))) ∙
    (isoComp-assoc-at (f ◁ comp-assoc t s e) (comp-assoc t (e ∘ s) f)
      ((comp-assoc s e f ▷ t) ∙ ((β ▷ s) ▷ t)) ∙
    (isoComp-cong (idIso ((f ◁ comp-assoc t s e) ∙ comp-assoc t (e ∘ s) f))
      (idIso ((comp-assoc s e f ▷ t) ∙ ((β ▷ s) ▷ t))) ∙
    (isoComp-assoc-at ((f ◁ comp-assoc t s e) ∙ comp-assoc t (e ∘ s) f)
      (comp-assoc s e f ▷ t) ((β ▷ s) ▷ t) ∙
    (isoComp-cong (invIso (isoComp-assoc-at (f ◁ comp-assoc t s e)
        (comp-assoc t (e ∘ s) f) (comp-assoc s e f ▷ t)) ∙ pentagon-whiskered t s e f)
      (idIso ((β ▷ s) ▷ t)) ∙
    (invIso (isoComp-assoc-at (comp-assoc (s ∘ t) e f) (comp-assoc t s (f ∘ e)) ((β ▷ s) ▷ t)) ∙
    (isoComp-cong (idIso (comp-assoc (s ∘ t) e f)) (invIso (preWhisker-comp-at β s t)) ∙
      isoComp-assoc-at (comp-assoc (s ∘ t) e f) (β ▷ (s ∘ t)) (comp-assoc t s A)))))))

  V : NatIso (e ∘ q) ((e ∘ s) ∘ t)
  V = invIso (comp-assoc t s e) ∙ (e ◁ invIso κ)

  transport : Iso₂
    ((f ◁ V) ∙ (N q ∙ ((A ◁ κ) ∙ comp-assoc t s A)))
    (comp-assoc t (e ∘ s) f ∙ (N s ▷ t))
  transport = cancel-left fa result ∙
    (isoComp-cong (idIso (invIso fa)) (cancel-left fk (fa ∙ result)) ∙
    (isoComp-assoc-at (invIso fa) (invIso fk) (fk ∙ (fa ∙ result)) ∙
    (isoComp-cong inverseV expanded)))
    where
    fa = f ◁ comp-assoc t s e
    fk = f ◁ (e ◁ κ)
    result = comp-assoc t (e ∘ s) f ∙ (N s ▷ t)
    inverseV = isoComp-cong (post-inverse f (comp-assoc t s e))
      (post-inverse f (e ◁ κ) ∙ (postWhisker f ◁ post-inverse e κ)) ∙ postWhisker-isoComp-at f (invIso (comp-assoc t s e)) (e ◁ invIso κ)
    expanded = isoComp-cong (idIso fk) iterated ∙
      (isoComp-assoc-at fk (N (s ∘ t)) (comp-assoc t s A) ∙
      (isoComp-cong natural (idIso (comp-assoc t s A)) ∙
        invIso (isoComp-assoc-at (N q) (A ◁ κ) (comp-assoc t s A))))
```
