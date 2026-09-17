# Substituting into postcomposition and uncurrying

The comparison uses the chosen substitution map on products. Its proof
combines iterated uncurrying with the evaluation calculation above.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.MappingSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section03.SubstitutionCoherence 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.EvaluationSubstitution 𝒯 using (module Evaluation)

mapPost-uncurry-pre-proof : {X Y T C D : CAT} (f : MAP C D)
  (u : MAP X (Map T C)) (r : MAP Y X) →
  Iso₂ ((f ◁ mapUncurry-pre u r) ∙
    (mapPost-uncurry f (u ∘ r) ∙ mapUncurryIso (comp-assoc r u (mapPost f))))
    (comp-assoc (productMap r (id T)) (mapUncurry u) f ∙
      ((mapPost-uncurry f u ▷ productMap r (id T)) ∙ mapUncurry-pre (mapPost f ∘ u) r))
mapPost-uncurry-pre-proof {X} {Y} {T} {C} {D} f u r =
  isoComp-cong (idIso targetAssoc)
    (isoComp-cong ((preWhisker R ◁ isoComp-assoc-at (comp-assoc S mapEval f) (mapPost-β f ▷ S) (mapUncurry-pre F u)) ∙
      invIso (preWhisker-isoComp-at (Eval.N S) (mapUncurry-pre F u) R)) (idIso y) ∙
      invIso (isoComp-assoc-at (Eval.N S ▷ R) x y)) ∙
  (isoComp-assoc-at targetAssoc (Eval.N S ▷ R) K ∙
  (isoComp-cong Eval.transport (idIso K) ∙
  (invIso (isoComp-assoc-at action (Eval.N Q ∙ (Aκ ∙ assocA)) K) ∙
  (isoComp-cong (idIso action)
    (invIso (isoComp-assoc-at (Eval.N Q) (Aκ ∙ assocA) K) ∙
      isoComp-cong (idIso (Eval.N Q)) (invIso (isoComp-assoc-at Aκ assocA K))) ∙
  (isoComp-cong (idIso action)
    (isoComp-cong (idIso (Eval.N Q)) iteration ∙
      (isoComp-assoc-at (Eval.N Q) (mapUncurry-pre F (u ∘ r)) (mapUncurryIso (comp-assoc r u F)) ∙
        isoComp-cong (invIso (isoComp-assoc-at (comp-assoc Q mapEval f) (mapPost-β f ▷ Q) (mapUncurry-pre F (u ∘ r))))
          (idIso (mapUncurryIso (comp-assoc r u F))))))))))
  where
  F : MAP (Map T C) (Map T D)
  F = mapPost f
  S : MAP (X × T) (Map T C × T)
  S = productMap u (id T)
  R : MAP (Y × T) (X × T)
  R = productMap r (id T)
  Q : MAP (Y × T) (Map T C × T)
  Q = productMap (u ∘ r) (id T)
  module Eval = Evaluation (mapEval {T} {C}) f (mapUncurry F) (mapPost-β f) S R Q (slice-comparison u r)
  action = f ◁ mapUncurry-pre u r
  Aκ = mapUncurry F ◁ slice-comparison u r
  assocA = comp-assoc R S (mapUncurry F)
  targetAssoc = comp-assoc R (mapUncurry u) f
  x = mapUncurry-pre F u ▷ R
  y = mapUncurry-pre (F ∘ u) r
  K = x ∙ y
  iteration : Iso₂ (mapUncurry-pre F (u ∘ r) ∙ mapUncurryIso (comp-assoc r u F))
    (Aκ ∙ (assocA ∙ K))
  iteration = mapUncurry-pre-iterated F u r
  core : Iso₂ (action ∙ (Eval.N Q ∙ (Aκ ∙ assocA)))
    (targetAssoc ∙ (Eval.N S ▷ R))
  core = Eval.transport

abstract
  mapPost-uncurry-pre : {X Y T C D : CAT} (f : MAP C D)
    (u : MAP X (Map T C)) (r : MAP Y X) →
    Iso₂ ((f ◁ mapUncurry-pre u r) ∙
      (mapPost-uncurry f (u ∘ r) ∙ mapUncurryIso (comp-assoc r u (mapPost f))))
      (comp-assoc (productMap r (id T)) (mapUncurry u) f ∙
        ((mapPost-uncurry f u ▷ productMap r (id T)) ∙ mapUncurry-pre (mapPost f ∘ u) r))
  mapPost-uncurry-pre = mapPost-uncurry-pre-proof
```
