# Substituting into postcomposition and uncurrying

The comparison uses the chosen substitution map on products. Its proof
combines iterated uncurrying with the evaluation calculation above.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup

module SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappingSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.Substitution.SubstitutionCoherence 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.EvaluationSubstitution 𝒯 using (module Evaluation)

mapPost-uncurry-restrict-proof : {X Y T C D : CAT} (f : MAP C D)
  (u : MAP X (Map T C)) (r : MAP Y X) →
  ((f ◁ mapUncurry-restrict u r) ∙
    (mapPost-uncurry f (u ∘ r) ∙ mapUncurryIso (comp-assoc r u (mapPost f)))) =₂
    (comp-assoc (productMap r (id T)) (mapUncurry u) f ∙
      ((mapPost-uncurry f u ▷ productMap r (id T)) ∙ mapUncurry-restrict (mapPost f ∘ u) r))
mapPost-uncurry-restrict-proof {X} {Y} {T} {C} {D} f u r =
  isoComp-cong (idIso targetAssoc)
    (isoComp-cong ((preWhisker R ◁ isoComp-assoc-at (comp-assoc S mapEval f) (mapPost-β f ▷ S) (mapUncurry-restrict F u)) ∙
      (preWhisker-isoComp-at (Eval.N S) (mapUncurry-restrict F u) R) ⁻¹) (idIso y) ∙
      (isoComp-assoc-at (Eval.N S ▷ R) x y) ⁻¹) ∙
  (isoComp-assoc-at targetAssoc (Eval.N S ▷ R) K ∙
  (isoComp-cong Eval.transport (idIso K) ∙
  ((isoComp-assoc-at action (Eval.N Q ∙ (Aκ ∙ assocA)) K) ⁻¹ ∙
  (isoComp-cong (idIso action)
    ((isoComp-assoc-at (Eval.N Q) (Aκ ∙ assocA) K) ⁻¹ ∙
      isoComp-cong (idIso (Eval.N Q)) ((isoComp-assoc-at Aκ assocA K) ⁻¹)) ∙
  (isoComp-cong (idIso action)
    (isoComp-cong (idIso (Eval.N Q)) iteration ∙
      (isoComp-assoc-at (Eval.N Q) (mapUncurry-restrict F (u ∘ r)) (mapUncurryIso (comp-assoc r u F)) ∙
        isoComp-cong ((isoComp-assoc-at (comp-assoc Q mapEval f) (mapPost-β f ▷ Q) (mapUncurry-restrict F (u ∘ r))) ⁻¹)
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
  action = f ◁ mapUncurry-restrict u r
  Aκ = mapUncurry F ◁ slice-comparison u r
  assocA = comp-assoc R S (mapUncurry F)
  targetAssoc = comp-assoc R (mapUncurry u) f
  x = mapUncurry-restrict F u ▷ R
  y = mapUncurry-restrict (F ∘ u) r
  K = x ∙ y
  iteration : (mapUncurry-restrict F (u ∘ r) ∙ mapUncurryIso (comp-assoc r u F)) =₂
    (Aκ ∙ (assocA ∙ K))
  iteration = mapUncurry-restrict-iterated F u r
  core : (action ∙ (Eval.N Q ∙ (Aκ ∙ assocA))) =₂
    (targetAssoc ∙ (Eval.N S ▷ R))
  core = Eval.transport

abstract
  mapPost-uncurry-restrict : {X Y T C D : CAT} (f : MAP C D)
    (u : MAP X (Map T C)) (r : MAP Y X) →
    ((f ◁ mapUncurry-restrict u r) ∙
      (mapPost-uncurry f (u ∘ r) ∙ mapUncurryIso (comp-assoc r u (mapPost f)))) =₂
      (comp-assoc (productMap r (id T)) (mapUncurry u) f ∙
        ((mapPost-uncurry f u ▷ productMap r (id T)) ∙ mapUncurry-restrict (mapPost f ∘ u) r))
  mapPost-uncurry-restrict = mapPost-uncurry-restrict-proof
```
