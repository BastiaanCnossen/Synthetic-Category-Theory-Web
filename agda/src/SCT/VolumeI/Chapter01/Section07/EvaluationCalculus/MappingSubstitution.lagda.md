# Substituting into postcomposition and uncurrying

The comparison uses the chosen substitution map on products. Its proof
combines iterated uncurrying with the evaluation calculation above.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.SubstitutionCoherence 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.EvaluationSubstitution 𝒯 using (module Evaluation)

funPost-uncurry-restrict-proof : {X Y T C D : CAT} (f : MAP C D)
  (u : MAP X (Fun T C)) (r : MAP Y X) →
  ((f ◁ funUncurry-restrict u r) ∙
    (funPost-uncurry f (u ∘ r) ∙ funUncurryIso (comp-assoc r u (funPost f)))) =₂
    (comp-assoc (productMap r (id T)) (funUncurry u) f ∙
      ((funPost-uncurry f u ▷ productMap r (id T)) ∙ funUncurry-restrict (funPost f ∘ u) r))
funPost-uncurry-restrict-proof {X} {Y} {T} {C} {D} f u r =
  isoComp-cong (idIso targetAssoc)
    (isoComp-cong ((preWhisker R ◁ isoComp-assoc-at (comp-assoc S funEval f) (funPost-β f ▷ S) (funUncurry-restrict F u)) ∙
      (preWhisker-isoComp-at (Eval.N S) (funUncurry-restrict F u) R) ⁻¹) (idIso y) ∙
      (isoComp-assoc-at (Eval.N S ▷ R) x y) ⁻¹) ∙
  (isoComp-assoc-at targetAssoc (Eval.N S ▷ R) K ∙
  (isoComp-cong Eval.transport (idIso K) ∙
  ((isoComp-assoc-at action (Eval.N Q ∙ (Aκ ∙ assocA)) K) ⁻¹ ∙
  (isoComp-cong (idIso action)
    ((isoComp-assoc-at (Eval.N Q) (Aκ ∙ assocA) K) ⁻¹ ∙
      isoComp-cong (idIso (Eval.N Q)) ((isoComp-assoc-at Aκ assocA K) ⁻¹)) ∙
  (isoComp-cong (idIso action)
    (isoComp-cong (idIso (Eval.N Q)) iteration ∙
      (isoComp-assoc-at (Eval.N Q) (funUncurry-restrict F (u ∘ r)) (funUncurryIso (comp-assoc r u F)) ∙
        isoComp-cong ((isoComp-assoc-at (comp-assoc Q funEval f) (funPost-β f ▷ Q) (funUncurry-restrict F (u ∘ r))) ⁻¹)
          (idIso (funUncurryIso (comp-assoc r u F))))))))))
  where
  F : MAP (Fun T C) (Fun T D)
  F = funPost f
  S : MAP (X × T) (Fun T C × T)
  S = productMap u (id T)
  R : MAP (Y × T) (X × T)
  R = productMap r (id T)
  Q : MAP (Y × T) (Fun T C × T)
  Q = productMap (u ∘ r) (id T)
  module Eval = Evaluation (funEval {T} {C}) f (funUncurry F) (funPost-β f) S R Q (slice-comparison u r)
  action = f ◁ funUncurry-restrict u r
  Aκ = funUncurry F ◁ slice-comparison u r
  assocA = comp-assoc R S (funUncurry F)
  targetAssoc = comp-assoc R (funUncurry u) f
  x = funUncurry-restrict F u ▷ R
  y = funUncurry-restrict (F ∘ u) r
  K = x ∙ y
  iteration : (funUncurry-restrict F (u ∘ r) ∙ funUncurryIso (comp-assoc r u F)) =₂
    (Aκ ∙ (assocA ∙ K))
  iteration = funUncurry-restrict-iterated F u r
  core : (action ∙ (Eval.N Q ∙ (Aκ ∙ assocA))) =₂
    (targetAssoc ∙ (Eval.N S ▷ R))
  core = Eval.transport

abstract
  funPost-uncurry-restrict : {X Y T C D : CAT} (f : MAP C D)
    (u : MAP X (Fun T C)) (r : MAP Y X) →
    ((f ◁ funUncurry-restrict u r) ∙
      (funPost-uncurry f (u ∘ r) ∙ funUncurryIso (comp-assoc r u (funPost f)))) =₂
      (comp-assoc (productMap r (id T)) (funUncurry u) f ∙
        ((funPost-uncurry f u ▷ productMap r (id T)) ∙ funUncurry-restrict (funPost f ∘ u) r))
  funPost-uncurry-restrict = funPost-uncurry-restrict-proof
```


