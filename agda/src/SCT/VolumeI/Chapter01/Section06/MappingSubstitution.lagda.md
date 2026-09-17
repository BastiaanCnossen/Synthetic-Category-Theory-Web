# Substituting into postcomposition and uncurrying

The comparison uses the chosen substitution map on products. Its proof
combines iterated uncurrying with the evaluation calculation above.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.MappingSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ

open import SCT.VolumeI.Chapter01.Section06.SubstitutionCoherence 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.EvaluationSubstitution 𝒯 using (module Evaluation)

funPost-uncurry-pre-proof : {X Y T C D : CAT} (f : MAP C D)
  (u : MAP X (Fun T C)) (r : MAP Y X) →
  =₂ ((f ◁ funUncurry-pre u r) ∙
    (funPost-uncurry f (u ∘ r) ∙ funUncurryIso (comp-assoc r u (funPost f))))
    (comp-assoc (productMap r (id T)) (funUncurry u) f ∙
      ((funPost-uncurry f u ▷ productMap r (id T)) ∙ funUncurry-pre (funPost f ∘ u) r))
funPost-uncurry-pre-proof {X} {Y} {T} {C} {D} f u r =
  isoComp-cong (idIso targetAssoc)
    (isoComp-cong ((preWhisker R ◁ isoComp-assoc-at (comp-assoc S funEval f) (funPost-β f ▷ S) (funUncurry-pre F u)) ∙
      invIso (preWhisker-isoComp-at (Eval.N S) (funUncurry-pre F u) R)) (idIso y) ∙
      invIso (isoComp-assoc-at (Eval.N S ▷ R) x y)) ∙
  (isoComp-assoc-at targetAssoc (Eval.N S ▷ R) K ∙
  (isoComp-cong Eval.transport (idIso K) ∙
  (invIso (isoComp-assoc-at action (Eval.N Q ∙ (Aκ ∙ assocA)) K) ∙
  (isoComp-cong (idIso action)
    (invIso (isoComp-assoc-at (Eval.N Q) (Aκ ∙ assocA) K) ∙
      isoComp-cong (idIso (Eval.N Q)) (invIso (isoComp-assoc-at Aκ assocA K))) ∙
  (isoComp-cong (idIso action)
    (isoComp-cong (idIso (Eval.N Q)) iteration ∙
      (isoComp-assoc-at (Eval.N Q) (funUncurry-pre F (u ∘ r)) (funUncurryIso (comp-assoc r u F)) ∙
        isoComp-cong (invIso (isoComp-assoc-at (comp-assoc Q funEval f) (funPost-β f ▷ Q) (funUncurry-pre F (u ∘ r))))
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
  action = f ◁ funUncurry-pre u r
  Aκ = funUncurry F ◁ slice-comparison u r
  assocA = comp-assoc R S (funUncurry F)
  targetAssoc = comp-assoc R (funUncurry u) f
  x = funUncurry-pre F u ▷ R
  y = funUncurry-pre (F ∘ u) r
  K = x ∙ y
  iteration : =₂ (funUncurry-pre F (u ∘ r) ∙ funUncurryIso (comp-assoc r u F))
    (Aκ ∙ (assocA ∙ K))
  iteration = funUncurry-pre-iterated F u r
  core : =₂ (action ∙ (Eval.N Q ∙ (Aκ ∙ assocA)))
    (targetAssoc ∙ (Eval.N S ▷ R))
  core = Eval.transport

abstract
  funPost-uncurry-pre : {X Y T C D : CAT} (f : MAP C D)
    (u : MAP X (Fun T C)) (r : MAP Y X) →
    =₂ ((f ◁ funUncurry-pre u r) ∙
      (funPost-uncurry f (u ∘ r) ∙ funUncurryIso (comp-assoc r u (funPost f))))
      (comp-assoc (productMap r (id T)) (funUncurry u) f ∙
        ((funPost-uncurry f u ▷ productMap r (id T)) ∙ funUncurry-pre (funPost f ∘ u) r))
  funPost-uncurry-pre = funPost-uncurry-pre-proof
```


