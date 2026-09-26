# Projecting a pulled evaluation functor

Projecting evaluation after base change removes its final pullback lift.
The resulting relative functor first enters the old evaluation domain
and then applies evaluation. All three triangles remain part of the
comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.ProjectedRelativeEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target; forward-composite)

module Evaluation {C D E S S′ : CAT} (h : MAP S′ S) (f : MAP C S) {g : MAP D S}
  {r : MAP E S′} (ε : FunctorOver g f) (into : FunctorOver (h ∘ r) g) where
  pulled : FunctorOver r (pullback₂ {f = f} {h})
  pulled = Target.backward h f r (compose-over ε into)

  abstract
    comparison : {X : CAT} {t : MAP X S′} (u : FunctorOver t r) → FunctorOverIso
      (Target.forward h f t (compose-over pulled u)) (compose-over ε (compose-over into (postbase h u)))
    comparison u = compose-iso-over (associator-over (postbase h u) into ε)
      (compose-iso-over (prewhisker-over (postbase h u) (Target.forward-backward h f _ (compose-over ε into)))
        (forward-composite h f pulled u))
```
