# Evaluating comparisons of relative cones

Forgetting a relative cone is an actual map of cospans. Its normalized
matching is precisely the matching used in relative pullback evaluation.
Consequently both restriction and comparisons of whole cones survive
forgetting and uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Action
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanRestriction as Restriction

module Evaluation {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  module U = Postcompose k u using (functor)
  module V = Postcompose k v using (functor)
  forget : CospanMap U.functor V.functor (funPost (FunctorLift.lift u)) (funPost (FunctorLift.lift v))
  forget = record
    { left = Over.forget k f ; right = Over.forget k g ; base = Over.forget k h
    ; leftSquare = Cone.match (Postcomposition.square k u)
    ; rightSquare = Cone.match (Postcomposition.square k v) }
  module Forget = Action.Action 𝒯 P forget using (normalized; module Normalization; module Identification)
  ordinary = Forget.normalized
  value : {X : CAT} → Cone U.functor V.functor X → Cone (FunctorLift.lift u) (FunctorLift.lift v) (X × K)
  value s = uncurryCone (ordinary s)
  abstract
    comparison : {X : CAT} {s t : Cone U.functor V.functor X} → ConeIso s t → ConeIso (value s) (value t)
    comparison Φ = uncurryConeIso (Forget.Identification.normalized-comparison Φ)
    restrict-ordinary : {X Y : CAT} (r : MAP Y X) (s : Cone U.functor V.functor X) →
      ConeIso (conePre r (ordinary s)) (ordinary (conePre r s))
    restrict-ordinary r s = coneIso-compose (coneIso-inverse (Forget.Normalization.comparison (conePre r s)))
      (coneIso-compose (Restriction.Restriction.comparison 𝒯 P forget r s)
        (coneIso-pre r (Forget.Normalization.comparison s)))
```
