# Evaluation after the Beck–Chevalley family comparison

Postcompose the geometric comparison with the original evaluation.
Projection removes the final target pullback, and the two opposite
source associators cancel. The result compares the two uncurried
families over the original base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyDomain 𝒯 M ℱ P using (module Domain)
open import SCT.VolumeI.Chapter03.Section05.Currying.ProjectedRelativeEvaluation 𝒯 M ℱ P using (module Evaluation)
import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyFamilies as Geometry

module Pulled {S T S′ T′ C D : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (g : MAP D T) (f : MAP C S)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) where
  module Dom = Domain p b square g
  module Eval = Evaluation Dom.h f ε Dom.into-over
  pulled = Eval.pulled

  module At {K X : CAT} (k : MAP K T′) (u : FunctorOver (k ∘ pr₂ {C = X}) Dom.t) where
    module Geometric = Geometry.Family 𝒯 M ℱ P p b square square-isPullback g k u
    open Geometric using (J; argument)
    module Target = Families Dom.h f Geometric.Parameters.rN
    old-evaluated = compose-over ε Geometric.Old.pulled
    common = compose-over old-evaluated argument

    abstract
      comparison : FunctorOverIso
        (Target.forward (compose-over pulled Geometric.New.pulled)) common
      comparison = compose-iso-over
        (inverse-iso-over (associator-over argument Geometric.Old.pulled ε))
        (compose-iso-over (source-change-inverse J (compose-over ε (compose-over Geometric.Old.pulled argument)))
          (change-source-iso (J ⁻¹)
            (compose-iso-over (compose-source-change J (compose-over Geometric.Old.pulled argument) ε)
              (compose-iso-over (postwhisker-over ε (inverse-iso-over Geometric.comparison))
                (Eval.comparison Geometric.New.pulled)))))
```
