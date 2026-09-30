# Computing the chosen base-change identification

The base-change action was lifted on the whole anima of relative
identifications. Restrict its full cone computation to a specified
identification, then use the computation for its encoding. This gives
both projection images and their compatibility with the specified
matching, rather than only the triangle over the new base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeComparisonComputation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport 𝒯 P using (module Transport)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints-at)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeComparisonFamilies 𝒯 M ℱ P using (module Change)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Action
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanRestriction as Restriction
import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications as NativeBaseChange

module Computation {C D S T : CAT} (p : MAP S T)
  {f : MAP C T} {g : MAP D T} (u v : FunctorOver f g) where
  module Changed = Change p u v
    using (first; second; hu; hv; source; restricted; transported; functor;
      cone-computation; comparison; module Encoded; module Restricted; module Target)
  module Input = Changed.Encoded
  module Native = NativeBaseChange.Change 𝒯 M ℱ P p using (module Identification)
  module Endpoints = Transport (coneIso-inverse (pullbackLift-β Changed.first))
    (coneIso-inverse (pullbackLift-β Changed.second)) using (cospan; mapCone; module Right)
  module Output = Encoding
    (conePre Changed.hu (pullbackCone g p))
    (conePre Changed.hv (pullbackCone g p))
  module RestrictInput = Action.Action 𝒯 P Changed.Restricted.cospan using (module Identification)
  module TransportInput = Action.Action 𝒯 P Endpoints.cospan using (module Identification)

  prescribed : FunctorOverIso u v → Cone Output.leftMap Output.rightMap One
  prescribed Φ = Endpoints.mapCone
    (CospanMap.mapCone Changed.Restricted.cospan (Input.encode Φ))

  opaque
    restricted-computation : (Φ : FunctorOverIso u v) →
      ConeIso (conePre (Input.point Φ) Changed.restricted)
        (CospanMap.mapCone Changed.Restricted.cospan (Input.encode Φ))
    restricted-computation Φ = coneIso-compose
      (RestrictInput.Identification.comparison (pullbackLift-β (Input.encode Φ)))
      (Restriction.Restriction.comparison 𝒯 P Changed.Restricted.cospan
        (Input.point Φ) Changed.source)

  opaque
    transported-computation : (Φ : FunctorOverIso u v) →
      ConeIso (conePre (Input.point Φ) Changed.transported) (prescribed Φ)
    transported-computation Φ = coneIso-compose
      (TransportInput.Identification.comparison (restricted-computation Φ))
      (Restriction.Restriction.comparison 𝒯 P Endpoints.cospan
        (Input.point Φ) Changed.restricted)

  opaque
    cone-computation : (Φ : FunctorOverIso u v) →
      ConeIso
        (conePre (FunctorOverIso.underlying (Changed.comparison Φ)) Changed.Target.comparisonCone)
        (prescribed Φ)
    cone-computation Φ = coneIso-compose (transported-computation Φ)
      (coneIso-compose (coneIso-pre (Input.point Φ) Changed.cone-computation)
        (coneIso-inverse (conePre-assoc (Input.point Φ) Changed.functor Changed.Target.comparisonCone)))

  opaque
    comparison-computation : (Φ : FunctorOverIso u v) →
      ConeIso₂
        (Output.decode
          (conePre (FunctorOverIso.underlying (Changed.comparison Φ)) Changed.Target.comparisonCone))
        (Output.decode (prescribed Φ))
    comparison-computation Φ = Output.decode-comparison (cone-computation Φ)

  opaque
    unfolding Native.Identification.comparison
    native-cone-computation : (Φ : FunctorOverIso u v) →
      ConeIso
        (conePre (FunctorOverIso.underlying (Native.Identification.comparison Φ))
          Changed.Target.comparisonCone)
        (prescribed Φ)
    native-cone-computation Φ = cone-computation Φ

  first-β = pullbackLift-β₁ Changed.first
  second-β = pullbackLift-β₁ Changed.second
  first-base-β = pullbackLift-β₂ Changed.first
  second-base-β = pullbackLift-β₂ Changed.second

  opaque
    left-image : (Φ : FunctorOverIso u v) →
      (pullback₁ {f = g} {p} ◁ FunctorOverIso.underlying (Changed.comparison Φ)) =₂
      (second-β ⁻¹ ∙ ((FunctorOverIso.underlying Φ ▷ pullback₁ {f = f} {p}) ∙ first-β))
    left-image Φ = isoComp-cong (idIso (second-β ⁻¹))
      (isoComp-cong (idIso (FunctorOverIso.underlying Φ ▷ pullback₁ {f = f} {p}))
        (inverse-inverse first-β)) ∙
      (changeEndpoints-at (first-β ⁻¹) (second-β ⁻¹)
        (FunctorOverIso.underlying Φ ▷ pullback₁ {f = f} {p}) ∙
        ConeIso.leftIso (cone-computation Φ))

    right-image : (Φ : FunctorOverIso u v) →
      (pullback₂ {f = g} {p} ◁ FunctorOverIso.underlying (Changed.comparison Φ)) =₂
      (second-base-β ⁻¹ ∙ first-base-β)
    right-image Φ = isoComp-cong (idIso (second-base-β ⁻¹))
      (inverse-inverse first-base-β ∙ isoComp-unitˡ-at ((first-base-β ⁻¹) ⁻¹)) ∙
      (changeEndpoints-at (first-base-β ⁻¹) (second-base-β ⁻¹)
        (idIso (pullback₂ {f = f} {p})) ∙
      ((Endpoints.Right.forward ◁ const-evaluate (idIso (pullback₂ {f = f} {p})) (id One)) ∙
        ConeIso.rightIso (cone-computation Φ)))
```
