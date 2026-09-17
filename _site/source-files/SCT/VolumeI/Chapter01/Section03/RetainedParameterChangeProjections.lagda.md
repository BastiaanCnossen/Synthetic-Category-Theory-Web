# Projections of retained parameter change

Both projection calculations concern the specified retained comparison.
They follow its two routes through their common pair and then cancel the
output route. The second calculation retains the original uncurrying
comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section03.ParameterChange as Change
import SCT.VolumeI.Chapter01.Section03.ParameterChangeNaturality as Naturality
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section03.RetainedParameterChangeProjections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M using (productMap-pair)
open Change 𝒯 M using (retained-parameter-change)
module Retained = Internal.RetainedEvaluation 𝒯 M
module Routes = Naturality.Routes 𝒯 M
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂; left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

abstract
  project-paste : {X Y Z : CAT} (π : MAP Y Z)
    {u v w : MAP X Y} {z : MAP X Z}
    (b : =₁ (π ∘ w) z) (β : =₁ v w) (α : =₁ u v)
    → =₂ (b ∙ (π ◁ (β ∙ α))) ((b ∙ (π ◁ β)) ∙ (π ◁ α))
  project-paste π b β α = invIso (isoComp-assoc-at b (π ◁ β) (π ◁ α)) ∙
    isoComp-cong (idIso b) (postWhisker-isoComp-at π β α)

  cancel-routes : {X Y Z : CAT} (π : MAP Y Z)
    {u v w : MAP X Y} {z : MAP X Z}
    (output : =₁ v w) (input : =₁ u w) (b : =₁ (π ∘ w) z)
    {out : =₁ (π ∘ v) z} {inn : =₁ (π ∘ u) z}
    → =₂ (b ∙ (π ◁ output)) out → =₂ (b ∙ (π ◁ input)) inn
    → =₂ (out ∙ (π ◁ (invIso output ∙ input))) inn
  cancel-routes π output input b outLaw inLaw = inLaw ∙
    (isoComp-cong (idIso b)
      ((postWhisker π ◁ cancel-inverse output input) ∙
        invIso (postWhisker-isoComp-at π output (invIso output ∙ input))) ∙
    (isoComp-assoc-at b (π ◁ output) (π ◁ (invIso output ∙ input)) ∙
      isoComp-cong (invIso outLaw) (idIso (π ◁ (invIso output ∙ input)))))

module ProjectionRoutes {P Q C D : CAT}
  (f : MAP P (Map C D)) (σ : MAP Q P) where

  open Routes {C = C} {D = D} σ

  RP = Retained.retained P f
  RQ = Retained.retained Q (f ∘ σ)
  u = mapUncurry f
  v = mapUncurry (f ∘ σ)
  κ = retained-parameter-change f σ
  βP₁ = pair-β₁ pr₁ u
  βP₂ = pair-β₂ pr₁ u
  βQ₁ = pair-β₁ pr₁ v
  βQ₂ = pair-β₂ pr₁ v
  bC = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
  bD = pair-β₁ (σ ∘ pr₁) (id D ∘ pr₂)
  dD = pair-β₂ (σ ∘ pr₁) (id D ∘ pr₂)
  qD = comp-unitˡ pr₂ ∙ dD
  A₁ = (σ ◁ βQ₁) ∙ comp-assoc RQ pr₁ σ
  A₂ = (id D ◁ βQ₂) ∙ comp-assoc RQ pr₂ (id D)
  t₁ = (bD ▷ RQ) ∙ invIso (comp-assoc RQ target-change pr₁)
  t₂ = (dD ▷ RQ) ∙ invIso (comp-assoc RQ target-change pr₂)

  base-output : =₁ (pr₁ ∘ (RP ∘ source-change)) (σ ∘ pr₁)
  base-output = bC ∙ ((βP₁ ▷ source-change) ∙ invIso (comp-assoc source-change RP pr₁))

  base-input : =₁ (pr₁ ∘ (target-change ∘ RQ)) (σ ∘ pr₁)
  base-input = (σ ◁ βQ₁) ∙ (comp-assoc RQ pr₁ σ ∙ t₁)

  evaluation-output : =₁ (pr₂ ∘ (RP ∘ source-change)) (u ∘ source-change)
  evaluation-output = (βP₂ ▷ source-change) ∙ invIso (comp-assoc source-change RP pr₂)

  evaluation-input : =₁ (pr₂ ∘ (target-change ∘ RQ)) v
  evaluation-input = βQ₂ ∙ ((qD ▷ RQ) ∙ invIso (comp-assoc RQ target-change pr₂))

  abstract
    output-base : =₂ (pair-β₁ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₁ ◁ output-route f)) base-output
    output-base = pair-pre-cong-triangle₁ pr₁ u source-change bC (idIso (u ∘ source-change))

    output-evaluation : =₂ (pair-β₂ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₂ ◁ output-route f)) evaluation-output
    output-evaluation = isoComp-unitˡ-at evaluation-output ∙
      pair-pre-cong-triangle₂ pr₁ u source-change bC (idIso (u ∘ source-change))

    input-base : =₂ (pair-β₁ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₁ ◁ input-route f)) base-input
    input-base = isoComp-assoc-at (σ ◁ βQ₁) (comp-assoc RQ pr₁ σ) t₁ ∙
      (pair-pre-cong-triangle₁ (σ ∘ pr₁) (id D ∘ pr₂) RQ A₁ A₂ ∙
      (isoComp-cong (isoComp-unitˡ-at (pair-β₁ (σ ∘ pr₁) (id D ∘ v)))
        (idIso (pr₁ ◁ productMap-pair σ (id D) pr₁ v)) ∙
      (isoComp-cong (pair-cong-triangle₁ (idIso (σ ∘ pr₁))
        (mapUncurry-pre f σ ∙ comp-unitˡ v)) (idIso (pr₁ ◁ productMap-pair σ (id D) pr₁ v)) ∙
        project-paste pr₁ (pair-β₁ (σ ∘ pr₁) (u ∘ source-change))
          (input-normalization f) (productMap-pair σ (id D) pr₁ v))))

    input-evaluation : =₂
      (pair-β₂ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₂ ◁ input-route f))
      (mapUncurry-pre f σ ∙ evaluation-input)
    input-evaluation =
      let unitV = comp-unitˡ v
          ν = mapUncurry-pre f σ
          A = comp-assoc RQ pr₂ (id D)
          λπ = comp-unitˡ pr₂ ▷ RQ
          tail = invIso (comp-assoc RQ target-change pr₂)
          unit = isoComp-cong (idIso βQ₂) (left-unitor-comp RQ pr₂) ∙
            (isoComp-assoc-at βQ₂ (comp-unitˡ (pr₂ ∘ RQ)) A ∙
            (isoComp-cong (postWhisker-id-at βQ₂) (idIso A) ∙
              invIso (isoComp-assoc-at unitV (id D ◁ βQ₂) A)))
          finish = isoComp-cong (idIso βQ₂)
              (isoComp-cong (invIso (preWhisker-isoComp-at (comp-unitˡ pr₂) dD RQ)) (idIso tail) ∙
                invIso (isoComp-assoc-at λπ (dD ▷ RQ) tail)) ∙
            isoComp-assoc-at βQ₂ λπ t₂
          normalize = isoComp-cong (idIso ν) (finish ∙ isoComp-cong unit (idIso t₂)) ∙
            (isoComp-cong (idIso ν) (invIso (isoComp-assoc-at unitV A₂ t₂)) ∙
              isoComp-assoc-at ν unitV (A₂ ∙ t₂))
          projected = isoComp-cong (idIso (ν ∙ unitV))
              (pair-pre-cong-triangle₂ (σ ∘ pr₁) (id D ∘ pr₂) RQ A₁ A₂) ∙
            (isoComp-assoc-at (ν ∙ unitV) (pair-β₂ (σ ∘ pr₁) (id D ∘ v))
              (pr₂ ◁ productMap-pair σ (id D) pr₁ v) ∙
            (isoComp-cong (pair-cong-triangle₂ (idIso (σ ∘ pr₁)) (ν ∙ unitV))
              (idIso (pr₂ ◁ productMap-pair σ (id D) pr₁ v)) ∙
              project-paste pr₂ (pair-β₂ (σ ∘ pr₁) (u ∘ source-change))
                (input-normalization f) (productMap-pair σ (id D) pr₁ v)))
      in normalize ∙ projected

    retained-change-base : =₂ (base-output ∙ (pr₁ ◁ κ)) base-input
    retained-change-base = cancel-routes pr₁ (output-route f) (input-route f)
      (pair-β₁ (σ ∘ pr₁) (u ∘ source-change)) output-base input-base

    retained-change-evaluation : =₂
      (evaluation-output ∙ (pr₂ ◁ κ)) (mapUncurry-pre f σ ∙ evaluation-input)
    retained-change-evaluation = cancel-routes pr₂ (output-route f) (input-route f)
      (pair-β₂ (σ ∘ pr₁) (u ∘ source-change)) output-evaluation input-evaluation
```
