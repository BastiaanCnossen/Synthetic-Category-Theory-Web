# Projections of retained parameter change

Both projection calculations concern the specified retained comparison.
They follow its two routes through their common pair and then cancel the
output route. The second calculation retains the original uncurrying
comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as Change
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChangeNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.RetainedParameterChangeProjections
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
    (b : (π ∘ w) =₁ z) (β : v =₁ w) (α : u =₁ v)
    → (b ∙ (π ◁ (β ∙ α))) =₂ ((b ∙ (π ◁ β)) ∙ (π ◁ α))
  project-paste π b β α = (isoComp-assoc-at b (π ◁ β) (π ◁ α)) ⁻¹ ∙
    isoComp-cong (idIso b) (postWhisker-isoComp-at π β α)

  cancel-routes : {X Y Z : CAT} (π : MAP Y Z)
    {u v w : MAP X Y} {z : MAP X Z}
    (output : v =₁ w) (input : u =₁ w) (b : (π ∘ w) =₁ z)
    {out : (π ∘ v) =₁ z} {inn : (π ∘ u) =₁ z}
    → (b ∙ (π ◁ output)) =₂ out → (b ∙ (π ◁ input)) =₂ inn
    → (out ∙ (π ◁ (output ⁻¹ ∙ input))) =₂ inn
  cancel-routes π output input b outLaw inLaw = inLaw ∙
    (isoComp-cong (idIso b)
      ((postWhisker π ◁ cancel-inverse output input) ∙
        (postWhisker-isoComp-at π output (output ⁻¹ ∙ input)) ⁻¹) ∙
    (isoComp-assoc-at b (π ◁ output) (π ◁ (output ⁻¹ ∙ input)) ∙
      isoComp-cong (outLaw ⁻¹) (idIso (π ◁ (output ⁻¹ ∙ input)))))

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
  t₁ = (bD ▷ RQ) ∙ (comp-assoc RQ target-change pr₁) ⁻¹
  t₂ = (dD ▷ RQ) ∙ (comp-assoc RQ target-change pr₂) ⁻¹

  base-output : (pr₁ ∘ (RP ∘ source-change)) =₁ (σ ∘ pr₁)
  base-output = bC ∙ ((βP₁ ▷ source-change) ∙ (comp-assoc source-change RP pr₁) ⁻¹)

  base-input : (pr₁ ∘ (target-change ∘ RQ)) =₁ (σ ∘ pr₁)
  base-input = (σ ◁ βQ₁) ∙ (comp-assoc RQ pr₁ σ ∙ t₁)

  evaluation-output : (pr₂ ∘ (RP ∘ source-change)) =₁ (u ∘ source-change)
  evaluation-output = (βP₂ ▷ source-change) ∙ (comp-assoc source-change RP pr₂) ⁻¹

  evaluation-input : (pr₂ ∘ (target-change ∘ RQ)) =₁ v
  evaluation-input = βQ₂ ∙ ((qD ▷ RQ) ∙ (comp-assoc RQ target-change pr₂) ⁻¹)

  abstract
    output-base : (pair-β₁ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₁ ◁ output-route f)) =₂ base-output
    output-base = pair-pre-cong-triangle₁ pr₁ u source-change bC (idIso (u ∘ source-change))

    output-evaluation : (pair-β₂ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₂ ◁ output-route f)) =₂ evaluation-output
    output-evaluation = isoComp-unitˡ-at evaluation-output ∙
      pair-pre-cong-triangle₂ pr₁ u source-change bC (idIso (u ∘ source-change))

    input-base : (pair-β₁ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₁ ◁ input-route f)) =₂ base-input
    input-base = isoComp-assoc-at (σ ◁ βQ₁) (comp-assoc RQ pr₁ σ) t₁ ∙
      (pair-pre-cong-triangle₁ (σ ∘ pr₁) (id D ∘ pr₂) RQ A₁ A₂ ∙
      (isoComp-cong (isoComp-unitˡ-at (pair-β₁ (σ ∘ pr₁) (id D ∘ v)))
        (idIso (pr₁ ◁ productMap-pair σ (id D) pr₁ v)) ∙
      (isoComp-cong (pair-cong-triangle₁ (idIso (σ ∘ pr₁))
        (mapUncurry-restrict f σ ∙ comp-unitˡ v)) (idIso (pr₁ ◁ productMap-pair σ (id D) pr₁ v)) ∙
        project-paste pr₁ (pair-β₁ (σ ∘ pr₁) (u ∘ source-change))
          (input-normalization f) (productMap-pair σ (id D) pr₁ v))))

    input-evaluation :
      (pair-β₂ (σ ∘ pr₁) (u ∘ source-change) ∙ (pr₂ ◁ input-route f)) =₂
      (mapUncurry-restrict f σ ∙ evaluation-input)
    input-evaluation =
      let unitV = comp-unitˡ v
          ν = mapUncurry-restrict f σ
          A = comp-assoc RQ pr₂ (id D)
          λπ = comp-unitˡ pr₂ ▷ RQ
          tail = (comp-assoc RQ target-change pr₂) ⁻¹
          unit = isoComp-cong (idIso βQ₂) (left-unitor-comp RQ pr₂) ∙
            (isoComp-assoc-at βQ₂ (comp-unitˡ (pr₂ ∘ RQ)) A ∙
            (isoComp-cong (postWhisker-id-at βQ₂) (idIso A) ∙
              (isoComp-assoc-at unitV (id D ◁ βQ₂) A) ⁻¹))
          finish = isoComp-cong (idIso βQ₂)
              (isoComp-cong ((preWhisker-isoComp-at (comp-unitˡ pr₂) dD RQ) ⁻¹) (idIso tail) ∙
                (isoComp-assoc-at λπ (dD ▷ RQ) tail) ⁻¹) ∙
            isoComp-assoc-at βQ₂ λπ t₂
          normalize = isoComp-cong (idIso ν) (finish ∙ isoComp-cong unit (idIso t₂)) ∙
            (isoComp-cong (idIso ν) ((isoComp-assoc-at unitV A₂ t₂) ⁻¹) ∙
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

    retained-change-base : (base-output ∙ (pr₁ ◁ κ)) =₂ base-input
    retained-change-base = cancel-routes pr₁ (output-route f) (input-route f)
      (pair-β₁ (σ ∘ pr₁) (u ∘ source-change)) output-base input-base

    retained-change-evaluation :
      (evaluation-output ∙ (pr₂ ◁ κ)) =₂ (mapUncurry-restrict f σ ∙ evaluation-input)
    retained-change-evaluation = cancel-routes pr₂ (output-route f) (input-route f)
      (pair-β₂ (σ ∘ pr₁) (u ∘ source-change)) output-evaluation input-evaluation
```
