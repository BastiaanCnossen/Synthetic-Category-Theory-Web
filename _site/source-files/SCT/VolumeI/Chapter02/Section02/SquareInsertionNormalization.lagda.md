# Normalizing the parameter side of an insertion corner

After lifting the first projection of an insertion square through another
functor, the incoming frame agrees with first evaluating that functor and
then restricting its endpoint frame. The triangle law removes the unit,
and projection composition accounts for the associators.

This calculation applies to both the parameter and the outer coordinate
of the square-currying permutation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareInsertionNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ
import SCT.VolumeI.Chapter02.Section02.InsertionProjectionWitnesses as Insertion
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projections
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (change-middle; lift-assoc)
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; right-unitor-comp; preWhisker-id-reflect)
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionCalculus 𝒯 using (section-pre; section-image; section-comp)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; cancel-left-reflect)
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductUnits
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at; whisker-mixed-at)
open import SCT.VolumeI.Chapter01.Section04.ProductPairingComparisons 𝒯 M using (identity-coordinate)
open import SCT.VolumeI.Chapter01.Section04.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
module PS = Projections 𝒯

abstract
  unitors-on-identity : (X : CAT) → comp-unitʳ (id X) =₂ comp-unitˡ (id X)
  unitors-on-identity X = preWhisker-id-reflect
    (left-unitor-comp (id X) (id X) ∙
      isoComp-cong (cancel-left-reflect (comp-unitˡ (id X)) (postWhisker-id-at (comp-unitˡ (id X))))
        (idIso (comp-assoc (id X) (id X) (id X))) ∙
      triangle-whiskered (id X) (id X))

  identity-section : {X K : CAT} (π : MAP K X) (i : MAP X K) (b : (π ∘ i) =₁ id X) →
    section-image π i b (id X) =₂ (b ∙ (comp-unitˡ π ▷ i))
  identity-section {X} π i b = identity-coordinate π i b ∙
    isoComp-cong (unitors-on-identity X) (idIso (PS.lift-base (id X) π i b))

module Incoming {Γ X A D : CAT} (r : MAP Γ X) (u : Obj-abs A)
  (p : MAP X D) {z : MAP Γ D} (b : (p ∘ r) =₁ z) where
  module Insert = Insertion.Parameter 𝒯 M ℱ r u
  i = insert {X = X} u
  β = pair-β₁ (id X) (const u)
  lifted = PS.lift-base p pr₁ i β
  step = comp-unitʳ p ∙ lifted
  raw = b ∙ PS.lift-base p pr₁ (i ∘ r) Insert.incoming₁
  normalized = PS.compose-base (p ∘ pr₁) i step r b
  tail = (step ▷ r) ∙ (comp-assoc r i (p ∘ pr₁)) ⁻¹

  abstract
    comparison : raw =₂ normalized
    comparison = isoComp-cong (idIso b)
      (isoComp-unitˡ-at tail ∙ (section-pre pr₁ i β r p) ⁻¹)

module Outgoing {Γ X A D : CAT} (r : MAP Γ X) (u : Obj-abs A) (p : MAP X D) where
  module Insert = Insertion.Parameter 𝒯 M ℱ r u
  step = productMap r (id A)
  i = insert {X = Γ} u
  β = pair-β₁ (id Γ) (const u)
  βstep = pair-β₁ (r ∘ pr₁) (id A ∘ pr₂)
  q = p ∘ r
  lifted = PS.lift-base p pr₁ step βstep
  α : (p ∘ (r ∘ pr₁ {Γ} {A})) =₁ (q ∘ pr₁)
  α = (comp-assoc pr₁ r p) ⁻¹
  first-step = α ∙ lifted
  at-endpoint = comp-unitʳ q ∙ PS.lift-base q pr₁ i β
  inner = PS.lift-base r pr₁ i β
  unit = comp-unitʳ r
  d = PS.lift-base p (r ∘ pr₁) i (unit ∙ inner)
  L = PS.lift-base p (r ∘ pr₁) i inner
  Q = PS.lift-base q pr₁ i β
  v = p ◁ unit
  A₀ = comp-assoc (id Γ) r p
  A₁ = comp-assoc pr₁ r p ▷ i
  raw = PS.lift-base p pr₁ (step ∘ i) Insert.outgoing₁
  normalized = PS.compose-base (p ∘ pr₁) step first-step i at-endpoint
  middle = PS.compose-base (p ∘ pr₁) step lifted i d

  abstract
    distribute : d =₂ (v ∙ L)
    distribute = isoComp-assoc-at v (p ◁ inner) (comp-assoc i (r ∘ pr₁) p) ∙
      isoComp-cong (postWhisker-isoComp-at p unit inner) (idIso (comp-assoc i (r ∘ pr₁) p))

    associated : (d ∙ A₁) =₂ at-endpoint
    associated = isoComp-cong ((right-unitor-comp r p) ⁻¹) (idIso Q) ∙
      (isoComp-assoc-at v A₀ Q) ⁻¹ ∙
      isoComp-cong (idIso v) ((lift-assoc pr₁ (id Γ) i β r p) ⁻¹) ∙
      isoComp-assoc-at v L A₁ ∙
      isoComp-cong distribute (idIso A₁)

    solved : d =₂ (at-endpoint ∙ (α ▷ i))
    solved = isoComp-cong (idIso at-endpoint) ((pre-inverse (comp-assoc pr₁ r p) i) ⁻¹) ∙
      isoComp-cong associated (idIso (A₁ ⁻¹)) ∙
      (cancel-right A₁ d) ⁻¹

    change-frame : normalized =₂ middle
    change-frame = isoComp-unitˡ-at middle ∙
      change-middle (p ∘ pr₁) step i lifted d α at-endpoint (idIso q)
        (solved ∙ isoComp-unitˡ-at d)

    comparison : raw =₂ normalized
    comparison = change-frame ⁻¹ ∙
      (PS.lift-compose p pr₁ step i βstep (unit ∙ inner)) ⁻¹

module Lifted {Γ X A D : CAT} (r : MAP Γ X) (u : Obj-abs A) (p : MAP X D) where
  module Insert = Insertion.Parameter 𝒯 M ℱ r u
  module Source = Incoming r u p (idIso (p ∘ r))
  module Target = Outgoing r u p
  corner = insert-natural r u

  abstract
    comparison : PS.Square (p ∘ pr₁) Source.normalized Target.normalized corner
    comparison = Source.comparison ∙ (isoComp-unitˡ-at _ ) ⁻¹ ∙
      PS.lift-square p pr₁ Insert.incoming₁ Insert.outgoing₁ corner Insert.projection₁ ∙
      isoComp-cong (Target.comparison ⁻¹) (idIso ((p ∘ pr₁) ◁ corner))

module ConstantSection {X K C : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ id X) (v : Obj-abs C) where
  tπ = terminal-iso (terminate X ∘ π) (terminate K)
  ti = terminal-iso (terminate K ∘ i) (terminate X)
  s = section-image π i b (terminate X)
  normal = ti ∙ (tπ ▷ i)
  A₀ = comp-assoc i (terminate X ∘ π) v
  A₁ = comp-assoc i (terminate K) v
  B₀ = comp-assoc π (terminate X) v ▷ i
  α = v ◁ ti
  β = v ◁ (tπ ▷ i)
  γ = (v ◁ tπ) ▷ i
  F = PS.lift-base v (terminate X ∘ π) i normal

  abstract
    normalize : F =₂ (const-pre v i ∙ γ)
    normalize = (isoComp-assoc-at α A₁ γ) ⁻¹ ∙
      isoComp-cong (idIso α) ((whisker-mixed-at tπ i v) ⁻¹) ∙
      isoComp-assoc-at α β A₀ ∙
      isoComp-cong (postWhisker-isoComp-at v ti (tπ ▷ i)) (idIso A₀)

    comparison : section-image π i b (const v) =₂ (const-pre v i ∙ (const-pre v π ▷ i))
    comparison = isoComp-cong (idIso (const-pre v i))
        ((preWhisker-isoComp-at (v ◁ tπ) (comp-assoc π (terminate X) v) i) ⁻¹) ∙
      isoComp-assoc-at (const-pre v i) γ B₀ ∙
      isoComp-cong normalize (idIso B₀) ∙
      isoComp-cong
        (isoComp-cong (postWhisker v ◁ terminal-Iso₂ s normal) (idIso A₀)) (idIso B₀) ∙
      section-comp π i b (terminate X) v
```
