# Transporting native comparison animae

The pullback encoding a comparison over a base has a terminal right
corner. Restriction along an equivalence over the base gives an
equivalence between these encodings. Changing either endpoint along
a specified relative identification also gives an equivalence.

In both constructions, the commuting squares are defined on the entire
comparison animae. They retain the triangle witnesses, not only the
underlying comparisons. The terminal right corner remains terminal
throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyPairing as Pairing
import SCT.VolumeI.Chapter01.Section03.Whiskering as Multiplication
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Cancellation
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport as Transport

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.Transport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints-map; changeEndpoints-map-isEquiv)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (change-map-evaluate)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonAlgebra 𝒯 using (left-boundary)
open Param vocabulary terminal products productLaws composition vertical using (const-comp; const-cong; assoc)
open Param.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (whisker-mixed-general)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (pre-composition)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pre-constant)
open Multiplication vocabulary terminal products productLaws composition vertical whiskering
  using (rightMultiply; rightMultiply-isEquiv; right-evaluate)
open Cancellation vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Restriction {B C D S : CAT} {b : MAP B S} {f : MAP C S} {g : MAP D S}
  (q : FunctorOver b f) (u v : FunctorOver f g) where
  r = FunctorLift.lift q
  τ = FunctorLift.comparison q
  h = FunctorLift.lift u
  k = FunctorLift.lift v
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  a₀ = comp-assoc r h g
  a₁ = comp-assoc r k g
  module Source = Encoding u v
  module Target = Encoding (compose-over u q) (compose-over v q)
  left : MAP Source.Left Target.Left
  left = preWhisker r
  base : MAP Source.Middle Target.Middle
  base = changeEndpoints-map a₀ τ ∘ preWhisker r

  opaque
    base-at : {A : CAT} (γ : MAP A Source.Middle) →
      (base ∘ γ) =₁ (const τ ∙ ((γ ▷ r) ∙ const (a₀ ⁻¹)))
    base-at γ = change-map-evaluate a₀ τ (γ ▷ r) ∙
      comp-assoc γ (preWhisker r) (changeEndpoints-map a₀ τ)

    mixed : (const a₁ ∙ (postWhisker g ▷ r)) =₁ ((g ◁ left) ∙ const a₀)
    mixed = isoComp-cong (postWhisker g ◁ comp-unitʳ (preWhisker r)) (idIso (const a₀)) ∙
      (whisker-mixed-general (id Source.Left) r g ∙
        isoComp-cong (idIso (const a₁)) (preWhisker r ◁ (comp-unitʳ (postWhisker g)) ⁻¹))

    left-normalization : (Target.leftMap ∘ left) =₁ (const Target.θv ∙ (g ◁ left))
    left-normalization = isoComp-cong (const-pre Target.θv left) (idIso _) ∙
      isoComp-pre (const Target.θv) (postWhisker g) left

    leftSquare : (Target.leftMap ∘ left) =₁ (base ∘ Source.leftMap)
    leftSquare = (base-at Source.leftMap) ⁻¹ ∙
      ((isoComp-cong (idIso (const τ))
        (isoComp-cong
          (isoComp-cong (pre-constant θv r) (idIso _) ∙ pre-composition (const θv) (postWhisker g) r)
          (idIso (const (a₀ ⁻¹))))) ⁻¹ ∙
      ((left-boundary a₀ a₁ (θv ▷ r) τ (postWhisker g ▷ r) (g ◁ left) mixed) ⁻¹ ∙
        left-normalization))

    rightSquare : (Target.rightMap ∘ id One) =₁ (base ∘ Source.rightMap)
    rightSquare = (base-at Source.rightMap) ⁻¹ ∙
      ((const-comp τ ((θu ▷ r) ∙ a₀ ⁻¹) ∙
        isoComp-cong (idIso (const τ))
          (const-comp (θu ▷ r) (a₀ ⁻¹) ∙
            isoComp-cong (pre-constant θu r) (idIso (const (a₀ ⁻¹))))) ⁻¹ ∙
        comp-unitʳ Target.rightMap)

  cospan : CospanMap Source.leftMap Source.rightMap Target.leftMap Target.rightMap
  cospan = record { left = left ; right = id One ; base = base
    ; leftSquare = leftSquare ; rightSquare = rightSquare }

  functor : MAP Source.category Target.category
  functor = CospanMap.pullbackMap cospan

  opaque
    equivalence : IsEquiv r → IsEquiv functor
    equivalence er = CospanEquivalence.pullbackMap-isEquiv cospan
      (preWhisker-isEquiv r er h k) (id-isEquiv One)
      (equiv-compose (preWhisker r) (changeEndpoints-map a₀ τ)
        (preWhisker-isEquiv r er (g ∘ h) f) (changeEndpoints-map-isEquiv a₀ τ))

module Endpoints {C D S : CAT} {f : MAP C S} {g : MAP D S}
  {u u′ v v′ : FunctorOver f g} (Φ : FunctorOverIso u u′) (Ψ : FunctorOverIso v v′) where
  module Source = Encoding u v
  module Target = Encoding u′ v′
  α = FunctorOverIso.underlying Φ
  β = FunctorOverIso.underlying Ψ
  p = g ◁ α
  q = g ◁ β
  module Left = Transport.Conjugation 𝒯 P α β using (forward; evaluate; isEquiv)
  base : MAP Source.Middle Target.Middle
  base = rightMultiply (p ⁻¹)

  opaque
    left-normalization : (Target.leftMap ∘ Left.forward) =₁
      (const Target.θv ∙ (const q ∙ ((g ◁ id Source.Left) ∙ const (p ⁻¹))))
    left-normalization = isoComp-cong (idIso (const Target.θv))
      (Transport.post-conjugation 𝒯 P g α β (id Source.Left) ∙
        (postWhisker g ◁ (Left.evaluate (id Source.Left) ∙ (comp-unitʳ Left.forward) ⁻¹))) ∙
      isoComp-evaluate (const Target.θv) (postWhisker g) Left.forward
        (const-pre Target.θv Left.forward) (idIso _)

    left-matching : (const {P = Source.Left} Target.θv ∙ const q) =₁ const Source.θv
    left-matching = const-cong (FunctorOverIso.compatible Ψ) ∙ const-comp Target.θv q

    leftSquare : (Target.leftMap ∘ Left.forward) =₁ (base ∘ Source.leftMap)
    leftSquare = (right-evaluate (p ⁻¹) Source.leftMap) ⁻¹ ∙
      (isoComp-cong
        (isoComp-cong (idIso (const Source.θv)) (comp-unitʳ (postWhisker g)))
        (idIso (const (p ⁻¹))) ∙
      ((assoc (const Source.θv) (g ◁ id Source.Left) (const (p ⁻¹))) ⁻¹ ∙
      (isoComp-cong left-matching (idIso ((g ◁ id Source.Left) ∙ const (p ⁻¹))) ∙
      ((assoc (const Target.θv) (const q) ((g ◁ id Source.Left) ∙ const (p ⁻¹))) ⁻¹ ∙
        left-normalization))))

    right-matching : (Source.θu ∙ p ⁻¹) =₂ Target.θu
    right-matching = cancel-right p Target.θu ∙
      isoComp-cong ((FunctorOverIso.compatible Φ) ⁻¹) (idIso (p ⁻¹))

    rightSquare : (Target.rightMap ∘ id One) =₁ (base ∘ Source.rightMap)
    rightSquare = (right-evaluate (p ⁻¹) Source.rightMap) ⁻¹ ∙
      ((const-cong right-matching ∙ const-comp Source.θu (p ⁻¹)) ⁻¹ ∙
        comp-unitʳ Target.rightMap)

  cospan : CospanMap Source.leftMap Source.rightMap Target.leftMap Target.rightMap
  cospan = record { left = Left.forward ; right = id One ; base = base
    ; leftSquare = leftSquare ; rightSquare = rightSquare }

  functor : MAP Source.category Target.category
  functor = CospanMap.pullbackMap cospan

  opaque
    equivalence : IsEquiv functor
    equivalence = CospanEquivalence.pullbackMap-isEquiv cospan
      Left.isEquiv (id-isEquiv One) (rightMultiply-isEquiv (p ⁻¹))
```
