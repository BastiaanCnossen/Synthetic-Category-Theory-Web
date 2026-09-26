# Product symmetry respects isomorphisms of restrictions

The comparison for product symmetry is natural in the restricted functor.
We verify this on each projection, retaining the action of the given
isomorphism on the varying coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.SwapRestrictionData as Swap
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.SwapRestrictionNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; substitution-square-projection; projected-square)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₁; pair-cong-triangle₂)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
module PS = Projections 𝒯

module Naturality {X A B : CAT} {u v : MAP A B} (α : u =₁ v) where
  module U = Swap.Coordinates 𝒯 {X} u
  module V = Swap.Coordinates 𝒯 {X} v
  S = swap {X} {A}
  T = swap {X} {B}
  Ru = productMap u (id X)
  Rv = productMap v (id X)
  Lu = productRestriction X u
  Lv = productRestriction X v
  Rα = productMap-cong α (idIso (id X))
  Lα = productMap-cong (idIso (id X)) α
  η : (u ∘ pr₂ {C = X}) =₁ (v ∘ pr₂ {C = X})
  η = α ▷ pr₂
  ru = transport-pre pr₁ Ru (pair-β₁ (u ∘ pr₁) (id X ∘ pr₂)) S
  rv = transport-pre pr₁ Rv (pair-β₁ (v ∘ pr₁) (id X ∘ pr₂)) S
  hu = PS.lift-base u pr₁ S (pair-β₁ pr₂ pr₁)
  hv = PS.lift-base v pr₁ S (pair-β₁ pr₂ pr₁)
  tu = transport-pre pr₁ T (pair-β₁ pr₂ pr₁) Lu
  tv = transport-pre pr₁ T (pair-β₁ pr₂ pr₁) Lv
  bu = pair-β₂ (id X ∘ pr₁) (u ∘ pr₂)
  bv = pair-β₂ (id X ∘ pr₁) (v ∘ pr₂)
  ru₂ = pair-β₂ (u ∘ pr₁) (id X ∘ pr₂)
  rv₂ = pair-β₂ (v ∘ pr₁) (id X ∘ pr₂)
  lu₁ = pair-β₁ (id X ∘ pr₁) (u ∘ pr₂)
  lv₁ = pair-β₁ (id X ∘ pr₁) (v ∘ pr₂)
  rb-u = comp-unitˡ pr₂ ∙ ru₂
  rb-v = comp-unitˡ pr₂ ∙ rv₂
  lb-u = comp-unitˡ pr₁ ∙ lu₁
  lb-v = comp-unitˡ pr₁ ∙ lv₁

  abstract
    source-change₁ : (V.first-source-base ∙ (pr₁ ◁ (Rα ▷ S))) =₂ (η ∙ U.first-source-base)
    source-change₁ = paste-squares ru rv hu hv
      (pr₁ ◁ (Rα ▷ S)) ((α ▷ pr₁) ▷ S) η
      (pre-square-projection pr₁ Rα (α ▷ pr₁)
        (pair-β₁ (u ∘ pr₁) (id X ∘ pr₂)) (pair-β₁ (v ∘ pr₁) (id X ∘ pr₂)) S
        (pair-cong-triangle₁ (α ▷ pr₁) (idIso (id X) ▷ pr₂)))
      (lift-base-outer pr₁ pr₂ S (pair-β₁ pr₂ pr₁) α)

    target-change₁ : (V.first-target-base ∙ (pr₁ ◁ (T ◁ Lα))) =₂ (η ∙ U.first-target-base)
    target-change₁ = paste-squares tu tv bu bv
      (pr₁ ◁ (T ◁ Lα)) (pr₂ ◁ Lα) η
      (substitution-square-projection pr₁ T pr₂ (pair-β₁ pr₂ pr₁) Lα)
      (pair-cong-triangle₂ (idIso (id X) ▷ pr₁) (α ▷ pr₂))

    right-fixed : PS.Square pr₂ rb-u rb-v Rα
    right-fixed = isoComp-cong (idIso (comp-unitˡ pr₂))
      (isoComp-unitˡ-at ru₂ ∙
      (isoComp-cong (preWhisker-idIso (id X) pr₂) (idIso ru₂) ∙
        pair-cong-triangle₂ (α ▷ pr₁) (idIso (id X) ▷ pr₂))) ∙
      isoComp-assoc-at (comp-unitˡ pr₂) rv₂ (pr₂ ◁ Rα)

    left-fixed : PS.Square pr₁ lb-u lb-v Lα
    left-fixed = isoComp-cong (idIso (comp-unitˡ pr₁))
      (isoComp-unitˡ-at lu₁ ∙
      (isoComp-cong (preWhisker-idIso (id X) pr₁) (idIso lu₁) ∙
        pair-cong-triangle₁ (idIso (id X) ▷ pr₁) (α ▷ pr₂))) ∙
      isoComp-assoc-at (comp-unitˡ pr₁) lv₁ (pr₁ ◁ Lα)

    source-change₂ : (V.second-source-base ∙ (pr₂ ◁ (Rα ▷ S))) =₂ U.second-source-base
    source-change₂ = PS.pre-square pr₂ S rb-u rb-v (pair-β₂ pr₂ pr₁) Rα right-fixed

    target-change₂ : (V.second-target-base ∙ (pr₂ ◁ (T ◁ Lα))) =₂ U.second-target-base
    target-change₂ = PS.post-square pr₂ T (pair-β₂ pr₂ pr₁) lb-u lb-v Lα left-fixed

    first : (pr₁ ◁ (V.value ∙ (Rα ▷ S))) =₂ (pr₁ ◁ ((T ◁ Lα) ∙ U.value))
    first = (projected-square pr₁ (T ◁ Lα) U.value V.value (Rα ▷ S)
      U.first-target-base V.first-target-base η U.first-source-base V.first-source-base
      target-change₁ U.projection₁ V.projection₁ source-change₁) ⁻¹

    second : (pr₂ ◁ (V.value ∙ (Rα ▷ S))) =₂ (pr₂ ◁ ((T ◁ Lα) ∙ U.value))
    second = (projected-square pr₂ (T ◁ Lα) U.value V.value (Rα ▷ S)
      U.second-target-base V.second-target-base (idIso pr₁) U.second-source-base V.second-source-base
      ((isoComp-unitˡ-at U.second-target-base) ⁻¹ ∙ target-change₂)
      U.projection₂ V.projection₂
      ((isoComp-unitˡ-at U.second-source-base) ⁻¹ ∙ source-change₂)) ⁻¹

    comparison : (V.value ∙ (Rα ▷ S)) =₂ ((T ◁ Lα) ∙ U.value)
    comparison = pair-iso-extensionality first second
```
