# Associativity of restrictions in the second product coordinate

The compositor of `X × -` includes the chosen left unitor of `id X`.
We compare its actual two associative composites. The constant coordinate
uses its projection witness; the varying coordinate uses coordinate
associativity. Product extensionality is assembled by `PairingAssembly`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ProductRestrictionAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductComparisonProjections 𝒯 using (module Normalized)
open import SCT.VolumeI.Chapter01.Section08.ProductCompositionAssociativity 𝒯 M
  using (module CoordinateAssociativity)
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M using (module PairingAssembly)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

module Coordinates {Y X Z : CAT} (C : CAT) (f : MAP X Z) (σ : MAP Y X) where
  substitution = productMap (id C) σ
  module N = Normalized (id C) (id C) σ f (comp-unitˡ (id C)) (idIso (f ∘ σ))
  first = N.first
  second = N.secondBefore
  normalized = pair-cong first second ∙ pair-pre (id C ∘ pr₁) (f ∘ pr₂) substitution

  second-unit : N.second =₂ second
  second-unit = isoComp-unitˡ-at second ∙
    isoComp-cong (preWhisker-idIso (f ∘ σ) pr₂) (idIso second)

  normalization : (productRestriction-comp C σ f) =₂ normalized
  normalization = isoComp-cong (pair-cong-Iso₂ (idIso first) second-unit)
    (idIso (pair-pre (id C ∘ pr₁) (f ∘ pr₂) substitution)) ∙ N.normalization

  projection₁ = N.projection₁
  projection₂ :
    (pair-β₂ (id C ∘ pr₁) ((f ∘ σ) ∘ pr₂) ∙ (pr₂ ◁ productRestriction-comp C σ f)) =₂
    (second ∙ ((pair-β₂ (id C ∘ pr₁) (f ∘ pr₂) ▷ substitution) ∙
      (comp-assoc substitution (productMap (id C) f) pr₂) ⁻¹))
  projection₂ = isoComp-cong second-unit (idIso _) ∙ N.projection₂

constant-normalization : {Y X Z : CAT} (C : CAT) (f : MAP X Z) (σ : MAP Y X)
  → (Coordinates.first C f σ) =₂
      (pair-β₁ (id C ∘ pr₁) (σ ∘ pr₂) ∙
        (comp-unitˡ pr₁ ▷ productMap (id C) σ))
constant-normalization C f σ = coordinate-left-unit pr₁ (id C) pr₁ (productMap (id C) σ)
  (pair-β₁ (id C ∘ pr₁) (σ ∘ pr₂))

constant-coordinate-assoc : {W Y X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP Y X) (τ : MAP W Y)
  →
      (Coordinates.first C f (σ ∘ τ) ∙
        (((id C ∘ pr₁) ◁ productRestriction-comp C τ σ) ∙
          comp-assoc (productMap (id C) τ) (productMap (id C) σ) (id C ∘ pr₁))) =₂
      ((idIso (id C) ▷ pr₁) ∙
        (Coordinates.first C (f ∘ σ) τ ∙
          (Coordinates.first C f σ ▷ productMap (id C) τ)))
constant-coordinate-assoc C f σ τ =
  let s = productMap (id C) σ
      t = productMap (id C) τ
      st = productMap (id C) (σ ∘ τ)
      κ = productRestriction-comp C τ σ
      q = id C ∘ pr₁
      v = comp-unitˡ pr₁
      b = pair-β₁ (id C ∘ pr₁) (σ ∘ pr₂)
      bst = pair-β₁ (id C ∘ pr₁) ((σ ∘ τ) ∘ pr₂)
      S = Coordinates.first C f σ
      T = Coordinates.first C (f ∘ σ) τ
      Aq = comp-assoc t s q
      Aπ = comp-assoc t s pr₁
      vv = (v ▷ s) ▷ t
      normalized = T ∙ (S ▷ t)

      leftStart :
        (Coordinates.first C f (σ ∘ τ) ∙ ((q ◁ κ) ∙ Aq)) =₂
        ((bst ∙ (pr₁ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq))
      leftStart = (isoComp-assoc-at bst (pr₁ ◁ κ) ((v ▷ (s ∘ t)) ∙ Aq)) ⁻¹ ∙
        (isoComp-cong (idIso bst) (isoComp-assoc-at (pr₁ ◁ κ) (v ▷ (s ∘ t)) Aq) ∙
        (isoComp-cong (idIso bst) (isoComp-cong (interchange-at v κ) (idIso Aq)) ∙
        (reassociateFour bst (v ▷ st) (q ◁ κ) Aq ∙
          isoComp-cong (constant-normalization C f (σ ∘ τ)) (idIso ((q ◁ κ) ∙ Aq)))))

      middle :
        ((bst ∙ (pr₁ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq)) =₂
        ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv))
      middle = isoComp-cong (Coordinates.projection₁ C σ τ)
        ((preWhisker-comp-at v s t) ⁻¹)

      cancellation :
        ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv)) =₂
        (T ∙ ((b ▷ t) ∙ vv))
      cancellation = isoComp-cong (idIso T)
          (isoComp-cong (idIso (b ▷ t))
            (isoComp-unitˡ-at vv ∙
              (isoComp-cong (isoComp-inverseˡ-at Aπ) (idIso vv) ∙
                (isoComp-assoc-at (Aπ ⁻¹) Aπ vv) ⁻¹)) ∙
            isoComp-assoc-at (b ▷ t) (Aπ ⁻¹) (Aπ ∙ vv)) ∙
        isoComp-assoc-at T ((b ▷ t) ∙ Aπ ⁻¹) (Aπ ∙ vv)

      rightFinish : (T ∙ ((b ▷ t) ∙ vv)) =₂ normalized
      rightFinish = isoComp-cong (idIso T)
        ((preWhisker t ◁ (constant-normalization C f σ) ⁻¹) ∙
          (preWhisker-isoComp-at b (v ▷ s) t) ⁻¹)

      insertIdentity : normalized =₂ ((idIso (id C) ▷ pr₁) ∙ normalized)
      insertIdentity =
        (isoComp-unitˡ-at normalized ∙ isoComp-cong (preWhisker-idIso (id C) pr₁) (idIso normalized)) ⁻¹
  in insertIdentity ∙ (rightFinish ∙ (cancellation ∙ (middle ∙ leftStart)))

varying-coordinate-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R) →
  (Coordinates.second C f (σ ∘ τ) ∙
    (((f ∘ pr₂) ◁ productRestriction-comp C τ σ) ∙
      comp-assoc (productMap (id C) τ) (productMap (id C) σ) (f ∘ pr₂))) =₂
  ((comp-assoc τ σ f ▷ pr₂) ∙
    (Coordinates.second C (f ∘ σ) τ ∙
      (Coordinates.second C f σ ▷ productMap (id C) τ)))
varying-coordinate-assoc C f σ τ = CoordinateAssociativity.comparison
  pr₂ pr₂ pr₂ τ σ f (productMap (id C) σ) (productMap (id C) τ)
  (productMap (id C) (σ ∘ τ)) (productRestriction-comp C τ σ)
  (pair-β₂ (id C ∘ pr₁) (σ ∘ pr₂))
  (pair-β₂ (id C ∘ pr₁) (τ ∘ pr₂))
  (pair-β₂ (id C ∘ pr₁) ((σ ∘ τ) ∘ pr₂))
  (Coordinates.projection₂ C σ τ)

abstract
  restriction-assoc : {Q R X Z : CAT} (C : CAT)
    (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R) →
    (productRestriction-comp C (σ ∘ τ) f ∙
      ((productMap (id C) f ◁ productRestriction-comp C τ σ) ∙
        comp-assoc (productMap (id C) τ) (productMap (id C) σ) (productMap (id C) f))) =₂
    (productMap-cong (idIso (id C)) (comp-assoc τ σ f) ∙
      (productRestriction-comp C τ (f ∘ σ) ∙
        (productRestriction-comp C σ f ▷ productMap (id C) τ)))
  restriction-assoc C f σ τ =
    let h = productMap (id C) σ
        k = productMap (id C) τ
        l = productMap (id C) (σ ∘ τ)
        κ = productRestriction-comp C τ σ
        sourceTail = (productMap (id C) f ◁ κ) ∙ comp-assoc k h (productMap (id C) f)
        η = productMap-cong (idIso (id C)) (comp-assoc τ σ f)
        normalizeShort = isoComp-cong (Coordinates.normalization C f (σ ∘ τ)) (idIso sourceTail)
        normalizeLong = isoComp-cong (idIso η)
          (isoComp-cong (Coordinates.normalization C (f ∘ σ) τ)
            (preWhisker k ◁ Coordinates.normalization C f σ))
        assembled = PairingAssembly.assemble (id C ∘ pr₁) (f ∘ pr₂) h k l κ
          (Coordinates.first C f σ) (Coordinates.second C f σ)
          (Coordinates.first C (f ∘ σ) τ) (Coordinates.second C (f ∘ σ) τ)
          (Coordinates.first C f (σ ∘ τ)) (Coordinates.second C f (σ ∘ τ))
          (idIso (id C) ▷ pr₁) (comp-assoc τ σ f ▷ pr₂)
          (constant-coordinate-assoc C f σ τ) (varying-coordinate-assoc C f σ τ)
    in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)
```
