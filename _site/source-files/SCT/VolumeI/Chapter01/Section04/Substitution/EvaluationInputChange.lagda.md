# Simultaneous evaluation and change of parameter

The product comparison used to restrict an evaluation also accepts an
arbitrary pair of inputs. We compare this instance with successive
restriction and evaluation, retaining the chosen product comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as CoordinateComparisons
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FramedSubstitution as FramedSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingAssembly as Assembly
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairingFunctoriality as ChosenPairingFunctoriality

module SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationInputChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M using (mapUncurry-restrict)
open Compatibility 𝒯 M using (slice-comparison)
open MapComposition 𝒯 M
open EvaluationParameterChange 𝒯 M using (module AtCoordinates)
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle using (coordinate-at; coordinate-at-change; post-change-with-inverse; cancel-forward)
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (coordinate-at-outer-composition)
private
  module Chosen = ChosenPairing vocabulary terminal products productLaws composition vertical whiskering
  module ChosenLaws = ChosenPairingFunctoriality vocabulary terminal products productLaws
    composition vertical whiskering pentagonTriangle
  module Framed = FramedSubstitution vocabulary terminal products productLaws composition vertical whiskering
open Assembly vocabulary terminal products productLaws composition vertical whiskering
  Chosen.operations ChosenLaws.functoriality using (module PairingAssembly)
module ProductCoordinates = ProductSubstitution.Coordinates 𝒯 M
open ProductSecondCoordinate 𝒯 M using (second-normalization)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂; left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; postWhisker-id-at; preWhisker-comp-at)

at-second-normalization : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → (AtCoordinates.second f p x) =₂ (pair-β₂ p x ∙ (comp-unitˡ pr₂ ▷ pair p x))
at-second-normalization {C = C} f p x =
  isoComp-cong (idIso (pair-β₂ p x)) (left-unitor-comp (pair p x) pr₂) ∙
    (isoComp-assoc-at (pair-β₂ p x) (comp-unitˡ (pr₂ ∘ pair p x)) (comp-assoc (pair p x) pr₂ (id C)) ∙
    (isoComp-cong (postWhisker-id-at (pair-β₂ p x)) (idIso (comp-assoc (pair p x) pr₂ (id C))) ∙
      (isoComp-assoc-at (comp-unitˡ x) (id C ◁ pair-β₂ p x) (comp-assoc (pair p x) pr₂ (id C))) ⁻¹))

at-comparison-projection₁ : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → (pair-β₁ (f ∘ p) x ∙ (pr₁ ◁ AtCoordinates.comparison f p x)) =₂
      (AtCoordinates.first f p x ∙
        ((pair-β₁ (f ∘ pr₁) (id C ∘ pr₂) ▷ pair p x) ∙
          (comp-assoc (pair p x) (productMap f (id C)) pr₁) ⁻¹))
at-comparison-projection₁ {C = C} f p x =
  pair-pre-cong-triangle₁ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
    (AtCoordinates.first f p x) (AtCoordinates.second f p x) ∙
      isoComp-cong (idIso (pair-β₁ (f ∘ p) x)) (postWhisker pr₁ ◁ AtCoordinates.normalization f p x)

at-comparison-projection₂ : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → (pair-β₂ (f ∘ p) x ∙ (pr₂ ◁ AtCoordinates.comparison f p x)) =₂
      (AtCoordinates.second f p x ∙
        ((pair-β₂ (f ∘ pr₁) (id C ∘ pr₂) ▷ pair p x) ∙
          (comp-assoc (pair p x) (productMap f (id C)) pr₂) ⁻¹))
at-comparison-projection₂ {C = C} f p x =
  pair-pre-cong-triangle₂ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
    (AtCoordinates.first f p x) (AtCoordinates.second f p x) ∙
      isoComp-cong (idIso (pair-β₂ (f ∘ p) x)) (postWhisker pr₂ ◁ AtCoordinates.normalization f p x)

first-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  →
      (AtCoordinates.first f (σ ∘ p) x ∙
        (((f ∘ pr₁) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (f ∘ pr₁))) =₂
      (comp-assoc p σ f ∙
        (AtCoordinates.first (f ∘ σ) p x ∙ (ProductCoordinates.first C f σ ▷ pair p x)))
first-input-change {C = C} f σ p x =
  let h = productMap σ (id C)
      t = pair p x
      n = AtCoordinates.comparison σ p x
      b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
      c = AtCoordinates.first σ p x
      original = coordinate-at f pr₁ h b
      u = ProductCoordinates.first C f σ
      w = AtCoordinates.first (f ∘ σ) p x
      A = comp-assoc p σ f
      corner = comp-assoc pr₁ σ f
      mid = comp-assoc t (σ ∘ pr₁) f
      simplify = (preWhisker t ◁ cancel-forward corner original) ∙
        (preWhisker-isoComp-at corner u t) ⁻¹
      normalizeLong = isoComp-cong (idIso (f ◁ c)) (isoComp-cong (idIso mid) simplify) ∙
        (isoComp-cong (idIso (f ◁ c)) (isoComp-assoc-at mid (corner ▷ t) (u ▷ t)) ∙
        (isoComp-assoc-at (f ◁ c) (mid ∙ (corner ▷ t)) (u ▷ t) ∙
        (isoComp-cong (coordinate-at-outer-composition f σ pr₁ t (pair-β₁ p x)) (idIso (u ▷ t)) ∙
          (isoComp-assoc-at A w (u ▷ t)) ⁻¹)))
  in normalizeLong ⁻¹ ∙
    coordinate-at-change f pr₁ h t (pair (σ ∘ p) x) n b (pair-β₁ (σ ∘ p) x) c
      (at-comparison-projection₁ σ p x)

second-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  →
      (AtCoordinates.second f (σ ∘ p) x ∙
        (((id C ∘ pr₂) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (id C ∘ pr₂))) =₂
      (idIso x ∙
        (AtCoordinates.second (f ∘ σ) p x ∙ (ProductCoordinates.second C f σ ▷ pair p x)))
second-input-change {C = C} f σ p x =
  let h = productMap σ (id C)
      t = pair p x
      n = AtCoordinates.comparison σ p x
      q = id C ∘ pr₂
      v = comp-unitˡ pr₂
      b = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      b′ = pair-β₂ (σ ∘ p) x
      S = ProductCoordinates.second C f σ
      T = AtCoordinates.second (f ∘ σ) p x
      normalized = T ∙ (S ▷ t)
      composition = Framed.Composition.compatible h t (pair (σ ∘ p) x) n q pr₂
        (id C ∘ pr₂) x v b b′ S T (AtCoordinates.second f (σ ∘ p) x)
        (second-normalization C f σ) (at-second-normalization f (σ ∘ p) x)
        (at-comparison-projection₂ σ p x)
  in (isoComp-unitˡ-at normalized) ⁻¹ ∙ composition

at-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  →
      (AtCoordinates.comparison f (σ ∘ p) x ∙
        ((productMap f (id C) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (productMap f (id C)))) =₂
      (pair-cong (comp-assoc p σ f) (idIso x) ∙
        (AtCoordinates.comparison (f ∘ σ) p x ∙ (slice-comparison {C = C} f σ ▷ pair p x)))
at-input-change {C = C} f σ p x =
  let u = ProductCoordinates.first C f σ
      v = ProductCoordinates.second C f σ
      w = AtCoordinates.first (f ∘ σ) p x
      z = AtCoordinates.second (f ∘ σ) p x
      a = AtCoordinates.first f (σ ∘ p) x
      d = AtCoordinates.second f (σ ∘ p) x
      η = comp-assoc p σ f
      θ = idIso x
      assembled = PairingAssembly.assemble (f ∘ pr₁) (id C ∘ pr₂)
        (productMap σ (id C)) (pair p x) (pair (σ ∘ p) x) (AtCoordinates.comparison σ p x)
        u v w z a d η θ (first-input-change f σ p x) (second-input-change f σ p x)
      normalizeShort = isoComp-cong (AtCoordinates.normalization f (σ ∘ p) x) (idIso _)
      normalizeLong = isoComp-cong (idIso (pair-cong η θ))
        (isoComp-cong (AtCoordinates.normalization (f ∘ σ) p x)
          (preWhisker (pair p x) ◁ ProductCoordinates.normalization C f σ))
  in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)

```

Postcompose the paired square by evaluation. To recover the desired direction,
we cancel the forward restriction comparison against the prescribed reverse
restriction comparison. The following witness records precisely that cancellation.

```agda
forward-uncurry-restrict : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  → (mapUncurry f ∘ productMap σ (id C)) =₁ (mapUncurry (f ∘ σ))
forward-uncurry-restrict {C = C} f σ = (mapEval ◁ slice-comparison f σ) ∙
  comp-assoc (productMap σ (id C)) (productMap f (id C)) mapEval

forward-uncurry-restrict-cancel : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  → (forward-uncurry-restrict f σ ∙ mapUncurry-restrict f σ) =₂ (idIso (mapUncurry (f ∘ σ)))
forward-uncurry-restrict-cancel {C = C} f σ =
  Framed.post-comparison-inverse mapEval (productMap f (id C))
    (productMap σ (id C)) (slice-comparison {C = C} f σ)

mapUncurry-at-input-change : {Γ Q P C D : CAT}
  (f : MAP P (Map C D)) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  → let n = AtCoordinates.comparison σ p x
    in
      (applyTerm-cong (comp-assoc p σ f) (idIso x) ∙ mapUncurry-at (f ∘ σ) p x) =₂
      (mapUncurry-at f (σ ∘ p) x ∙
        ((mapUncurry f ◁ n) ∙
          (comp-assoc (pair p x) (productMap σ (id C)) (mapUncurry f) ∙
            (mapUncurry-restrict f σ ▷ pair p x))))
mapUncurry-at-input-change {C = C} f σ p x =
  post-change-with-inverse mapEval (productMap f (id C)) (productMap σ (id C))
    (pair p x) (pair (σ ∘ p) x) (AtCoordinates.comparison σ p x)
    (slice-comparison f σ) (AtCoordinates.comparison (f ∘ σ) p x)
    (AtCoordinates.comparison f (σ ∘ p) x)
    (pair-cong (comp-assoc p σ f) (idIso x)) (at-input-change f σ p x)
    (mapUncurry-restrict f σ) (forward-uncurry-restrict-cancel f σ)
```
