# The second coordinate of product substitution

The second coordinate of substitution by `σ × id C` is independent of
the functor in the first coordinate. Its composition law follows by
normalizing the identity functor's left unitor, using the already chosen
projection witness of the substitution comparison, and cancelling the
external associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section04.ProductSecondCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Compatibility 𝒯 M using (slice-comparison)
module Coordinates = ProductSubstitution.Coordinates 𝒯 M
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)

second-normalization : {Y X Z : CAT} (C : CAT) (f : MAP X Z) (σ : MAP Y X)
  → (Coordinates.second C f σ) =₂
      (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂) ∙
        (comp-unitˡ pr₂ ▷ productMap σ (id C)))
second-normalization C f σ = coordinate-left-unit pr₂ (id C) pr₂ (productMap σ (id C))
  (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂))

second-coordinate-assoc : {W Y X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP Y X) (τ : MAP W Y)
  →
      (Coordinates.second C f (σ ∘ τ) ∙
        (((id C ∘ pr₂) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (id C ∘ pr₂))) =₂
      ((idIso (id C) ▷ pr₂) ∙
        (Coordinates.second C (f ∘ σ) τ ∙
          (Coordinates.second C f σ ▷ productMap τ (id C))))
second-coordinate-assoc C f σ τ =
  let s = productMap σ (id C)
      t = productMap τ (id C)
      st = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      q = id C ∘ pr₂
      v = comp-unitˡ pr₂
      b = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      bst = pair-β₂ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
      S = Coordinates.second C f σ
      T = Coordinates.second C (f ∘ σ) τ
      Aq = comp-assoc t s q
      Aπ = comp-assoc t s pr₂
      vv = (v ▷ s) ▷ t
      normalized = T ∙ (S ▷ t)

      leftStart :
        (Coordinates.second C f (σ ∘ τ) ∙ ((q ◁ κ) ∙ Aq)) =₂
        ((bst ∙ (pr₂ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq))
      leftStart = (isoComp-assoc-at bst (pr₂ ◁ κ) ((v ▷ (s ∘ t)) ∙ Aq)) ⁻¹ ∙
        (isoComp-cong (idIso bst) (isoComp-assoc-at (pr₂ ◁ κ) (v ▷ (s ∘ t)) Aq) ∙
        (isoComp-cong (idIso bst) (isoComp-cong (interchange-at v κ) (idIso Aq)) ∙
        (reassociateFour bst (v ▷ st) (q ◁ κ) Aq ∙
          isoComp-cong (second-normalization C f (σ ∘ τ)) (idIso ((q ◁ κ) ∙ Aq)))))

      middle :
        ((bst ∙ (pr₂ ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq)) =₂
        ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv))
      middle = isoComp-cong (Coordinates.projection₂ C σ τ)
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
        ((preWhisker t ◁ (second-normalization C f σ) ⁻¹) ∙
          (preWhisker-isoComp-at b (v ▷ s) t) ⁻¹)

      insertIdentity : normalized =₂ ((idIso (id C) ▷ pr₂) ∙ normalized)
      insertIdentity =
        (isoComp-unitˡ-at normalized ∙ isoComp-cong (preWhisker-idIso (id C) pr₂) (idIso normalized)) ⁻¹
  in insertIdentity ∙ (rightFinish ∙ (cancellation ∙ (middle ∙ leftStart)))
```
