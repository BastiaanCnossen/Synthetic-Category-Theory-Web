# Four points in a product

Distributivity identifies two copies of the two-point category with its
square. The four inclusions are ordered `(00,10,01,11)`. Consequently,
products of two specified two-point equivalences are given by the four
corresponding pairs of points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter02.Section01.SquareCalculus.FourPoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open Coproducts.CoproductStructure B public
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B public
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯
  using (pair-after; productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U
  using (module Distributivity)

Two Four : CAT
Two = One ⊔ One
Four = Two ⊔ Two

points₄ : {C : CAT} → Obj-abs C → Obj-abs C → Obj-abs C → Obj-abs C → MAP Four C
points₄ x₀₀ x₁₀ x₀₁ x₁₁ = copair (copair x₀₀ x₁₀) (copair x₀₁ x₁₁)

points₄-post : {C D : CAT} (h : MAP C D) (x₀₀ x₁₀ x₀₁ x₁₁ : Obj-abs C) →
  (h ∘ points₄ x₀₀ x₁₀ x₀₁ x₁₁) =₁
  points₄ (h ∘ x₀₀) (h ∘ x₁₀) (h ∘ x₀₁) (h ∘ x₁₁)
points₄-post h x₀₀ x₁₀ x₀₁ x₁₁ =
  copair-cong (copair-post x₀₀ x₁₀ h) (copair-post x₀₁ x₁₁ h) ∙
    copair-post (copair x₀₀ x₁₀) (copair x₀₁ x₁₁) h

points₄-cong : {C : CAT} {x₀₀ x₁₀ x₀₁ x₁₁ y₀₀ y₁₀ y₀₁ y₁₁ : Obj-abs C} →
  x₀₀ =₁ y₀₀ → x₁₀ =₁ y₁₀ → x₀₁ =₁ y₀₁ → x₁₁ =₁ y₁₁ →
  points₄ x₀₀ x₁₀ x₀₁ x₁₁ =₁ points₄ y₀₀ y₁₀ y₀₁ y₁₁
points₄-cong α β γ δ = copair-cong (copair-cong α β) (copair-cong γ δ)

grid : MAP Four (Two × Two)
grid = copair (pair (id Two) (const in₁)) (pair (id Two) (const in₂))

module Distribution = Distributivity Two One One using (distribute; distribute-isEquiv)

grid-isEquiv : IsEquiv grid
grid-isEquiv = equiv-transport comparison
  (equiv-compose units Distribution.distribute
    (coproductMap-isEquiv _ _ unit-equivalence unit-equivalence)
    Distribution.distribute-isEquiv)
  where
  units = coproductMap (product-unitʳ-inverse Two) (product-unitʳ-inverse Two)
  unit-equivalence = equiv-inverse (product-unitʳ-isEquiv Two)
  component : (j : Obj-abs Two) →
    (productMap (id Two) j ∘ product-unitʳ-inverse Two) =₁ pair (id Two) (const j)
  component j = pair-cong (comp-unitˡ (id Two)) (idIso (const j)) ∙
    pair-after (id Two) j (id Two) (terminate Two)
  comparison : (Distribution.distribute ∘ units) =₁ grid
  comparison = copair-cong
    (component in₁ ∙ copair-pre₁ _ _ (product-unitʳ-inverse Two))
    (component in₂ ∙ copair-pre₂ _ _ (product-unitʳ-inverse Two)) ∙
    copair-post _ _ Distribution.distribute

module Rectangle {C D : CAT} (x₀ x₁ : Obj-abs C) (y₀ y₁ : Obj-abs D) where
  rectangle : MAP Four (C × D)
  rectangle = points₄ (pair x₀ y₀) (pair x₁ y₀) (pair x₀ y₁) (pair x₁ y₁)
  horizontalPoints = copair x₀ x₁
  verticalPoints = copair y₀ y₁

  row : (j : Obj-abs Two) (y : Obj-abs D) → (verticalPoints ∘ j) =₁ y →
    (productMap horizontalPoints verticalPoints ∘ pair (id Two) (const j)) =₁
      copair (pair x₀ y) (pair x₁ y)
  row j y ε = row-copair ∙ row-normal
    where
    constant-at : (i : Obj-abs Two) → (const y ∘ i) =₁ y
    constant-at i = comp-unitʳ y ∙
      ((y ◁ terminal-iso (terminate Two ∘ i) (id One)) ∙ comp-assoc i (terminate Two) y)
    row-copair : pair horizontalPoints (const y) =₁ copair (pair x₀ y) (pair x₁ y)
    row-copair = coproduct-reflect _ _
      ((copair-β₁ (pair x₀ y) (pair x₁ y)) ⁻¹ ∙
        (pair-cong (copair-β₁ x₀ x₁) (constant-at in₁) ∙ pair-pre horizontalPoints (const y) in₁))
      ((copair-β₂ (pair x₀ y) (pair x₁ y)) ⁻¹ ∙
        (pair-cong (copair-β₂ x₀ x₁) (constant-at in₂) ∙ pair-pre horizontalPoints (const y) in₂))
    row-normal : (productMap horizontalPoints verticalPoints ∘ pair (id Two) (const j)) =₁
      pair horizontalPoints (const y)
    row-normal = pair-cong (comp-unitʳ horizontalPoints)
      ((ε ▷ terminate Two) ∙ (comp-assoc (terminate Two) j verticalPoints) ⁻¹) ∙
      pair-after horizontalPoints verticalPoints (id Two) (const j)

  comparison : (productMap horizontalPoints verticalPoints ∘ grid) =₁ rectangle
  comparison = copair-cong (row in₁ y₀ (copair-β₁ y₀ y₁))
    (row in₂ y₁ (copair-β₂ y₀ y₁)) ∙ copair-post _ _ (productMap horizontalPoints verticalPoints)

  isEquiv : IsEquiv horizontalPoints → IsEquiv verticalPoints → IsEquiv rectangle
  isEquiv ex ey = equiv-transport comparison
    (equiv-compose grid (productMap horizontalPoints verticalPoints) grid-isEquiv
      (productMap-isEquiv horizontalPoints verticalPoints ex ey))
```
