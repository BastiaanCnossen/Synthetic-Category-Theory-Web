# Case distinction with a parameter

Copair the two families and precompose with the inverse of distributivity.
The two restriction comparisons follow from its inverse comparison and the
copairing beta comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section06.CoproductCalculus.ParametrizedCases
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U using (module Distributivity)

module Cases {X C D E : CAT} (f : MAP (X × C) E) (g : MAP (X × D) E) where

  module Distribution = Distributivity X C D
  e = Distribution.distribute-isEquiv
  inverse = IsEquiv.inverse e
  left : MAP (X × C) (X × (C ⊔ D))
  left = productMap (id X) in₁
  right : MAP (X × D) (X × (C ⊔ D))
  right = productMap (id X) in₂

  cases : MAP (X × (C ⊔ D)) E
  cases = copair f g ∘ inverse

  inverse-left : (inverse ∘ left) =₁ in₁
  inverse-left = comp-unitˡ in₁ ∙
    (((IsEquiv.sectionIso e) ⁻¹ ▷ in₁) ∙
    ((comp-assoc in₁ Distribution.distribute inverse) ⁻¹ ∙
      (inverse ◁ (copair-β₁ left right) ⁻¹)))

  inverse-right : (inverse ∘ right) =₁ in₂
  inverse-right = comp-unitˡ in₂ ∙
    (((IsEquiv.sectionIso e) ⁻¹ ▷ in₂) ∙
    ((comp-assoc in₂ Distribution.distribute inverse) ⁻¹ ∙
      (inverse ◁ (copair-β₂ left right) ⁻¹)))

  cases-β₁ : (cases ∘ left) =₁ f
  cases-β₁ = copair-β₁ f g ∙
    ((copair f g ◁ inverse-left) ∙ comp-assoc left inverse (copair f g))

  cases-β₂ : (cases ∘ right) =₁ g
  cases-β₂ = copair-β₂ f g ∙
    ((copair f g ◁ inverse-right) ∙ comp-assoc right inverse (copair f g))
```
