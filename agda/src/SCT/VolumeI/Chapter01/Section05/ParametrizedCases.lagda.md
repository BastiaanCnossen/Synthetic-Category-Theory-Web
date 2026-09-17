# Case distinction with a parameter

Copair the two families and precompose with the inverse of distributivity.
The two restriction comparisons follow from its inverse comparison and the
copairing beta comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section05.ParametrizedCases
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section04.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.Distributivity 𝒯 M B P U using (module Distributivity)

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

  inverse-left : =₁ (inverse ∘ left) in₁
  inverse-left = comp-unitˡ in₁ ∙
    ((invIso (IsEquiv.sectionIso e) ▷ in₁) ∙
    (invIso (comp-assoc in₁ Distribution.distribute inverse) ∙
      (inverse ◁ invIso (copair-β₁ left right))))

  inverse-right : =₁ (inverse ∘ right) in₂
  inverse-right = comp-unitˡ in₂ ∙
    ((invIso (IsEquiv.sectionIso e) ▷ in₂) ∙
    (invIso (comp-assoc in₂ Distribution.distribute inverse) ∙
      (inverse ◁ invIso (copair-β₂ left right))))

  cases-β₁ : =₁ (cases ∘ left) f
  cases-β₁ = copair-β₁ f g ∙
    ((copair f g ◁ inverse-left) ∙ comp-assoc left inverse (copair f g))

  cases-β₂ : =₁ (cases ∘ right) g
  cases-β₂ = copair-β₂ f g ∙
    ((copair f g ◁ inverse-right) ∙ comp-assoc right inverse (copair f g))
```
