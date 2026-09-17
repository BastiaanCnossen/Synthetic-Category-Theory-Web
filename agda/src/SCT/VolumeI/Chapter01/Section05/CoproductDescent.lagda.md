# Descent for coproducts

The two base-change inclusions are obtained by changing the restricted
copairing boundary, applying the nested-pullback equivalence, and swapping
the pullback legs. Their copairing is an equivalence by the reassembly
clause of coproduct universality. This is the comparison functor in
`lem:Descent_For_Coproducts`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section05.CoproductDescent
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section04.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.NestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section05.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P using (pullbackSwap; pullbackSwap-isEquiv)

module Descent {C D Γ Γ′ : CAT} (f : MAP C Γ) (g : MAP D Γ) (φ : MAP Γ′ Γ) where

  combined = copair f g
  Total = Pullback combined φ
  totalProjection : MAP Total (C ⊔ D)
  totalProjection = pb₁
  module LeftBoundary = ChangeLeft (invIso (copair-β₁ f g)) φ
  module RightBoundary = ChangeLeft (invIso (copair-β₂ f g)) φ
  module LeftNesting = Nested in₁ combined φ
  module RightNesting = Nested in₂ combined φ

  identify₁ : MAP (Pullback f φ) (Pullback totalProjection in₁)
  identify₁ = pullbackSwap in₁ totalProjection ∘ (LeftNesting.insert ∘ LeftBoundary.forward)

  identify₂ : MAP (Pullback g φ) (Pullback totalProjection in₂)
  identify₂ = pullbackSwap in₂ totalProjection ∘ (RightNesting.insert ∘ RightBoundary.forward)

  identify₁-isEquiv : IsEquiv identify₁
  identify₁-isEquiv = equiv-compose (LeftNesting.insert ∘ LeftBoundary.forward)
    (pullbackSwap in₁ totalProjection)
    (equiv-compose LeftBoundary.forward LeftNesting.insert LeftBoundary.forward-isEquiv LeftNesting.insert-isEquiv)
    (pullbackSwap-isEquiv in₁ totalProjection)

  identify₂-isEquiv : IsEquiv identify₂
  identify₂-isEquiv = equiv-compose (RightNesting.insert ∘ RightBoundary.forward)
    (pullbackSwap in₂ totalProjection)
    (equiv-compose RightBoundary.forward RightNesting.insert RightBoundary.forward-isEquiv RightNesting.insert-isEquiv)
    (pullbackSwap-isEquiv in₂ totalProjection)

  include₁ : MAP (Pullback f φ) Total
  include₁ = pb₁ ∘ identify₁
  include₂ : MAP (Pullback g φ) Total
  include₂ = pb₁ ∘ identify₂

  descent : MAP (Pullback f φ ⊔ Pullback g φ) Total
  descent = copair include₁ include₂

  reassembly-comparison : =₁
    (reassemble totalProjection ∘ coproductMap identify₁ identify₂) descent
  reassembly-comparison = copair-cong (copair-pre₁ pb₁ pb₁ identify₁) (copair-pre₂ pb₁ pb₁ identify₂) ∙
    copair-post (in₁ ∘ identify₁) (in₂ ∘ identify₂) (reassemble totalProjection)

  descent-isEquiv : IsEquiv descent
  descent-isEquiv = equiv-transport reassembly-comparison
    (equiv-compose (coproductMap identify₁ identify₂) (reassemble totalProjection)
      (coproductMap-isEquiv identify₁ identify₂ identify₁-isEquiv identify₂-isEquiv)
      (reassemble-isEquiv totalProjection))
```
