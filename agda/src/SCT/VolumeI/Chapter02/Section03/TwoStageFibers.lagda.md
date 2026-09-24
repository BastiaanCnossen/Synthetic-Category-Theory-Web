# Reordering the two inverse conditions

A triangle can first have its short edge fixed and then its long edge
made constant, or the two conditions can be imposed in the other order.
Two nested-pullback equivalences and symmetry give the comparison, with
an explicit equation for its projection to the original parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section03.TwoStageFibers
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
  using (pullback-swap; pullbackSwap; pullbackSwap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks 𝒯 P using (module Nested)
import SCT.VolumeI.Chapter01.Section06.UniversalNestedPullbacks as UniversalNested

module At {B A T E D : CAT} (f : MAP B A) (g : MAP T A) (h : MAP T E) (s : MAP D E) where
  Raw = Pullback f g
  J = Pullback h s
  triangle : MAP Raw T
  triangle = pullback₂
  base : MAP Raw B
  base = pullback₁
  forget : MAP J T
  forget = pullback₁
  Fiber = Pullback (h ∘ triangle) s
  one-sided = g ∘ forget

  private
    module First = Nested triangle h s
    module Last = UniversalNested.Nested 𝒯 P forget g f
      (coneSwap (pullbackCone f g))
      (pullback-swap (pullbackCone f g) (pullbackCone-isPullback f g))
    swap-pullback = pullbackSwap triangle forget
    middle = swap-pullback ∘ First.insert

  comparison : MAP Fiber (Pullback one-sided f)
  comparison = Last.flatten ∘ middle

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-compose middle Last.flatten
    (equiv-compose First.insert swap-pullback First.insert-isEquiv (pullbackSwap-isEquiv triangle forget))
    Last.flatten-isEquiv

  private
    middle-base : (Last.r ∘ middle) =₁ (pullback₁ {f = h ∘ triangle} {s})
    middle-base = pullbackLift-β₁ First.insertionCone ∙
      ((pullbackLift-β₂ (coneSwap (pullbackCone triangle forget)) ▷ First.insert) ∙
        (comp-assoc First.insert swap-pullback Last.r) ⁻¹)

  base-comparison : (pullback₂ ∘ comparison) =₁ (base ∘ pullback₁ {f = h ∘ triangle} {s})
  base-comparison = (base ◁ middle-base) ∙
    (comp-assoc middle Last.r base ∙
      ((pullbackLift-β₂ Last.flatCone ▷ middle) ∙ (comp-assoc middle Last.flatten pullback₂) ⁻¹))

  projection-isEquiv : IsEquiv (base ∘ pullback₁ {f = h ∘ triangle} {s}) →
    IsEquiv (pullback₂ {f = one-sided} {f})
  projection-isEquiv e = equiv-cancel-right comparison pullback₂ comparison-isEquiv
    (equiv-transport (base-comparison ⁻¹) e)
```
