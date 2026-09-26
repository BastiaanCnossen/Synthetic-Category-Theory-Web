# Pulling back a relative family

Base change of a functor category applies this construction to its universal
family. The computations for arbitrary families use the same cone and lift.
Sharing this definition keeps their specified matching identification identical
without repeatedly expanding two independently written cone expressions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.PulledFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)

module Change {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  C′ = Pullback f p
  D′ = Pullback g p
  f′ : MAP C′ S
  f′ = pullback₂
  g′ : MAP D′ S
  g′ = pullback₂

  module At {X : CAT} (v : FunctorOver (f ∘ pr₂ {C = X}) g) where
    R : MAP (X × C′) (X × C)
    R = productMap (id X) (pullback₁ {f = f} {p})
    h = FunctorLift.lift v
    θ = FunctorLift.comparison v
    Z = comp-assoc (pr₂ {C = X}) f′ p
    d = pullbackMatch {f = f} {p} ▷ pr₂ {C = X}
    A = comp-assoc (pr₂ {C = X}) (pullback₁ {f = f} {p}) f
    b = f ◁ pair-β₂ (id X ∘ pr₁ {C = X} {D = C′}) (pullback₁ {f = f} {p} ∘ pr₂ {C = X} {D = C′})
    κ = comp-assoc R (pr₂ {C = X} {D = C}) f
    tail = (θ ▷ R) ∙ (comp-assoc R h g) ⁻¹

    cone : Cone g p (X × C′)
    cone = record { left = h ∘ R ; right = f′ ∘ pr₂
      ; match = Z ∙ (d ∙ ((A ⁻¹) ∙ (b ∙ (κ ∙ tail)))) }
    pulled : FunctorOver (f′ ∘ pr₂ {C = X}) g′
    pulled = record { lift = pullbackLift cone ; comparison = pullbackLift-β₂ cone }
```
