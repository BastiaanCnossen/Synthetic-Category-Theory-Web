# Exponentiability from dependent products after base change

The stability theorem supplies the Beck–Chevalley clause for any chosen
dependent products. Consequently, to construct an exponentiable functor
it suffices to supply dependent products after every base change. This
is a derived constructor for the manuscript's two-clause definition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ExponentiabilityCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P using (IsExponentiable)
open import SCT.VolumeI.Chapter03.Section05.DependentProductsBaseChange 𝒯 M ℱ P using (module BaseChange)

abstract
  from-dependent-products : {S T : CAT} (p : MAP S T) →
    ({S′ T′ : CAT} (b : MAP T′ T) (square : Cone p b S′) →
      IsPullback square → {C : CAT} (f : MAP C S′) → DependentProduct (Cone.right square) f) →
    IsExponentiable p
  from-dependent-products p products = record
    { over-base-change = products
    ; beck-chevalley = λ b first e₁ b′ second e₂ f Π Π′ →
        BaseChange.beck-chevalley-isEquiv (Cone.right first) b′ second e₂ f Π Π′ }
```
