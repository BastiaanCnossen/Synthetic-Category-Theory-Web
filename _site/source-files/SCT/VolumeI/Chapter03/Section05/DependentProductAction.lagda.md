# The induced functor between dependent products

For the construction in `con:Functoriality_Of_Dependent_Products`, compose
the source evaluation with the given functor over the base and relatively
curry. The computation below is an identification of relative mapping
points, so it retains the supplied triangle identification.

The identity and composition laws, with their triangles over the base,
are proved in `DependentProductActionLaws`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.DependentProductAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeTransposition 𝒯 M ℱ P using (module Transpose)

module Induced {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (u : FunctorOver f g) where
  source = DependentProduct.category ΠC
  target = DependentProduct.category ΠD
  source-projection = DependentProduct.projection ΠC
  target-projection = DependentProduct.projection ΠD

  evaluated : FunctorOver (pullback₂ {f = source-projection} {p}) g
  evaluated = compose-over u (DependentProduct.evaluation ΠC)

  module Curried = Transpose p g ΠD source-projection evaluated

  over : FunctorOver source-projection target-projection
  over = Curried.over

  functor : MAP source target
  functor = FunctorLift.lift over

  triangle : (target-projection ∘ functor) =₁ source-projection
  triangle = FunctorLift.comparison over

  uncurrying-comparison :
    (RelativeCurrying.At.uncurry p g ΠD source-projection ∘
      Over.name-over source-projection target-projection over) =₁
        Over.name-over (pullback₂ {f = source-projection} {p}) g evaluated
  uncurrying-comparison = Curried.comparison
```
