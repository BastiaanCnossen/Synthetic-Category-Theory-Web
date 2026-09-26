# Transposing a functor over the base

Relative currying acts on the whole triangle. After decoding the curried
point, naming the resulting triangle and uncurrying it recovers the
specified original point. The roundtrip theorem for `FunOver` retains
the matching identification in this assertion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.RelativeTransposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P

module Transpose {S T C E : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (t : MAP E T)
  (u : FunctorOver (pullback₂ {f = t} {p}) f) where
  g = DependentProduct.projection Π
  module Curry = RelativeCurrying.At p f Π t
  source-point = Over.name-over (pullback₂ {f = t} {p}) f u

  abstract
    point : Obj-abs (MapOver t g)
    point = Curry.curry ∘ source-point

    over : FunctorOver t g
    over = Over.decode-over t g point

    uncurrying-comparison : (Curry.uncurry ∘ point) =₁ source-point
    uncurrying-comparison = comp-unitˡ source-point ∙
      ((Curry.uncurry-curry ▷ source-point) ∙
        (comp-assoc source-point Curry.curry Curry.uncurry) ⁻¹)

    name-comparison : Over.name-over t g over =₁ point
    name-comparison = Over.name-decode-over t g point

    comparison : (Curry.uncurry ∘ Over.name-over t g over) =₁ source-point
    comparison = uncurrying-comparison ∙ (Curry.uncurry ◁ name-comparison)
```
