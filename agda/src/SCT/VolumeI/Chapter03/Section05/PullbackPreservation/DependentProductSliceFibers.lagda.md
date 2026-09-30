# Taking fibers of dependent uncurrying

Take the fiber of the uncurrying naturality square over a specified
functor to the target dependent product. Both horizontal arrows are
equivalences, and the image of that point is its native evaluation.
The nested-slice fiber comparison then identifies the two fibers with
functor categories over their respective targets.

This is the fiber equivalence for the sliced adjunction. Identifying
it with evaluation by a single sliced dependent product is a separate
step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductSliceFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingNaturality 𝒯 M ℱ P using (module Natural)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingPoints 𝒯 M ℱ P using (relative-point; module Points)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionFiber 𝒯 M ℱ P using (module At)

module Fiber {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (u : FunctorOver f g)
  (k : MAP K (DependentProduct.category ΠD)) where
  πC = DependentProduct.projection ΠC
  πD = DependentProduct.projection ΠD
  induced : FunctorOver πC πD
  induced = Induced.over p f g ΠC ΠD u
  t = πD ∘ k
  t′ : MAP (Pullback t p) S
  t′ = pullback₂
  x : FunctorOver t πD
  x = record { lift = k ; comparison = idIso t }
  evaluated : FunctorOver t′ g
  evaluated = Currying.evaluate p g ΠD x
  e = FunctorLift.lift evaluated
  module C = Uncurrying p f ΠC t using (functor; functor-isEquiv)
  module D = Uncurrying p g ΠD t using (functor; functor-isEquiv)
  module Before = Postcompose t induced using (functor)
  module After = Postcompose t′ u using (functor)
  point = relative-point t πD x
  target-point = relative-point t′ g evaluated
  module Source = At k induced t point (Over.named-forget t πD x)
    using (category; functor; functor-isEquiv; comparison)
  module Target = At e u t′ target-point (Over.named-forget t′ g evaluated)
    using (category; functor; functor-isEquiv; comparison)
  cospan : CospanMap Before.functor point After.functor target-point
  cospan = record
    { left = C.functor ; right = id One ; base = D.functor
    ; leftSquare = Natural.comparison p f g ΠC ΠD u t ⁻¹
    ; rightSquare = Points.comparison p g ΠD t x ⁻¹ ∙ comp-unitʳ target-point }
  module Changed = CospanMap cospan using (pullbackMap; pullbackMap-β)
  inverse-source : MAP (FunOver k (FunctorLift.lift induced)) Source.category
  inverse-source = IsEquiv.inverse Source.functor-isEquiv
  functor : MAP (FunOver k (FunctorLift.lift induced)) (FunOver e (FunctorLift.lift u))
  functor = Target.functor ∘ (Changed.pullbackMap ∘ inverse-source)
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (Changed.pullbackMap ∘ inverse-source) Target.functor
      (equiv-compose inverse-source Changed.pullbackMap (equiv-inverse Source.functor-isEquiv)
        (CospanEquivalence.pullbackMap-isEquiv cospan C.functor-isEquiv (id-isEquiv One) D.functor-isEquiv))
      Target.functor-isEquiv
  maps : MAP (MapOver k (FunctorLift.lift induced)) (MapOver e (FunctorLift.lift u))
  maps = mapPost functor
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
