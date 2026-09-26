# Global sections of an internal functor category

For `prop:map_to_the_point_is exponentiable`, apply the section comparison
first to the terminal dependent product and then to the dependent product
defining the internal functor category. The pullback-target comparison
identifies the remaining sections with functors over the original base.
The canonical equivalence in the manuscript is the inverse of evaluation.
Taking cores proves `cor:map_to_the_point_is exponentiable`.

Over the terminal base, the same construction identifies the internal
functor category with the ordinary functor category. This supplies the
terminal-base case needed for the fiber statement.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorSections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P using (IsExponentiable)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.InternalFunctors 𝒯 M ℱ P using (module FunctorCategory)
open import SCT.VolumeI.Chapter03.Section05.SectionsOfDependentProducts 𝒯 M ℱ P using (module Sections; module OverTerminal; module Global)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.TerminalBase 𝒯 M ℱ P using (module OverOne)
open import SCT.VolumeI.Chapter03.Section05.TerminalExponentiability 𝒯 M ℱ P using (module Terminal)

module InternalSections {C D S : CAT} (p : MAP C S) (q : MAP D S) (ep : IsExponentiable p) where
  module Internal = FunctorCategory p q ep
  module Product = Sections p (pullback₂ {f = q} {p}) Internal.product
  module Target = PullbackTarget p q (id C)
  module Unit = Change (comp-unitʳ p) q
  functor : MAP (FunOver (id S) Internal.projection) (FunOver p q)
  functor = Unit.functor ∘ (Target.functor ∘ Product.functor)
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (Target.functor ∘ Product.functor) Unit.functor
      (equiv-compose Product.functor Target.functor Product.functor-isEquiv Target.functor-isEquiv)
      Unit.functor-isEquiv

module GlobalSections {C D S : CAT} (p : MAP C S) (q : MAP D S) (ep : IsExponentiable p) where
  module Internal = FunctorCategory p q ep
  product = Terminal.dependent-product S Internal.projection
  category = DependentProduct.category product
  module First = Global Internal.projection product
  module Second = InternalSections p q ep
  evaluation : MAP category (FunOver p q)
  evaluation = Second.functor ∘ First.functor
  abstract
    evaluation-isEquiv : IsEquiv evaluation
    evaluation-isEquiv = equiv-compose First.functor Second.functor First.functor-isEquiv Second.functor-isEquiv
  comparison : MAP (FunOver p q) category
  comparison = IsEquiv.inverse evaluation-isEquiv
  abstract
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-inverse evaluation-isEquiv
  maps : MAP (MapOver p q) (Core category)
  maps = mapPost comparison
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv comparison comparison-isEquiv

module TerminalBase {C D : CAT} (p : MAP C One) (q : MAP D One) (ep : IsExponentiable p) where
  module Internal = FunctorCategory p q ep
  module First = OverTerminal Internal.projection
  module Second = InternalSections p q ep
  functor : MAP Internal.category (Fun C D)
  functor = Over.forget p q ∘ (Second.functor ∘ IsEquiv.inverse First.functor-isEquiv)
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (Second.functor ∘ IsEquiv.inverse First.functor-isEquiv) (Over.forget p q)
      (equiv-compose (IsEquiv.inverse First.functor-isEquiv) Second.functor
        (equiv-inverse First.functor-isEquiv) Second.functor-isEquiv)
      (OverOne.forget-isEquiv p q)
```
