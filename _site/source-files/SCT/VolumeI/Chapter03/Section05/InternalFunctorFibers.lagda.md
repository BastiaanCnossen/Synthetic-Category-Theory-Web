# Fibers of the internal functor category

For the final claim of `obs:Relative_Functor_Categories_Compatible_With_Pullback`,
base change to the specified absolute object. The internal functor
category over the terminal base is the ordinary functor category of
the two fibers. The first equivalence is the already constructed
base-change comparison, with its specified triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P using (IsExponentiable)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctors 𝒯 M ℱ P using (module FunctorCategory)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorsBaseChange 𝒯 M ℱ P using (module ChangeBase)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorSections 𝒯 M ℱ P using (module TerminalBase)

module Fiber {C D S : CAT} (p : MAP C S) (q : MAP D S)
  (ep : IsExponentiable p) (s : Obj-abs S) where
  module Changed = ChangeBase p q ep s
  module Ordinary = TerminalBase Changed.TargetData.p′ Changed.TargetData.q′ Changed.ep′
  module Internal = FunctorCategory p q ep
  category = Pullback Internal.projection s
  source-fiber = Pullback p s
  target-fiber = Pullback q s
  functor : MAP category (Fun source-fiber target-fiber)
  functor = Ordinary.functor ∘ IsEquiv.inverse Changed.functor-isEquiv
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (IsEquiv.inverse Changed.functor-isEquiv) Ordinary.functor
      (equiv-inverse Changed.functor-isEquiv) Ordinary.functor-isEquiv
```
