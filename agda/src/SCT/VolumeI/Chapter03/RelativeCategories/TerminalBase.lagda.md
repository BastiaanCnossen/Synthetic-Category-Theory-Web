# Relative functors over the terminal category

Over the terminal base, forgetting the triangle recovers the ordinary
functor category. This is a supporting comparison for the absolute case
of `def:Relative_Functor_Category_Global_Sections`. It applies to any
specified structure functors into `One`.

The comparison is the actual first projection of the defining pullback.
Its equivalence follows because `Fun C One` is contractible. Passing to
cores gives the corresponding comparison of mapping animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.TerminalBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ
  using (fun-terminal-contractible; contractible-map)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module OverOne {C D : CAT} (f : MAP C One) (g : MAP D One) where
  abstract
    structure-point-isEquiv : IsEquiv (nameFun f)
    structure-point-isEquiv = contractible-map (nameFun f)
      (equiv-transport (terminal-iso _ _) (id-isEquiv One))
      (fun-terminal-contractible C)

    forget-isEquiv : IsEquiv (Over.forget f g)
    forget-isEquiv = pullback-equivalence (funPost g) (nameFun f) structure-point-isEquiv

  maps : MAP (MapOver f g) (Core (Fun C D))
  maps = mapPost (Over.forget f g)

  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv (Over.forget f g) forget-isEquiv
```
