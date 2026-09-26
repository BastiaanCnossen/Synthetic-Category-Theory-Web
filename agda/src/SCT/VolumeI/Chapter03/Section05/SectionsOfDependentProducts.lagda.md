# Sections of a dependent product

Uncurrying identifies sections of a dependent product with sections of
its input. Restriction along the unit pullback removes the chosen
pullback of the identity. Over the terminal base, a section is simply
an object of the total category, in category-parameterized families.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.SectionsOfDependentProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-unitʳ)
open import SCT.VolumeI.Chapter01.Section07.TerminalDomain 𝒯 M ℱ using (module TerminalContext)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.TerminalBase 𝒯 M ℱ P using (module OverOne)

module Sections {S T C : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) where
  g = DependentProduct.projection Π
  cone : Cone (id T) p S
  cone = record { left = p ; right = id S
    ; match = (comp-unitʳ p) ⁻¹ ∙ comp-unitˡ p }
  inclusion : FunctorOver (id S) (pullback₂ {f = id T} {p})
  inclusion = lift-triangle cone
  abstract
    inclusion-isEquiv : IsEquiv (FunctorLift.lift inclusion)
    inclusion-isEquiv = equiv-cancel-left (FunctorLift.lift inclusion) pullback₂
      (pullback-unitʳ p) (equiv-transport ((pullbackLift-β₂ cone) ⁻¹) (id-isEquiv S))
  module Uncurry = Uncurrying p f Π (id T)
  module Restrict = Precompose f inclusion
  functor : MAP (FunOver (id T) g) (FunOver (id S) f)
  functor = Restrict.functor ∘ Uncurry.functor
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose Uncurry.functor Restrict.functor Uncurry.functor-isEquiv
      (Restrict.Equivalence.functor-isEquiv inclusion-isEquiv)

module OverTerminal {C : CAT} (g : MAP C One) where
  functor : MAP (FunOver (id One) g) C
  functor = TerminalContext.backward C ∘ Over.forget (id One) g
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (Over.forget (id One) g) (TerminalContext.backward C)
      (OverOne.forget-isEquiv (id One) g) (TerminalContext.backward-isEquiv C)

module Global {S C : CAT} (f : MAP C S) (Π : DependentProduct (terminate S) f) where
  g = DependentProduct.projection Π
  module Source = OverTerminal g
  module Target = Sections (terminate S) f Π
  functor : MAP (DependentProduct.category Π) (FunOver (id S) f)
  functor = Target.functor ∘ IsEquiv.inverse Source.functor-isEquiv
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose (IsEquiv.inverse Source.functor-isEquiv) Target.functor
      (equiv-inverse Source.functor-isEquiv) Target.functor-isEquiv
```
