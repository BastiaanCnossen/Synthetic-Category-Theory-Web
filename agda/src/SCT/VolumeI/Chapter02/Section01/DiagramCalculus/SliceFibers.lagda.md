# Fibers of slice projections

Pullback pasting identifies the fiber of a slice projection with the
corresponding hom category. Consequently an initial or terminal object
has contractible hom categories in the indicated direction. No converse
or anima recognition is used here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionFibers as Fibers

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.SliceFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open Laws.PullbackStructure P

module FiberComparison {B C : CAT} (u v : MAP B C) (y : Obj-abs B)
  (x₀ x₁ : Obj-abs C) (α : (u ∘ y) =₁ x₀) (β : (v ∘ y) =₁ x₁) where
  module F = EndpointFiber u v
    using (base)
  comparison-on-base : (pair u v ∘ y) =₁ (pair x₀ x₁)
  comparison-on-base = pair-cong α β ∙ pair-pre u v y

  fiber-to-hom : MAP (Pullback F.base y) (Hom C x₀ x₁)
  fiber-to-hom = Fibers.Fiber.fiber-to-target 𝒯 P endpoints (pair u v) y (pair x₀ x₁) comparison-on-base

  fiber-to-hom-isEquiv : IsEquiv fiber-to-hom
  fiber-to-hom-isEquiv = Fibers.Fiber.fiber-to-target-isEquiv 𝒯 P endpoints (pair u v) y (pair x₀ x₁) comparison-on-base

  hom-contractible : IsEquiv F.base → IsContractible (Hom C x₀ x₁)
  hom-contractible = Fibers.Fiber.target-contractible 𝒯 P endpoints (pair u v) y (pair x₀ x₁) comparison-on-base
module TerminalFiber {C : CAT} (x y : Obj-abs C) =
  FiberComparison (id C) (const x) y y x (comp-unitˡ y) (const-One x ∙ const-pre x y)

module InitialFiber {C : CAT} (x y : Obj-abs C) =
  FiberComparison (const x) (id C) y x y (const-One x ∙ const-pre x y) (comp-unitˡ y)

terminal-hom-contractible : {C : CAT} (x : Obj-abs C) → IsTerminal x →
  (y : Obj-abs C) → IsContractible (Hom C y x)
terminal-hom-contractible x e y = TerminalFiber.hom-contractible x y e

initial-hom-contractible : {C : CAT} (x : Obj-abs C) → IsInitial x →
  (y : Obj-abs C) → IsContractible (Hom C x y)
initial-hom-contractible x e y = InitialFiber.hom-contractible x y e
```







