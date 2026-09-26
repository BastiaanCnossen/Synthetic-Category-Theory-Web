# Diagrams constant over a base

The pullback of postcomposition along the constant-diagram functor
selects diagrams whose image in the base is constant, with a specified
identification. Evaluation at any specified object gives a functor over
the base. Taking the interval supplies the relative arrow category used
in the slice construction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section07.MappingCalculus.RelativeArrows
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)

module Diagrams {A S : CAT} (J : CAT) (r : MAP A S) where
  constant : MAP S (Fun J S)
  constant = funCurry pr₁
  category : CAT
  category = Pullback (funPost {C = J} r) constant
  projection : MAP category S
  projection = pullback₂
  diagrams : MAP category (Fun J A)
  diagrams = pullback₁
  evaluated : MAP (category × J) A
  evaluated = funUncurry diagrams
  abstract
    evaluation-triangle : (r ∘ evaluated) =₁ (projection ∘ pr₁)
    evaluation-triangle = pair-β₁ (projection ∘ pr₁) (id J ∘ pr₂) ∙
      ((funCurry-β (pr₁ {S} {J}) ▷ productMap projection (id J)) ∙
        (funUncurry-restrict constant projection ∙
          (funUncurryIso (pullbackMatch {f = funPost r} {constant}) ∙
            (funPost-uncurry r diagrams) ⁻¹)))

  module At (e : Obj-abs J) where
    insertion : MAP category (category × J)
    insertion = pair (id category) (const e)
    functor : MAP category A
    functor = evaluated ∘ insertion
    abstract
      triangle : (r ∘ functor) =₁ projection
      triangle = comp-unitʳ projection ∙
        ((projection ◁ pair-β₁ (id category) (const e)) ∙
          (comp-assoc insertion (pr₁ {category} {J}) projection ∙
            ((evaluation-triangle ▷ insertion) ∙
              (comp-assoc insertion evaluated r) ⁻¹)))
    over : FunctorOver projection r
    over = record { lift = functor ; comparison = triangle }
```
