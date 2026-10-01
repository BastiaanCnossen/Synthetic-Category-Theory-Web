# An opaque interface to composite adjunctions

Downstream relative constructions need the composite adjunction and its
unit and counit formulas, rather than its expanded triangle proofs. This
interface retains the formulas as explicit comparisons while sealing the
construction itself.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeInterface
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.CompositeAdjunctions as Absolute
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeComponents as Components

module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
  private
    module Core = Absolute.Composite 𝒯 M ℱ P I E S Q adjA adjB
      using (adjunction; unit-comparison; counit-comparison; unit-invertible; counit-invertible)
    module Data = Components.Composite 𝒯 M ℱ P I E S Q adjA adjB using (unit; counit)

  abstract
    adjunction : Adjunction (k ∘ l) (r ∘ s)
    adjunction = Core.adjunction

    unit-comparison : ExpressionIso (Adjunction.unit adjunction) Data.unit
    unit-comparison = Core.unit-comparison

    counit-comparison : ExpressionIso (Adjunction.counit adjunction) Data.counit
    counit-comparison = Core.counit-comparison

    unit-invertible : IsInvertibleExpression (Adjunction.unit adjA) →
      IsInvertibleExpression (Adjunction.unit adjB) → IsInvertibleExpression (Adjunction.unit adjunction)
    unit-invertible = Core.unit-invertible

    counit-invertible : IsInvertibleExpression (Adjunction.counit adjA) →
      IsInvertibleExpression (Adjunction.counit adjB) → IsInvertibleExpression (Adjunction.counit adjunction)
    counit-invertible = Core.counit-invertible
```
