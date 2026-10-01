# Indexed limits and colimits as adjoints

These records are exactly the adjoint-functor definition in
`def:Indexed_Limits_And_Colimits`, retaining the chosen unit, counit,
and triangle identities. They do not assert that pointwise choices of
limits or colimits assemble into such a functor.

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

module SCT.VolumeI.Deferred.LimitsAndColimits.IndexedAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public

record IndexedLimits (J C : CAT) : Set m where
  field
    limit : MAP (Fun J C) C
    adjunction : Adjunction (constantDiagram J C) limit

record IndexedColimits (J C : CAT) : Set m where
  field
    colimit : MAP (Fun J C) C
    adjunction : Adjunction colimit (constantDiagram J C)
```
