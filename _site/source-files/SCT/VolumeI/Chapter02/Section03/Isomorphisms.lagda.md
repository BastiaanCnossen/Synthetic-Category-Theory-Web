# Isomorphisms and their category

The two inverse triangles in `def:Isomorphism` retain all their vertex
identifications. The definition allows different left and right inverses.

The category `Iso C` below is the iterated pullback of `def:Iso_C`:
first identify the common edge of the two triangles, then identify their
long edges with the two identity arrows, in reversed order.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.Isomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.CompositeWitnesses 𝒯 M ℱ P I E public
open Laws.PullbackStructure P

record IsInvertible {C : CAT} {x y : Obj-abs C} (f : Morphism x y) : Set m where
  field
    right-inverse : Morphism y x
    left-inverse : Morphism y x
    right-inverse-triangle : CompositeWitness right-inverse f (identity-morphism y)
    left-inverse-triangle : CompositeWitness f left-inverse (identity-morphism x)

InverseTriangles : CAT → CAT
InverseTriangles C = Pullback (edge₀ {C}) edge₂

inverseLongEdges : (C : CAT) → MAP (InverseTriangles C) (Ar C × Ar C)
inverseLongEdges C = pair (edge₁ ∘ pullback₁) (edge₁ ∘ pullback₂)

inverseIdentityEdges : (C : CAT) → MAP (C × C) (Ar C × Ar C)
inverseIdentityEdges C = pair (identityArrow ∘ pr₂) (identityArrow ∘ pr₁)

Iso : CAT → CAT
Iso C = Pullback (inverseLongEdges C) (inverseIdentityEdges C)

isoTriangles : {C : CAT} → MAP (Iso C) (InverseTriangles C)
isoTriangles = pullback₁

isoObjects : {C : CAT} → MAP (Iso C) (C × C)
isoObjects = pullback₂

isoArrow : {C : CAT} → MAP (Iso C) (Ar C)
isoArrow = (edge₀ ∘ pullback₁) ∘ isoTriangles

record IsoLift {Γ C : CAT} (f : MAP Γ (Ar C)) : Set m where
  field
    lift : MAP Γ (Iso C)
    comparison : (isoArrow ∘ lift) =₁ f
```
