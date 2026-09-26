# Relative functors commute with pasting cones

Flattening a cone past a square commutes with its action by a functor
over the base. Indeed, flattening postcomposes the old triangle and then
adjoins the square's matching identification. Composition commutes with
these two operations by the already established native comparison laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConePasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P

module Pasting {S T S′ T′ : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone b p S′) where
  p′ = Cone.left square
  h = Cone.right square

  flatten-action : {K E X : CAT} {k : MAP K T′} {t : MAP E T′}
    (u : FunctorOver k t) (s : Cone k p′ X) →
    ConeIso (PasteCones.flatten t b square (Action.value p′ u s))
      (Action.value p (postbase b u) (PasteCones.flatten k b square s))
  flatten-action u s = triangle-cone-iso (h ∘ Cone.right s)
    (compose-iso-over
      (inverse-iso-over (compose-source-change (Cone.match (conePre (Cone.right s) square))
        (postbase b (cone-triangle s)) (postbase b u)))
      (change-source-iso (Cone.match (conePre (Cone.right s) square))
        (inverse-iso-over (postbase-composite b (cone-triangle s) u))))
```
