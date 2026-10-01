# Cone categories and uniqueness of limits

The pullbacks in `def:Indexed_Diagrams` are ordinary relative slices of
the constant-diagram functor. Limit and colimit cones are terminal and
initial objects of these categories. Their uniqueness follows directly
from absolute uniqueness of universal objects; no joined indexing shape
or full subcategory of universal objects is used.

The conclusions identify the supplied cone objects and their vertices.
They do not identify records including their universal-property proof
fields or construct an anima of all universal cones.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Deferred.LimitsAndColimits.ConeCategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I public
import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.UniversalObjects as Universal

module Diagram (J C : CAT) (F : Obj-abs (Fun J C)) where
  module Cones = RelativeSlice (constantDiagram J C) F
  module Cocones = RelativeCoslice (constantDiagram J C) F

  IsLimit : Obj-abs Cones.category → Set m
  IsLimit = IsTerminal

  IsColimit : Obj-abs Cocones.category → Set m
  IsColimit = IsInitial

  record Limit : Set m where
    field
      cone : Obj-abs Cones.category
      universal : IsLimit cone
    value : Obj-abs C
    value = Cones.projection ∘ cone

  record Colimit : Set m where
    field
      cocone : Obj-abs Cocones.category
      universal : IsColimit cocone
    value : Obj-abs C
    value = Cocones.projection ∘ cocone

  limit-cone-identification : (x y : Limit) → Limit.cone x =₁ Limit.cone y
  limit-cone-identification x y = Universal.TerminalObjects.identification 𝒯 M ℱ P I E S R
    (Limit.cone x) (Limit.cone y) (Limit.universal x) (Limit.universal y)

  colimit-cocone-identification : (x y : Colimit) → Colimit.cocone x =₁ Colimit.cocone y
  colimit-cocone-identification x y = Universal.InitialObjects.identification 𝒯 M ℱ P I E S R
    (Colimit.cocone x) (Colimit.cocone y) (Colimit.universal x) (Colimit.universal y)

  limit-identification : (x y : Limit) → Limit.value x =₁ Limit.value y
  limit-identification x y = Cones.projection ◁ limit-cone-identification x y

  colimit-identification : (x y : Colimit) → Colimit.value x =₁ Colimit.value y
  colimit-identification x y = Cocones.projection ◁ colimit-cocone-identification x y
```
