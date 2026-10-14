# Naming a transformation in the relative functor category

A transformation over the base determines an actual interval diagram in
the relative functor category. Its endpoints are the named relative
functors. Both endpoint identifications are constructed from comparisons
of complete relative triangles.

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

module SCT.VolumeI.Chapter03.RelativeCategories.NamedMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
import SCT.VolumeI.Chapter03.RelativeCategories.Functors as Functors
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagrams as Diagrams
import SCT.VolumeI.Chapter03.RelativeCategories.Families.IntervalParameters as Parameters
import SCT.VolumeI.Chapter03.RelativeCategories.Families.AbsolutePointFamilies as Points
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation as Evaluation

module Name {C D B : CAT} {p : MAP C B} {q : MAP D B} {u v : FunctorOver p q}
  (α : Over.MorphismOver p q u v) where
  module Native = Functors.Over 𝒯 M ℱ P p q
  module Diagram = Diagrams.Diagram 𝒯 M ℱ P I E S α
  module Parameter = Parameters.At 𝒯 M ℱ P I p

  family = compose-over Diagram.family Parameter.symmetry
  module Curried = Evaluation.Curry 𝒯 M ℱ P p q
    (FunctorLift.lift family) (FunctorLift.comparison family)

  module Endpoint (z : Obj-abs [1]) (w : FunctorOver p q)
    (ξ : FunctorOverIso (compose-over Diagram.family (Parameter.insertion z)) w) where
    module Point = Points.CurriedFamily 𝒯 M ℱ P p q family z
    module Swapped = Parameter.Endpoint z

    abstract
      relative-comparison : FunctorOverIso (Native.Decode.triangle (Curried.functor ∘ z)) w
      relative-comparison = compose-iso-over ξ
        (compose-iso-over (postwhisker-over Diagram.family Swapped.comparison)
          (compose-iso-over
            (associator-over Point.Evaluated.parameter Parameter.symmetry Diagram.family)
            Point.comparison))

      comparison : (Curried.functor ∘ z) =₁ Native.Name.object w
      comparison = Points.identify-objects 𝒯 M ℱ P p q relative-comparison ∙
        (Native.Decode.object-roundtrip (Curried.functor ∘ z)) ⁻¹

  module Source = Endpoint zero u Diagram.Source.comparison
  module Target = Endpoint one v Diagram.Target.comparison

  value : Morphism (Native.Name.object u) (Native.Name.object v)
  value = record
    { diagram = Curried.functor
    ; source-identification = Source.comparison
    ; target-identification = Target.comparison }
```
