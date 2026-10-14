# Decoding a morphism of the relative functor category

The universal relative family turns an interval diagram in `FunOver`
into a transformation over the base. Endpoint identifications are
decoded as comparisons of complete relative triangles. This provides
the reverse construction to naming; inverse laws are separate.

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

module SCT.VolumeI.Chapter03.RelativeCategories.DecodedMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
import SCT.VolumeI.Chapter03.RelativeCategories.Functors as Functors
import SCT.VolumeI.Chapter03.RelativeCategories.DiagramMorphisms as Morphisms
import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families as Families
import SCT.VolumeI.Chapter03.RelativeCategories.Families.IntervalParameters as Parameters
import SCT.VolumeI.Chapter03.RelativeCategories.Families.AbsolutePointFamilies as Points

module Decode {C D B : CAT} {p : MAP C B} {q : MAP D B} {u v : FunctorOver p q}
  (α : Morphism (Functors.Over.Name.object 𝒯 M ℱ P p q u)
    (Functors.Over.Name.object 𝒯 M ℱ P p q v)) where
  module A = Morphism α
  module Native = Functors.Over 𝒯 M ℱ P p q
  module Parameter = Parameters.At 𝒯 M ℱ P I p

  evaluated = Families.family 𝒯 M ℱ P p q A.diagram
  family = compose-over evaluated Parameter.inverse-symmetry

  module Endpoint (z : Obj-abs [1]) (w : FunctorOver p q)
    (δ : (A.diagram ∘ z) =₁ Native.Name.object w) where
    module Point = Points.Family 𝒯 M ℱ P p q A.diagram z
    module Swapped = Parameter.Endpoint z

    abstract
      comparison : FunctorOverIso (compose-over family (Parameter.insertion z)) w
      comparison = compose-iso-over (Points.decoded-name 𝒯 M ℱ P p q w)
        (compose-iso-over (Points.decode-identification 𝒯 M ℱ P p q δ)
          (compose-iso-over (inverse-iso-over Point.comparison)
            (compose-iso-over (postwhisker-over evaluated Swapped.reverse-comparison)
              (associator-over (Parameter.insertion z) Parameter.inverse-symmetry evaluated))))

  module Source = Endpoint zero u A.source-identification
  module Target = Endpoint one v A.target-identification
  module Decoded = Morphisms.FromDiagram.WithEndpoints 𝒯 M ℱ P I E S family u v
    Source.comparison Target.comparison

  value : Over.MorphismOver p q u v
  value = Decoded.value
```
