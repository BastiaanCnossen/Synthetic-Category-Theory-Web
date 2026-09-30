# Hom families over a pullback

Specialize the paired-evaluation fiber theorem to the interval endpoints.
Its source fiber is literally the hom category of the pullback vertex.
The three canonically represented component families are identified with
the usual pairs of projected endpoints. These identifications give
equivalences from the component fibers to the corresponding hom categories,
with their whole endpoint-cone computations.

This identifies the objects of the component diagram. Identifying its
maps with the specified hom-post functors, and comparing the matching of
the resulting hom square, are separate obligations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.PullbackFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationFibers as Fibers
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as Families

module At {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (es : IsPullback s) (x y : Obj-abs S) where
  p = Cone.left s
  q = Cone.right s
  private
    module Evaluations = Fibers.Over 𝒯 M ℱ P zero one s es using (module At)
    module Fiber = Evaluations.At (pair x y)
      using (family-computation; left-family; right-family; base-family; matching;
        left-fiber; right-fiber; base-fiber; left-map; right-map; cone; isPullback)

  open Fiber public using (family-computation; left-family; right-family; base-family; matching;
    left-fiber; right-fiber; base-fiber; left-map; right-map)

  left-family-identification : left-family =₁ pair (p ∘ x) (p ∘ y)
  left-family-identification = productMap-pair p p x y ∙ ConeIso.leftIso Fiber.family-computation
  right-family-identification : right-family =₁ pair (q ∘ x) (q ∘ y)
  right-family-identification = productMap-pair q q x y ∙ ConeIso.rightIso Fiber.family-computation
  base-family-identification : base-family =₁ pair (f ∘ (p ∘ x)) (f ∘ (p ∘ y))
  base-family-identification = productMap-pair f f (p ∘ x) (p ∘ y) ∙
    (productMap f f ◁ left-family-identification)

  private
    module Left = Families.ChangeFamily 𝒯 M ℱ P I left-family-identification
      using (map; map-isEquiv; map-β)
    module Right = Families.ChangeFamily 𝒯 M ℱ P I right-family-identification
      using (map; map-isEquiv; map-β)
    module Base = Families.ChangeFamily 𝒯 M ℱ P I base-family-identification
      using (map; map-isEquiv; map-β)

  left-equivalence : MAP left-fiber (Hom C (p ∘ x) (p ∘ y))
  left-equivalence = Left.map
  left-equivalence-isEquiv : IsEquiv left-equivalence
  left-equivalence-isEquiv = Left.map-isEquiv
  open Left public using () renaming (map-β to left-equivalence-computation)

  right-equivalence : MAP right-fiber (Hom D (q ∘ x) (q ∘ y))
  right-equivalence = Right.map
  right-equivalence-isEquiv : IsEquiv right-equivalence
  right-equivalence-isEquiv = Right.map-isEquiv
  open Right public using () renaming (map-β to right-equivalence-computation)

  base-equivalence : MAP base-fiber (Hom E (f ∘ (p ∘ x)) (f ∘ (p ∘ y)))
  base-equivalence = Base.map
  base-equivalence-isEquiv : IsEquiv base-equivalence
  base-equivalence-isEquiv = Base.map-isEquiv
  open Base public using () renaming (map-β to base-equivalence-computation)

  fiber-cone : Cone left-map right-map (Hom S x y)
  fiber-cone = Fiber.cone
  fiber-cone-isPullback : IsPullback fiber-cone
  fiber-cone-isPullback = Fiber.isPullback
```
