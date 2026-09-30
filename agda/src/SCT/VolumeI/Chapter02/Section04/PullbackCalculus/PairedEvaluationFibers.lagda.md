# Fibers of paired evaluation over a pullback

Functor categories and products preserve a pullback square. The specified
paired-evaluation cube therefore identifies every fiber of the paired
evaluation functor with a pullback of its component fibers. The family
may have an arbitrary common parameter category.

The component diagram here uses the canonical representation of the
product pullback. Comparison with the literal endpoint families and the
selected hom-post functors is a further calculation; the theorem below
does not silently identify those choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (mappedCone; fun-preserves-pullback)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductPullbacks as Products
import SCT.VolumeI.Chapter01.Section06.Cospans.PullbackCubeFibers as Fibers
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationCones as Evaluation

module Over {T C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (z₀ z₁ : Obj-abs T) (s : Cone f g S) (es : IsPullback s) where
  private
    module Eval = Evaluation.At 𝒯 M ℱ P z₀ z₁ s
      using (evaluations; cospan; product-cone; cube)
    module Product = Products.Product 𝒯 P s s es es using (square-isPullback)
    module Cube = Fibers.Cube 𝒯 P Eval.cospan (mappedCone T s)
      Eval.product-cone Eval.evaluations Eval.cube using (module At)

  module At {Γ : CAT} (x : MAP Γ (S × S)) where
    private
      module Fiber = Cube.At x using (module Universal; family-computation; represented-family; left-family; right-family; base-family; matching; left-fiber; right-fiber; base-fiber; left-map; right-map)
      module Universal = Fiber.Universal (fun-preserves-pullback T s es) Product.square-isPullback
        using (cone; isPullback; to-component-pullback; to-component-pullback-isEquiv; fiber-computation)
    open Universal public using (cone; isPullback; to-component-pullback; to-component-pullback-isEquiv; fiber-computation)
    open Fiber public using (family-computation; represented-family;
      left-family; right-family; base-family; matching; left-fiber; right-fiber; base-fiber; left-map; right-map)
```
