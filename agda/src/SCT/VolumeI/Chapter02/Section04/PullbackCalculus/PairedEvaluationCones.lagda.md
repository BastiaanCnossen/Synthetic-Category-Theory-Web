# Evaluating a cone at two objects

Pairing the evaluations of a diagram cone keeps both matching witnesses.
For a mapped cone, this paired evaluation agrees with restriction of its
product cone along the pair of evaluation functors. This is a whole-cone
comparison, not merely an identification of the two leg functors.

The construction works for any diagram shape and two objects of that
shape. The interval endpoints will supply the hom-fiber application.
No pullback hypothesis is needed for this comparison. Pairing the two
single-evaluation cospan maps then gives an actual cospan map; the final
`cube` compares its image of the mapped cone with this restricted product
cone. Its matching squares use the specified `PairedSquares` construction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedEvaluationCones as Mapped
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P using (mappedCone)

open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
import SCT.VolumeI.Chapter01.Section06.Cospans.PairedMaps as PairedMaps
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCones as Evaluation

module EvaluationCospan {T C D E : CAT} (z₀ z₁ : Obj-abs T)
  (f : MAP C E) (g : MAP D E) where
  private
    module Eval₀ = Evaluation.EvaluationCone 𝒯 M ℱ P z₀ f g
      using (cospan; normalized-cone; module CoordinateEvaluation)
    module Eval₁ = Evaluation.EvaluationCone 𝒯 M ℱ P z₁ f g
      using (cospan; normalized-cone; module CoordinateEvaluation)
    module Paired = PairedMaps.Pair 𝒯 P Eval₀.cospan Eval₁.cospan using (cospan; comparison)
    module Product = Products.Coordinates 𝒯 f f g g using (module Paired; paired-iso)

  cospan : CospanMap (funPost {C = T} f) (funPost g) (productMap f f) (productMap g g)
  cospan = Paired.cospan

  comparison : {X : CAT} (q : Cone (funPost {C = T} f) (funPost g) X) →
    ConeIso (CospanMap.mapCone cospan q)
      (Product.Paired.cone (Eval₀.CoordinateEvaluation.read q) (Eval₁.CoordinateEvaluation.read q))
  comparison q = coneIso-compose
    (Product.paired-iso (Eval₀.normalized-cone q) (Eval₁.normalized-cone q))
    (Paired.comparison q)

module At {T C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (z₀ z₁ : Obj-abs T) (s : Cone f g S) where
  private
    module Product = Products.Coordinates 𝒯 f f g g
      using (module Paired; paired-iso; paired-pre)
    module Eval₀ = Mapped.MappedAt 𝒯 M ℱ P z₀ s using (module Evaluated; comparison)
    module Eval₁ = Mapped.MappedAt 𝒯 M ℱ P z₁ s using (module Evaluated; comparison)

  evaluations : MAP (Fun T S) (S × S)
  evaluations = pair (evaluate z₀) (evaluate z₁)

  product-cone : Cone (productMap f f) (productMap g g) (S × S)
  product-cone = Product.Paired.cone (conePre pr₁ s) (conePre pr₂ s)

  evaluated-cone : Cone (productMap f f) (productMap g g) (Fun T S)
  evaluated-cone = Product.Paired.cone Eval₀.Evaluated.value Eval₁.Evaluated.value

  endpoint-cone : Cone (productMap f f) (productMap g g) (Fun T S)
  endpoint-cone = Product.Paired.cone (conePre (evaluate z₀) s) (conePre (evaluate z₁) s)

  evaluated-comparison : ConeIso evaluated-cone endpoint-cone
  evaluated-comparison = Product.paired-iso Eval₀.comparison Eval₁.comparison

  restriction-comparison : ConeIso (conePre evaluations product-cone) endpoint-cone
  restriction-comparison = coneIso-compose
    (Product.paired-iso
      (coneIso-compose (cone-action s (pair-β₁ (evaluate z₀) (evaluate z₁)))
        (conePre-assoc evaluations pr₁ s))
      (coneIso-compose (cone-action s (pair-β₂ (evaluate z₀) (evaluate z₁)))
        (conePre-assoc evaluations pr₂ s)))
    (Product.paired-pre evaluations (conePre pr₁ s) (conePre pr₂ s))

  comparison : ConeIso (conePre evaluations product-cone) evaluated-cone
  comparison = coneIso-compose (coneIso-inverse evaluated-comparison) restriction-comparison

  private
    module Endpoint = EvaluationCospan z₀ z₁ f g using (cospan; comparison)

  cospan = Endpoint.cospan

  cube : ConeIso (conePre evaluations product-cone) (CospanMap.mapCone cospan (mappedCone T s))
  cube = coneIso-compose (coneIso-inverse (Endpoint.comparison (mappedCone T s))) comparison
```
