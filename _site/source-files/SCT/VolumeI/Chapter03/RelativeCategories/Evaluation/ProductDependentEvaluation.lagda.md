# Evaluation for a dependent product along a projection

For a category over `T × S`, take the pullback of its functor category
along the family of fibers of `T × S → T`. Uncurrying the specified
pullback identification gives evaluation over `T × S`. The product
square identifies its domain with the chosen pullback domain required
in the definition of a dependent product.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences 𝒯 M ℱ P using (module Inverse)

module Fibers (T S : CAT) where
  projection : MAP (T × S) T
  projection = pr₁
  name : MAP T (Fun S (T × S))
  name = funCurry (id (T × S))

  uncurry-name : {K : CAT} (k : MAP K T) →
    funUncurry (name ∘ k) =₁ productMap k (id S)
  uncurry-name k = (comp-unitˡ (productMap k (id S)) ∙
    (funCurry-β (id (T × S)) ▷ productMap k (id S))) ∙ funUncurry-restrict name k

  module Domain {K : CAT} (k : MAP K T) where
    square = FirstFactor.square k S
    structure = productMap k (id S)
    chosen : MAP (Pullback k projection) (T × S)
    chosen = pullback₂
    inclusion : FunctorOver structure chosen
    inclusion = record { lift = pullbackLift square ; comparison = ConeIso.rightIso (pullbackLift-β square) }
    abstract
      inclusion-isEquiv : IsEquiv (FunctorLift.lift inclusion)
      inclusion-isEquiv = FirstFactor.square-isPullback k S
    module Back = Inverse inclusion inclusion-isEquiv

module Evaluation {T S E : CAT} (r : MAP E (T × S)) where
  module F = Fibers T S
  category = Pullback (funPost r) F.name
  projection : MAP category T
  projection = pullback₂
  sections : MAP category (Fun S E)
  sections = pullback₁
  module D = F.Domain projection

  product-evaluation : FunctorOver D.structure r
  product-evaluation = record
    { lift = funUncurry sections
    ; comparison = F.uncurry-name projection ∙
        (funUncurryIso (pullbackMatch {f = funPost r} {F.name}) ∙ (funPost-uncurry r sections) ⁻¹) }

  evaluation : FunctorOver D.chosen r
  evaluation = compose-over product-evaluation D.Back.inverse

  abstract
    product-comparison : FunctorOverIso (compose-over evaluation D.inclusion) product-evaluation
    product-comparison = compose-iso-over (right-unit-over product-evaluation)
      (compose-iso-over (postwhisker-over product-evaluation D.Back.left-inverse)
        (associator-over D.inclusion D.Back.inverse product-evaluation))
```
