# Product base change agrees with pullback base change

Compare both families with the lift of the same acted parameter cone.
On the product side, use reassociation and the product square. On the
chosen-pullback side, adjoin the parameter to the product comparison.
Both cone comparisons retain the prescribed right leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.ProductBaseChangeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductEvaluationFamilies 𝒯 M ℱ P using (module Evaluate)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.NativeProductBaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductParameterCones 𝒯 M ℱ P using () renaming (module Parameters to ProductParameters)
open import SCT.VolumeI.Chapter03.Section05.Currying.ParameterizedConeComparison 𝒯 M ℱ P using () renaming (module Parameters to PullbackParameters)
open import SCT.VolumeI.Chapter03.Section05.Currying.ActedConeRestriction 𝒯 M ℱ P using (module Restrict)

module Families {T S E K X : CAT} (r : MAP E (T × S)) (k : MAP K T)
  (u : FunctorOver (k ∘ pr₂ {C = X}) (Evaluation.projection r)) where
  module Ev = Evaluation r
  module Dk = Ev.F.Domain k
  module Product = Evaluate r k u
  module ProductCone = ProductParameters r k X
  module Actual = Change Ev.F.projection k Ev.projection
  module Pulled = PullbackParameters (pullbackCone k Ev.F.projection) Dk.square Dk.inclusion
    (pullbackLift-β Dk.square) (idIso _) X
  source = compose-over Ev.D.inclusion Product.argument
  target = compose-over (Actual.At.pulled u) (Pulled.Arg.family X)

  abstract
    product-comparison : FunctorOverIso source
      (lift-triangle (Action.value Ev.F.projection u ProductCone.target))
    product-comparison = compose-iso-over
      (Restrict.comparison u ProductCone.inner ProductCone.target Product.R.argument ProductCone.comparison (idIso _))
      (compose-iso-over (prewhisker-over Product.R.argument (BaseChange.comparison S u))
        (inverse-iso-over (associator-over Product.R.argument Product.C.U.value Ev.D.inclusion)))

    pullback-comparison : FunctorOverIso target
      (lift-triangle (Action.value Ev.F.projection u ProductCone.target))
    pullback-comparison = compose-iso-over
      (Restrict.comparison u Pulled.Ps.cone Pulled.Pt.cone (Pulled.Arg.family X) Pulled.comparison (idIso _))
      (prewhisker-over (Pulled.Arg.family X) (Actual.At.action-comparison u))

    comparison : FunctorOverIso source target
    comparison = compose-iso-over (inverse-iso-over pullback-comparison) product-comparison
```
