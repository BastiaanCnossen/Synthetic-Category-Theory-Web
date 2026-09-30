# The direct comparison of dependent products

For `lem:Dependent_Products_Preserve_Pullbacks`, assume that the dependent
product of the original pullback is already available, as it is when
the base functor is exponentiable. Apply dependent products to both
projections and to their specified matching. Lifting the resulting
relative cone gives the comparison in the manuscript.

This constructs the comparison and its two relative projection
identifications. Its equivalence property is a further claim; it is not
asserted here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductPullbackComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductActionIdentifications 𝒯 M ℱ P
  using (module Identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P
  using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackLifting 𝒯 M ℱ P using (module Lift)

module Direct {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (projection; first; second; match-over)
  iu = Induced.over p f h ΠC ΠE u
  iv = Induced.over p g h ΠD ΠE v
  module Q = RelativePullback iu iv using (category; projection; first; second)

  module WithProduct (ΠR : DependentProduct p R.projection) where
    first = Induced.over p R.projection f ΠR ΠC R.first
    second = Induced.over p R.projection g ΠR ΠD R.second

    opaque
      matching : FunctorOverIso (compose-over iu first) (compose-over iv second)
      matching = compose-iso-over
        (inverse-iso-over (Action.Composite.comparison p R.projection g h ΠR ΠD ΠE R.second v))
        (compose-iso-over
          (Identification.comparison p R.projection h ΠR ΠE R.match-over)
          (Action.Composite.comparison p R.projection f h ΠR ΠC ΠE R.first u))

    module Lifted = Lift iu iv first second matching
      using (over; cone; cone-comparison; first-comparison; second-comparison)

    over : FunctorOver (DependentProduct.projection ΠR) Q.projection
    over = Lifted.over

    functor : MAP (DependentProduct.category ΠR) Q.category
    functor = FunctorLift.lift over

    first-comparison : FunctorOverIso (compose-over Q.first over) first
    first-comparison = Lifted.first-comparison

    second-comparison : FunctorOverIso (compose-over Q.second over) second
    second-comparison = Lifted.second-comparison
```
