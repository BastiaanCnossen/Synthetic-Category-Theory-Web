# Relative families out of a coproduct

Distribute the parameter across the coproduct, copair the two families,
and descend along the distributivity equivalence. Both restrictions
retain their triangles over the base. Comparisons on the two summands
likewise determine a comparison of the entire relative family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U using (module Distributivity)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Coproducts 𝒯 M ℱ P B using (module Sum)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences 𝒯 M ℱ P using (module Restriction)

module Families {C D E S : CAT} (p : MAP C S) (q : MAP D S) (r : MAP E S) (X : CAT) where
  module Domain = Sum p q using (projection; first; second)
  module Left = Argument Domain.first using (family)
  module Right = Argument Domain.second using (family)
  module Distributed = Sum (p ∘ pr₂ {C = X}) (q ∘ pr₂ {C = X}) using (projection; first; second; module Copair; module Compare)
  module Distribution = Distributed.Copair (Left.family X) (Right.family X)
    using (over; first-comparison; second-comparison)
  module Descend = Restriction (Domain.projection ∘ pr₂ {C = X}) r
    Distribution.over (Distributivity.distribute-isEquiv X C D) using (module Factor; module Reflect)

  module Copair (u : FunctorOver (p ∘ pr₂ {C = X}) r) (v : FunctorOver (q ∘ pr₂ {C = X}) r) where
    module Joined = Distributed.Copair u v using (over; first-comparison; second-comparison)
    module Lifted = Descend.Factor Joined.over using (value; comparison)
    value : FunctorOver (Domain.projection ∘ pr₂ {C = X}) r
    value = Lifted.value
    abstract
      first-comparison : FunctorOverIso (compose-over value (Left.family X)) u
      first-comparison = compose-iso-over Joined.first-comparison
        (compose-iso-over (prewhisker-over Distributed.first Lifted.comparison)
          (compose-iso-over (inverse-iso-over (associator-over Distributed.first Distribution.over value))
            (postwhisker-over value (inverse-iso-over Distribution.first-comparison))))
      second-comparison : FunctorOverIso (compose-over value (Right.family X)) v
      second-comparison = compose-iso-over Joined.second-comparison
        (compose-iso-over (prewhisker-over Distributed.second Lifted.comparison)
          (compose-iso-over (inverse-iso-over (associator-over Distributed.second Distribution.over value))
            (postwhisker-over value (inverse-iso-over Distribution.second-comparison))))

  module Compare (u v : FunctorOver (Domain.projection ∘ pr₂ {C = X}) r)
    (left : FunctorOverIso (compose-over u (Left.family X)) (compose-over v (Left.family X)))
    (right : FunctorOverIso (compose-over u (Right.family X)) (compose-over v (Right.family X))) where
    abstract
      first : FunctorOverIso (compose-over (compose-over u Distribution.over) Distributed.first)
        (compose-over (compose-over v Distribution.over) Distributed.first)
      first = compose-iso-over (inverse-iso-over (associator-over Distributed.first Distribution.over v))
        (compose-iso-over (postwhisker-over v (inverse-iso-over Distribution.first-comparison))
          (compose-iso-over left
            (compose-iso-over (postwhisker-over u Distribution.first-comparison)
              (associator-over Distributed.first Distribution.over u))))
      second : FunctorOverIso (compose-over (compose-over u Distribution.over) Distributed.second)
        (compose-over (compose-over v Distribution.over) Distributed.second)
      second = compose-iso-over (inverse-iso-over (associator-over Distributed.second Distribution.over v))
        (compose-iso-over (postwhisker-over v (inverse-iso-over Distribution.second-comparison))
          (compose-iso-over right
            (compose-iso-over (postwhisker-over u Distribution.second-comparison)
              (associator-over Distributed.second Distribution.over u))))
      comparison : FunctorOverIso u v
      comparison = Descend.Reflect.comparison u v
        (Distributed.Compare.comparison (compose-over u Distribution.over) (compose-over v Distribution.over) first second)
```
