# Functoriality of dependent products

The induced functor is characterized by its evaluation comparison.
Uncurrying its identity and composition laws reduces them to the unit
and associativity laws for functors over the base. Reflection through
relative currying then proves the desired identifications over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)

module Action {S T : CAT} (p : MAP S T) where
  abstract
    evaluation-comparison : {C D : CAT} (f : MAP C S) (g : MAP D S)
      (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (u : FunctorOver f g) →
      FunctorOverIso (Currying.evaluate p g ΠD (Induced.over p f g ΠC ΠD u))
        (compose-over u (DependentProduct.evaluation ΠC))
    evaluation-comparison f g ΠC ΠD u = Currying.Native.factor-β p g ΠD
      (DependentProduct.projection ΠC) (compose-over u (DependentProduct.evaluation ΠC))

    identity : {C : CAT} (f : MAP C S) (Π : DependentProduct p f) →
      FunctorOverIso (Induced.over p f f Π Π (identity-over f))
        (identity-over (DependentProduct.projection Π))
    identity f Π = Currying.Native.reflect p f Π (DependentProduct.projection Π)
      (Induced.over p f f Π Π (identity-over f)) (identity-over (DependentProduct.projection Π))
      (compose-iso-over (inverse-iso-over (Currying.Native.evaluate-identity p f Π))
        (compose-iso-over (left-unit-over (DependentProduct.evaluation Π))
          (evaluation-comparison f f Π Π (identity-over f))))

  module Composite {B C D : CAT} (f : MAP B S) (g : MAP C S) (h : MAP D S)
    (ΠB : DependentProduct p f) (ΠC : DependentProduct p g) (ΠD : DependentProduct p h)
    (u : FunctorOver f g) (v : FunctorOver g h) where
    iu = Induced.over p f g ΠB ΠC u
    iv = Induced.over p g h ΠC ΠD v
    ivu = Induced.over p f h ΠB ΠD (compose-over v u)
    εB = DependentProduct.evaluation ΠB
    εC = DependentProduct.evaluation ΠC
    module D = Currying.Native p h ΠD

    abstract
      comparison : FunctorOverIso (compose-over iv iu) ivu
      comparison = D.reflect (DependentProduct.projection ΠB) (compose-over iv iu) ivu
        (compose-iso-over (inverse-iso-over (evaluation-comparison f h ΠB ΠD (compose-over v u)))
          (compose-iso-over (inverse-iso-over (associator-over εB u v))
            (compose-iso-over (postwhisker-over v (evaluation-comparison f g ΠB ΠC u))
              (compose-iso-over (associator-over (Change.functor p iu) εC v)
                (compose-iso-over (prewhisker-over (Change.functor p iu) (evaluation-comparison g h ΠC ΠD v))
                  (D.evaluate-composite iu iv))))))
```
