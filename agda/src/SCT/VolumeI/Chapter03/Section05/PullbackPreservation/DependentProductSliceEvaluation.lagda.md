# Evaluation for the sliced dependent product

The target is the pullback of C along evaluation of the target dependent
product. Evaluation of the source, together with its specified
naturality comparison, gives a map to that pullback. The cartesian
base-change square identifies its domain with the pullback required by
the sliced dependent-product definition.

This constructs the evaluation map and its native computation. Its
universal property is not assumed here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductSliceEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences 𝒯 M ℱ P using (module Inverse)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Squares 𝒯 M ℱ P using (module Cartesian)

module Evaluation {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (u : FunctorOver f g) where
  πC = DependentProduct.projection ΠC
  πD = DependentProduct.projection ΠD
  εC = DependentProduct.evaluation ΠC
  εD = DependentProduct.evaluation ΠD
  induced : FunctorOver πC πD
  induced = Induced.over p f g ΠC ΠD u
  induced-map = FunctorLift.lift induced
  QD = Pullback πD p
  q : MAP QD (DependentProduct.category ΠD)
  q = pullback₁
  changed = Change.functor p induced
  changed-map = FunctorLift.lift changed
  target = Pullback (FunctorLift.lift u) (FunctorLift.lift εD)
  target-projection : MAP target QD
  target-projection = pullback₂
  cone : Cone (FunctorLift.lift u) (FunctorLift.lift εD) (Pullback πC p)
  cone = record { left = FunctorLift.lift εC ; right = changed-map
    ; match = FunctorOverIso.underlying (Action.evaluation-comparison p f g ΠC ΠD u) ⁻¹ }
  native-evaluation : FunctorOver changed-map target-projection
  native-evaluation = record { lift = pullbackLift cone ; comparison = pullbackLift-β₂ cone }
  module Domain = Cartesian p induced using (square; square-isPullback)
  domain-comparison : FunctorOver changed-map (pullback₂ {f = induced-map} {q})
  domain-comparison = record { lift = pullbackLift Domain.square ; comparison = pullbackLift-β₂ Domain.square }
  module Reversed = Inverse domain-comparison Domain.square-isPullback using (inverse; left-inverse)
  evaluation : FunctorOver (pullback₂ {f = induced-map} {q}) target-projection
  evaluation = compose-over native-evaluation Reversed.inverse
  abstract
    native-comparison : FunctorOverIso (compose-over evaluation domain-comparison) native-evaluation
    native-comparison = compose-iso-over (right-unit-over native-evaluation)
      (compose-iso-over (postwhisker-over native-evaluation Reversed.left-inverse)
        (associator-over domain-comparison Reversed.inverse native-evaluation))
```
