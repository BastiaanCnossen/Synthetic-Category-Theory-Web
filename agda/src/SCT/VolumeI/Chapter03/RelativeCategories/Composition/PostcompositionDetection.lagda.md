# Detecting an equivalence by relative postcomposition

It suffices to test relative mapping animae out of the source and target.
The target test lifts the identity and produces a right inverse over the
base. The source test reflects the resulting comparison and supplies the
left inverse. Forgetting the two triangles proves that the original
functor is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionDetection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P using (module Triangles)

module Test {K C D S : CAT} (k : MAP K S) {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) (equivalence : IsEquiv (Postcompose.maps k u)) where
  module Post = Postcompose k u using (maps; on-points-over; on-named-points)

  module Factor (w : FunctorOver k g) where
    chosen = equiv-lift equivalence (Over.name-over k g w)
    point = FunctorLift.lift chosen
    value = Over.decode-over k f point

    opaque
      comparison : FunctorOverIso (compose-over u value) w
      comparison = compose-iso-over (Triangles.decode-name-native k g w)
        (compose-iso-over
          (Triangles.decode-native-identification k g (FunctorLift.comparison chosen))
          (inverse-iso-over (Post.on-points-over point)))

  module Reflect (s t : FunctorOver k f) (Φ : FunctorOverIso (compose-over u s) (compose-over u t)) where
    opaque
      image : (Post.maps ∘ Over.name-over k f s) =₁ (Post.maps ∘ Over.name-over k f t)
      image = (Post.on-named-points t) ⁻¹ ∙
        (Triangles.Identification.identification k g (compose-over u s) (compose-over u t) Φ ∙
          Post.on-named-points s)

      comparison : FunctorOverIso s t
      comparison = Triangles.identify-native k f s t
        (equiv-reflect equivalence (Over.name-over k f s) (Over.name-over k f t) image)

module Detect {C D S : CAT} {f : MAP C S} {g : MAP D S} (u : FunctorOver f g)
  (source-test : IsEquiv (Postcompose.maps f u))
  (target-test : IsEquiv (Postcompose.maps g u)) where
  module Target = Test.Factor g u target-test (identity-over g) using (value; comparison)
  inverse : FunctorOver g f
  inverse = Target.value

  right-inverse : FunctorOverIso (compose-over u inverse) (identity-over g)
  right-inverse = Target.comparison

  opaque
    after-postcomposition : FunctorOverIso
      (compose-over u (compose-over inverse u)) (compose-over u (identity-over f))
    after-postcomposition = compose-iso-over (inverse-iso-over (right-unit-over u))
      (compose-iso-over (left-unit-over u)
        (compose-iso-over (prewhisker-over u right-inverse)
          (inverse-iso-over (associator-over u inverse u))))

    left-inverse : FunctorOverIso (compose-over inverse u) (identity-over f)
    left-inverse = Test.Reflect.comparison f u source-test
      (compose-over inverse u) (identity-over f) after-postcomposition

    isEquiv : IsEquiv (FunctorLift.lift u)
    isEquiv = record
      { inverse = FunctorLift.lift inverse
      ; sectionIso = (FunctorOverIso.underlying left-inverse) ⁻¹
      ; retractionIso = (FunctorOverIso.underlying right-inverse) ⁻¹ }

opaque
  detect : {C D S : CAT} {f : MAP C S} {g : MAP D S} (u : FunctorOver f g) →
    ({K : CAT} (k : MAP K S) → IsEquiv (Postcompose.maps k u)) → IsEquiv (FunctorLift.lift u)
  detect {f = f} {g} u tests = Detect.isEquiv u (tests f) (tests g)
```
