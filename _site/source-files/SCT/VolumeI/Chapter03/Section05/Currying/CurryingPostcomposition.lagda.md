# Currying a postcomposed family

Currying commutes with postcomposition over the base. Both sides are
identified by evaluating the whole family, using its triangle beta rule.
This generic calculation keeps large constructed families out of the
proof of the coherence itself.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.CurryingPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module PostCurry {X B C D S : CAT} (f : MAP B S) {g : MAP C S} {h : MAP D S}
  (u : FunctorOver g h) (v : FunctorOver (f ∘ pr₂ {C = X}) g) where
  curried = Curry.functor f g (FunctorLift.lift v) (FunctorLift.comparison v)
  composed = compose-over u v
  result = Curry.functor f h (FunctorLift.lift composed) (FunctorLift.comparison composed)

  abstract
    family-comparison : FunctorOverIso (family f h (Postcompose.functor f u ∘ curried)) composed
    family-comparison = compose-iso-over
      {v = compose-over u (family f g curried)}
      (postwhisker-over u {u = family f g curried} {v = v} (curried-beta f g v))
      (postcompose-family f u curried)

    comparison : (Postcompose.functor f u ∘ curried) =₁ result
    comparison = reflect-family f h (Postcompose.functor f u ∘ curried) result
      (compose-iso-over {v = composed}
        (inverse-iso-over {u = family f h result} {v = composed} (curried-beta f h composed))
        family-comparison)

  maps : MAP (Map One X) (MapOver f h)
  maps = Postcompose.maps f u ∘ mapPost {C = One} curried

  abstract
    maps-comparison : maps =₁ mapPost {C = One} result
    maps-comparison = mapPost-cong {C = One} comparison ∙
      (mapPost-comp {A = One} curried (Postcompose.functor f u) ∙
        (Postcompose.maps-as-core f u ▷ mapPost {C = One} curried))

abstract
  compare-curry-via : {X B D S : CAT} (f : MAP B S) (g : MAP D S)
    (F : MAP X (FunOver f g)) (v w : FunctorOver (f ∘ pr₂ {C = X}) g) →
    FunctorOverIso (family f g F) w → FunctorOverIso v w →
    F =₁ Curry.functor f g (FunctorLift.lift v) (FunctorLift.comparison v)
  compare-curry-via f g F v w Φ Ψ = reflect-family f g F
    (Curry.functor f g (FunctorLift.lift v) (FunctorLift.comparison v))
    (compose-iso-over {v = v} (inverse-iso-over (curried-beta f g v))
      (compose-iso-over {v = w} (inverse-iso-over Ψ) Φ))
```
