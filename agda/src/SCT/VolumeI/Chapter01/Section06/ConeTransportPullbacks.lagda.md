# Transferring a pullback along a comparison of cones

Suppose a conversion preserves and reflects cone comparisons, and takes
cones induced from `s` to cones induced from `t` along an equivalence of
their vertices. If `t` is a pullback, so is `s`. Only the source vertex and
the pullback of the source cospan need be animae: these are the two
parameters used in the lifting criterion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeTransportPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P
  using (cone-isPullback-from-lifting)

module Transfer {C D E S C′ D′ E′ S′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (s : Cone f g S) (t : Cone f′ g′ S′) (u : MAP S S′) (eu : IsEquiv u)
  (convert : {X : CAT} → isAn X → Cone f g X → Cone f′ g′ X)
  (convert-iso : {X : CAT} (xAn : isAn X) {p q : Cone f g X} →
    ConeIso p q → ConeIso (convert xAn p) (convert xAn q))
  (convert-reflect : {X : CAT} (xAn : isAn X) (p q : Cone f g X) →
    ConeIso (convert xAn p) (convert xAn q) → ConeIso p q)
  (comparison : {X : CAT} (xAn : isAn X) (h : MAP X S) →
    ConeIso (convert xAn (conePre h s)) (conePre (u ∘ h) t))
  (target-isPullback : IsPullback t) where

  module Known = UniversalCone t target-isPullback

  module Factor {X : CAT} (xAn : isAn X) (p : Cone f g X) where
    factor = Known.factor (convert xAn p)
    chosen = equiv-lift eu factor
    lift = FunctorLift.lift chosen

    computation : ConeIso (conePre lift s) p
    computation = convert-reflect xAn _ _
      (coneIso-compose (Known.factor-β (convert xAn p))
        (coneIso-compose (cone-action t (FunctorLift.comparison chosen))
          (comparison xAn lift)))

  reflect : {X : CAT} (xAn : isAn X) (h k : MAP X S) →
    ConeIso (conePre h s) (conePre k s) → h =₁ k
  reflect xAn h k Φ = equiv-reflect eu h k
    (Known.reflect (u ∘ h) (u ∘ k)
      (coneIso-compose (comparison xAn k)
        (coneIso-compose (convert-iso xAn Φ) (coneIso-inverse (comparison xAn h)))))

  source-isPullback : isAn S → isAn (Pullback f g) → IsPullback s
  source-isPullback sAn pAn = cone-isPullback-from-lifting s
    (Factor.lift pAn (pullbackCone f g))
    (Factor.computation pAn (pullbackCone f g)) (reflect sAn)
```
