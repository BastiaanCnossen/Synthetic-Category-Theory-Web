# Uncurrying whole cones

For every anima of parameters `X`, double uncurrying identifies cones over
`Map T (Fun K -)` with cones over `Map (T × K) -`. Both conversions act on
the specified matching, and their inverse comparisons are full `ConeIso`
data. No pullback structure or universality hypothesis is used here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.UncurryingCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M F
open import SCT.VolumeI.Chapter01.Section06.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.ConeUncurrying as MapUncurrying
import SCT.VolumeI.Chapter01.Section07.ConeUncurrying as FunUncurrying
import SCT.VolumeI.Chapter01.Section06.ConeCurrying as MapCurrying
import SCT.VolumeI.Chapter01.Section07.ConeCurrying as FunCurrying
import SCT.VolumeI.Chapter01.Section06.ConeReflection as MapReflection
import SCT.VolumeI.Chapter01.Section07.ConeReflection as FunReflection
open import SCT.VolumeI.Chapter01.Section07.MappingTests 𝒯 M F using (module Test)

private
  module MU = MapUncurrying 𝒯 M
  module FU = FunUncurrying 𝒯 M F
  module MR = MapReflection 𝒯 M
  module FR = FunReflection 𝒯 M F

module Transport {C D E : CAT} (T K : CAT) (f : MAP C E) (g : MAP D E) where

  TestCone : CAT → Set m
  TestCone X = Cone (mapPost {C = T} (funPost {C = K} f))
    (mapPost (funPost g)) X

  MappingCone : CAT → Set m
  MappingCone X = Cone (mapPost {C = T × K} f) (mapPost g) X

  raw : {X : CAT} → TestCone X → Cone f g (X × (T × K))
  raw {X} s = conePre (Associativity.backward X T K)
    (FU.uncurryCone (MU.uncurryCone s))

  raw-iso : {X : CAT} {s t : TestCone X} → ConeIso s t → ConeIso (raw s) (raw t)
  raw-iso {X} Φ = coneIso-pre (Associativity.backward X T K)
    (FU.uncurryConeIso (MU.uncurryConeIso Φ))

  raw-reflect : {X : CAT} (xAn : isAn X) (s t : TestCone X) →
    ConeIso (raw s) (raw t) → ConeIso s t
  raw-reflect {X} xAn s t Φ = MR.ReflectCone.comparison xAn s t
    (FR.ReflectCone.comparison (MU.uncurryCone s) (MU.uncurryCone t)
      (coneIso-compose (undo (FU.uncurryCone (MU.uncurryCone t)))
        (coneIso-compose (coneIso-pre (Associativity.forward X T K) Φ)
          (coneIso-inverse (undo (FU.uncurryCone (MU.uncurryCone s)))))))
    where
    undo : (q : Cone f g ((X × T) × K)) →
      ConeIso (conePre (Associativity.forward X T K)
        (conePre (Associativity.backward X T K) q)) q
    undo q = coneIso-compose (conePre-id q)
      (coneIso-compose (cone-action q (Associativity.backward-forward X T K))
        (conePre-assoc (Associativity.forward X T K) (Associativity.backward X T K) q))

  module Flatten {X : CAT} (xAn : isAn X) (s : TestCone X) where
    open MapCurrying.CurryCone 𝒯 M xAn (raw s) public

  module Inflate {X : CAT} (xAn : isAn X) (s : Cone f g (X × (T × K))) where
    module Inner = FunCurrying.CurryCone 𝒯 M F
      (conePre (Associativity.forward X T K) s)
    module Outer = MapCurrying.CurryCone 𝒯 M xAn Inner.value

    value : TestCone X
    value = Outer.value

    comparison : ConeIso (raw value) s
    comparison = coneIso-compose (conePre-id s)
      (coneIso-compose (cone-action s (Associativity.forward-backward X T K))
      (coneIso-compose (conePre-assoc (Associativity.backward X T K)
        (Associativity.forward X T K) s)
      (coneIso-compose (coneIso-pre (Associativity.backward X T K) Inner.comparison)
        (coneIso-pre (Associativity.backward X T K) (FU.uncurryConeIso Outer.comparison)))))
```

## The corner equivalences and the transported matching

The forward cone has exactly the legs obtained by composing with the
uncurrying equivalences at `C` and `D`. Its matching is the curried original
matching, transported along the displayed endpoint comparisons. Thus the
choice of matching is explicit, not an arbitrary commutative square on
the same four arrows.

```agda
  module Forward {X : CAT} (xAn : isAn X) (s : TestCone X) where
    module Curried = Flatten xAn s
    left = Test.forward T K C ∘ Cone.left s
    right = Test.forward T K D ∘ Cone.right s

    left-comparison : Cone.left Curried.value =₁ left
    left-comparison = mapReflect xAn _ _
      ((Test.represents T K C (Cone.left s)) ⁻¹ ∙ Curried.left-β)

    right-comparison : Cone.right Curried.value =₁ right
    right-comparison = mapReflect xAn _ _
      ((Test.represents T K D (Cone.right s)) ⁻¹ ∙ Curried.right-β)

    value : MappingCone X
    value = coneRetarget Curried.value left right left-comparison right-comparison

    retarget : ConeIso Curried.value value
    retarget = coneRetarget-β Curried.value left right left-comparison right-comparison

    evaluation : ConeIso (MU.uncurryCone value) (raw s)
    evaluation = coneIso-compose Curried.comparison
      (MU.uncurryConeIso (coneIso-inverse retarget))

  forward : {X : CAT} → isAn X → TestCone X → MappingCone X
  forward = Forward.value

  backward : {X : CAT} → isAn X → MappingCone X → TestCone X
  backward xAn s = Inflate.value xAn (MU.uncurryCone s)

  forward-iso : {X : CAT} (xAn : isAn X) {s t : TestCone X} →
    ConeIso s t → ConeIso (forward xAn s) (forward xAn t)
  forward-iso xAn {s} {t} Φ = MR.ReflectCone.comparison xAn _ _
    (coneIso-compose (coneIso-inverse (Forward.evaluation xAn t))
      (coneIso-compose (raw-iso Φ) (Forward.evaluation xAn s)))

  forward-reflect : {X : CAT} (xAn : isAn X) (s t : TestCone X) →
    ConeIso (forward xAn s) (forward xAn t) → ConeIso s t
  forward-reflect xAn s t Φ = raw-reflect xAn s t
    (coneIso-compose (Forward.evaluation xAn t)
      (coneIso-compose (MU.uncurryConeIso Φ) (coneIso-inverse (Forward.evaluation xAn s))))

  backward-iso : {X : CAT} (xAn : isAn X) {s t : MappingCone X} →
    ConeIso s t → ConeIso (backward xAn s) (backward xAn t)
  backward-iso xAn {s} {t} Φ = raw-reflect xAn _ _
    (coneIso-compose (coneIso-inverse (Inflate.comparison xAn (MU.uncurryCone t)))
      (coneIso-compose (MU.uncurryConeIso Φ) (Inflate.comparison xAn (MU.uncurryCone s))))

  forward-backward : {X : CAT} (xAn : isAn X) (s : MappingCone X) →
    ConeIso (forward xAn (backward xAn s)) s
  forward-backward xAn s = MR.ReflectCone.comparison xAn _ _
    (coneIso-compose (Inflate.comparison xAn (MU.uncurryCone s))
      (Forward.evaluation xAn (backward xAn s)))

  backward-forward : {X : CAT} (xAn : isAn X) (s : TestCone X) →
    ConeIso (backward xAn (forward xAn s)) s
  backward-forward xAn s = raw-reflect xAn _ _
    (coneIso-compose (Forward.evaluation xAn s)
      (Inflate.comparison xAn (MU.uncurryCone (forward xAn s))))
```
