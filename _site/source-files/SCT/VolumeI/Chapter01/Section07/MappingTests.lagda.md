# Testing functor-category comparisons on mapping animae

Uncurrying is an equivalence for every test category. Its compatibility
with postcomposition identifies the comparison functors used in the
constructor proofs on the whole mapping anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.MappingTests
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Evaluation 𝒯 M

module Test (T C D : CAT) where
  open Evaluation.At (funEval {C} {D}) T public
  forward-isEquiv : IsEquiv forward
  forward-isEquiv = funUniversal C D T

postcomposition : {C D E : CAT} (T : CAT) (f : MAP D E) →
  (Test.forward T C E ∘ mapPost (funPost f)) =₁
  (mapPost f ∘ Test.forward T C D)
postcomposition {C} {D} {E} T f = mapReflect (map-isAn T (Fun C D)) _ _
  ((mapPost-uncurry f (Test.forward T C D)) ⁻¹ ∙
  ((f ◁ mapCurry-β (map-isAn T (Fun C D)) (Test.evaluation T C D)) ⁻¹ ∙
  (comp-assoc r (funUncurry mapEval) f ∙
  ((funPost-uncurry f mapEval ▷ r) ∙
  ((funUncurry-cong (mapPost-β (funPost f)) ▷ r) ∙
    Test.represents T C E (mapPost (funPost f)))))))
  where r = Associativity.backward (Map T (Fun C D)) T C

mapPost-pair : {T A B C : CAT} (f : MAP A B) (g : MAP A C) →
  (pair (mapPost pr₁) (mapPost pr₂) ∘ mapPost {C = T} (pair f g)) =₁
  (pair (mapPost f) (mapPost g))
mapPost-pair f g = pair-cong
  (mapPost-cong (pair-β₁ f g) ∙ mapPost-comp (pair f g) pr₁)
  (mapPost-cong (pair-β₂ f g) ∙ mapPost-comp (pair f g) pr₂) ∙
  pair-pre (mapPost pr₁) (mapPost pr₂) (mapPost (pair f g))
```

Restriction in the domain commutes with uncurrying. The only additional
comparison is reassociation with a change in the last product factor.

```agda
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M
  using (productMap-pair; product-first; product-second)

last-regroup : {B C : CAT} (A T : CAT) (f : MAP B C) →
  (productMap (id (A × T)) f ∘ Associativity.backward A T B) =₁
  (Associativity.backward A T C ∘ productMap (id A) (productMap (id T) f))
last-regroup {B} {C} A T f = right-normal ⁻¹ ∙ left-normal
  where
  k = productMap (id A) (productMap (id T) f)
  p = pair pr₁ (pr₁ ∘ pr₂)
  first = comp-unitˡ pr₁ ∙ pair-β₁ (id A ∘ pr₁) (productMap (id T) f ∘ pr₂)
  second = comp-unitˡ (pr₁ ∘ pr₂) ∙
    (product-first (id T) f pr₂ ∙
    ((pr₁ ◁ pair-β₂ (id A ∘ pr₁) (productMap (id T) f ∘ pr₂)) ∙
      comp-assoc k pr₂ pr₁))
  third = product-second (id T) f pr₂ ∙
    ((pr₂ ◁ pair-β₂ (id A ∘ pr₁) (productMap (id T) f ∘ pr₂)) ∙
      comp-assoc k pr₂ pr₂)
  right-normal = pair-cong (pair-cong first second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) k)
    third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) k
  left-normal = pair-cong (comp-unitˡ p) (idIso (f ∘ (pr₂ ∘ pr₂))) ∙
    productMap-pair (id (A × T)) f p (pr₂ ∘ pr₂)

precomposition : {B C D : CAT} (T : CAT) (f : MAP B C) →
  (Test.forward T B D ∘ mapPost (funPre f)) =₁
  (mapPre (productMap (id T) f) ∘ Test.forward T C D)
precomposition {B} {C} {D} T f = mapReflect (map-isAn T (Fun C D)) _ _
  ((mapPre-uncurry (productMap (id T) f) (Test.forward T C D)) ⁻¹ ∙
  ((mapCurry-β (map-isAn T (Fun C D)) (Test.evaluation T C D) ▷ k) ⁻¹ ∙
  ((comp-assoc k (Associativity.backward A T C) (funUncurry mapEval)) ⁻¹ ∙
  ((funUncurry mapEval ◁ last-regroup A T f) ∙
  (comp-assoc r (productMap (id (A × T)) f) (funUncurry mapEval) ∙
  ((funPre-uncurry f mapEval ▷ r) ∙
  ((funUncurry-cong (mapPost-β (funPre f)) ▷ r) ∙
    Test.represents T B D (mapPost (funPre f)))))))))
  where
  A = Map T (Fun C D)
  r = Associativity.backward A T B
  k = productMap (id A) (productMap (id T) f)
```

The exponential comparison reassociates four factors. This identification
is proved by the four projections; it requires no additional coherence
axiom for product associators.

```agda
backward-pair : {R A B C : CAT} (x : MAP R A) (y : MAP R B) (z : MAP R C) →
  (Associativity.backward A B C ∘ pair x (pair y z)) =₁ (pair (pair x y) z)
backward-pair x y z = pair-cong
  (pair-cong (pair-β₁ x (pair y z))
    (pair-β₁ y z ∙ ((pr₁ ◁ pair-β₂ x (pair y z)) ∙ comp-assoc (pair x (pair y z)) pr₂ pr₁)) ∙
    pair-pre pr₁ (pr₁ ∘ pr₂) (pair x (pair y z)))
  (pair-β₂ y z ∙ ((pr₂ ◁ pair-β₂ x (pair y z)) ∙ comp-assoc (pair x (pair y z)) pr₂ pr₂)) ∙
  pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (pair x (pair y z))

fourfold-regroup : (A T X C : CAT) →
  (Associativity.backward (A × T) X C ∘ Associativity.backward A T (X × C)) =₁
  (productMap (Associativity.backward A T X) (id C) ∘
    (Associativity.backward A (T × X) C ∘ productMap (id A) (Associativity.backward T X C)))
fourfold-regroup A T X C = FunctorLift.lift
  (preWhisker-lift tuple tuple-isEquiv (right-normal ⁻¹ ∙ left-normal))
  where
  R = A × (T × (X × C))
  x : MAP R A
  x = pr₁
  y : MAP R T
  y = pr₁ ∘ pr₂
  z : MAP R X
  z = pr₁ ∘ (pr₂ ∘ pr₂)
  w : MAP R C
  w = pr₂ ∘ (pr₂ ∘ pr₂)
  tuple = pair x (pair y (pair z w))
  tuple-id : tuple =₁ (id R)
  tuple-id = pair-projections ∙
    pair-cong (idIso x) (pair-η pr₂ ∙ pair-cong (idIso y) (pair-η (pr₂ ∘ pr₂)))
  tuple-isEquiv = equiv-transport (tuple-id ⁻¹) (id-isEquiv R)
  b₁ = Associativity.backward A T (X × C)
  b₂ = Associativity.backward (A × T) X C
  b₃ = Associativity.backward A (T × X) C
  k = productMap (id A) (Associativity.backward T X C)
  e = productMap (Associativity.backward A T X) (id C)
  left-normal = backward-pair (pair x y) z w ∙
    ((b₂ ◁ backward-pair x y (pair z w)) ∙ comp-assoc tuple b₁ b₂)
  k-normal = pair-cong (comp-unitˡ x) (backward-pair y z w) ∙
    productMap-pair (id A) (Associativity.backward T X C) x (pair y (pair z w))
  middle-normal = backward-pair x (pair y z) w ∙
    ((b₃ ◁ k-normal) ∙ comp-assoc tuple k b₃)
  right-normal = pair-cong (backward-pair x y z) (comp-unitˡ w) ∙
    (productMap-pair (Associativity.backward A T X) (id C) (pair x (pair y z)) w ∙
    ((e ◁ middle-normal) ∙ comp-assoc tuple (b₃ ∘ k) e))
```
