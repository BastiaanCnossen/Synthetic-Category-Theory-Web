# Pushout squares through mapping animae

A supplied square includes its specified commuting identification. Mapping
out into E reverses its arrows, using the chosen precomposition comparisons
and the image of that identification to form the entire mapping cone.
IsPushout requires this actual cone to be universal for every categorical E.
It asserts a property of the supplied square, without choosing new pushouts.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section08.PushoutSquares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (extend)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre⁼; mapPre-comp)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback; module UniversalCone)

module _ {Γ : Context} where
  mappingOut : {A B C D : CAT Γ} {l : MAP A C} {r : MAP B D}
    (s : Square l r) (E : CAT Γ)
    → Cone (mapPre {D = E} (Square.source-map s)) (mapPre l) (Map D E)
  mappingOut {l = l} {r} s E = record
    { left = mapPre r ; right = mapPre (Square.target-map s)
    ; match = (mapPre-comp l (Square.target-map s)) ⁻¹ ∙
        (mapPre⁼ (Square.cell s) ∙ mapPre-comp (Square.source-map s) r) }

  IsPushout : {A B C D : CAT Γ} {l : MAP A C} {r : MAP B D}
    → Square l r → Set (c ⊔ m)
  IsPushout s = (E : CAT Γ) → IsPullback (mappingOut s E)
```

The mapping-out universal cone extends compatible families of mapping terms,
with both prescribed leg computations and their entire matching square.
The categorical parameter of such a family need not be an anima.

```agda
  module PushoutExtension {A B C D : CAT Γ} {l : MAP A C} {r : MAP B D}
    (s : Square l r) (e : IsPushout s) (E : CAT Γ) where
    private
      module Universal = UniversalCone (mappingOut s E) (e E)

    extend : {K : CAT Γ}
      → Cone (mapPre {D = E} (Square.source-map s)) (mapPre l) K → MAP K (Map D E)
    extend = Universal.factor

    β : {K : CAT Γ} (t : Cone (mapPre {D = E} (Square.source-map s)) (mapPre l) K)
      → ConeIdentification₁ (cone-restrict (extend t) (mappingOut s E)) t
    β = Universal.β

    left-image : {K : CAT Γ} (t : Cone (mapPre {D = E} (Square.source-map s)) (mapPre l) K)
      → (mapPre r ∘ extend t) =₁ Cone.left t
    left-image = Universal.β₁

    right-image : {K : CAT Γ} (t : Cone (mapPre {D = E} (Square.source-map s)) (mapPre l) K)
      → (mapPre (Square.target-map s) ∘ extend t) =₁ Cone.right t
    right-image = Universal.β₂
```
