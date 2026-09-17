# Checking equivalences on mapping animae

The recognition argument uses only the two test categories appearing in
the proof: the source and the target of the functor. This also makes the
anima-only variant immediate when both categories are animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Points as Points
import SCT.VolumeI.Chapter01.Section03.Functoriality as Functoriality

module SCT.VolumeI.Chapter01.Section03.EquivalenceDetection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open Points 𝒯 M
open Functoriality 𝒯 M

unnamedIso : {C D : CAT} {f g : MAP C D}
  → NatIso (nameMap f) (nameMap g) → NatIso f g
unnamedIso {f = f} {g} α = decode-name g ∙ (decodeMapIso α ∙ invIso (decode-name f))

mapPost-name : {B C D : CAT} (f : MAP C D) (g : MAP B C)
  → NatIso (mapPost f ∘ nameMap g) (nameMap (f ∘ g))
mapPost-name f g = mapReflect one-isAn _ _
  (invIso (mapCurry-β one-isAn ((f ∘ g) ∘ pr₂)) ∙
  (invIso (comp-assoc pr₂ g f) ∙
  ((f ◁ mapCurry-β one-isAn (g ∘ pr₂)) ∙ mapPost-uncurry f (nameMap g))))

mapPre-name : {B C D : CAT} (f : MAP B C) (g : MAP C D)
  → NatIso (mapPre f ∘ nameMap g) (nameMap (g ∘ f))
mapPre-name f g = mapReflect one-isAn _ _
  (invIso (mapCurry-β one-isAn ((g ∘ f) ∘ pr₂)) ∙
  (invIso (comp-assoc pr₂ f g) ∙
  ((g ◁ pair-β₂ (id One ∘ pr₁) (f ∘ pr₂)) ∙
  (comp-assoc (productMap (id One) f) pr₂ g ∙
  ((mapCurry-β one-isAn (g ∘ pr₂) ▷ productMap (id One) f) ∙
     mapPre-uncurry f (nameMap g))))))
```

An equivalence on a mapping anima reflects the isomorphisms between named
functors. The named comparisons above transport the endpoints; no strict
identification of a functor with its representing point is used.

```agda
mapPost-reflect : {B C D : CAT} (f : MAP C D)
  → IsEquiv (mapPost {C = B} f)
  → (g h : MAP B C) → NatIso (f ∘ g) (f ∘ h) → NatIso g h
mapPost-reflect f e g h α = unnamedIso (equiv-reflect e (nameMap g) (nameMap h)
  (invIso (mapPost-name f h) ∙ (nameMapIso α ∙ mapPost-name f g)))

mapPre-reflect : {B C D : CAT} (f : MAP B C)
  → IsEquiv (mapPre {D = D} f)
  → (g h : MAP C D) → NatIso (g ∘ f) (h ∘ f) → NatIso g h
mapPre-reflect f e g h α = unnamedIso (equiv-reflect e (nameMap g) (nameMap h)
  (invIso (mapPre-name f h) ∙ (nameMapIso α ∙ mapPre-name f g)))

mapPost-section : {C D : CAT} (f : MAP C D)
  → IsEquiv (mapPost {C = D} f) → Section f
mapPost-section {D = D} f e = record
  { section = decodeMap point
  ; comparison = unnamedIso
      (FunctorLift.comparison chosen ∙
        ((mapPost f ◁ name-decode point) ∙ invIso (mapPost-name f (decodeMap point))))
  }
  where
  chosen : FunctorLift (mapPost f) (nameMap (id D))
  chosen = equiv-lift e (nameMap (id D))
  point = FunctorLift.lift chosen

mapPre-retraction : {C D : CAT} (f : MAP C D)
  → IsEquiv (mapPre {D = C} f) → Retraction f
mapPre-retraction {C} f e = record
  { retraction = decodeMap point
  ; comparison = invIso (unnamedIso
      (FunctorLift.comparison chosen ∙
        ((mapPre f ◁ name-decode point) ∙ invIso (mapPre-name f (decodeMap point)))))
  }
  where
  chosen : FunctorLift (mapPre f) (nameMap (id C))
  chosen = equiv-lift e (nameMap (id C))
  point = FunctorLift.lift chosen
```

For postcomposition, first lift the identity of the target to obtain a
section, then reflect the other inverse comparison using the source test.
For precomposition the dual argument first obtains a retraction.

```agda
post-tests-isEquiv : {C D : CAT} (f : MAP C D)
  → IsEquiv (mapPost {C = C} f) → IsEquiv (mapPost {C = D} f) → IsEquiv f
post-tests-isEquiv {C} {D} f sourceTest targetTest = record
  { inverse = g
  ; sectionIso = invIso (mapPost-reflect f sourceTest (g ∘ f) (id C)
      (invIso (comp-unitʳ f) ∙
        (comp-unitˡ f ∙ ((Section.comparison s ▷ f) ∙ invIso (comp-assoc f g f)))))
  ; retractionIso = invIso (Section.comparison s)
  }
  where
  s = mapPost-section f targetTest
  g = Section.section s

pre-tests-isEquiv : {C D : CAT} (f : MAP C D)
  → IsEquiv (mapPre {D = C} f) → IsEquiv (mapPre {D = D} f) → IsEquiv f
pre-tests-isEquiv {C} {D} f sourceTest targetTest = record
  { inverse = g
  ; sectionIso = Retraction.comparison r
  ; retractionIso = invIso (mapPre-reflect f targetTest (f ∘ g) (id D)
      (invIso (comp-unitˡ f) ∙
        (comp-unitʳ f ∙ ((f ◁ invIso (Retraction.comparison r)) ∙ comp-assoc f g f))))
  }
  where
  r = mapPre-retraction f sourceTest
  g = Retraction.retraction r

post-tests-all : {C D : CAT} (f : MAP C D)
  → ((E : CAT) → IsEquiv (mapPost {C = E} f)) → IsEquiv f
post-tests-all {C} {D} f tests = post-tests-isEquiv f (tests C) (tests D)

pre-tests-all : {C D : CAT} (f : MAP C D)
  → ((E : CAT) → IsEquiv (mapPre {D = E} f)) → IsEquiv f
pre-tests-all {C} {D} f tests = pre-tests-isEquiv f (tests C) (tests D)

post-tests-animae : {C D : CAT} → isAn C → isAn D → (f : MAP C D)
  → ((E : CAT) → isAn E → IsEquiv (mapPost {C = E} f)) → IsEquiv f
post-tests-animae {C} {D} cAn dAn f tests = post-tests-isEquiv f (tests C cAn) (tests D dAn)

pre-tests-animae : {C D : CAT} → isAn C → isAn D → (f : MAP C D)
  → ((E : CAT) → isAn E → IsEquiv (mapPre {D = E} f)) → IsEquiv f
pre-tests-animae {C} {D} cAn dAn f tests = pre-tests-isEquiv f (tests C cAn) (tests D dAn)
```

Together with `mapPost-isEquiv` and `mapPre-isEquiv`, these give all
directions of the equivalence-detection proposition.
