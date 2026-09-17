# Functors as absolute points of mapping animae

An external functor is named by currying its composite with the second
projection. Decoding uses the explicit inverse `pair (terminate C) (id C)`
of the second projection from `One × C`. These are compared by specified
natural isomorphisms, rather than identified by Agda equality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section02.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter01.Section03.Points
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

oneProduct-in : (C : CAT) → MAP C (One × C)
oneProduct-in C = pair (terminate C) (id C)

oneProduct-section : (C : CAT) → NatIso (oneProduct-in C ∘ pr₂) (id (One × C))
oneProduct-section C = pair-iso (terminal-iso _ _)
  (invIso (comp-unitʳ pr₂) ∙
    (comp-unitˡ pr₂ ∙ project-pair₂ (terminate C) (id C) pr₂))

oneProduct-retraction : (C : CAT) → NatIso (pr₂ ∘ oneProduct-in C) (id C)
oneProduct-retraction C = pair-β₂ (terminate C) (id C)

oneProduct-in-isEquiv : (C : CAT) → IsEquiv (oneProduct-in C)
oneProduct-in-isEquiv C = record
  { inverse = pr₂
  ; sectionIso = invIso (oneProduct-retraction C)
  ; retractionIso = invIso (oneProduct-section C) }

oneProduct-pr₂-isEquiv : (C : CAT) → IsEquiv (pr₂ {One} {C})
oneProduct-pr₂-isEquiv C = equiv-inverse (oneProduct-in-isEquiv C)

nameMap : {C D : CAT} → MAP C D → ObjAbs (Map C D)
nameMap f = mapCurry one-isAn (f ∘ pr₂)

decodeMap : {C D : CAT} → ObjAbs (Map C D) → MAP C D
decodeMap {C} a = mapUncurry a ∘ oneProduct-in C

decode-name : {C D : CAT} (f : MAP C D) → NatIso (decodeMap (nameMap f)) f
decode-name {C} f = comp-unitʳ f ∙
  ((f ◁ oneProduct-retraction C) ∙
    (comp-assoc (oneProduct-in C) pr₂ f ∙
      (mapCurry-β one-isAn (f ∘ pr₂) ▷ oneProduct-in C)))

name-decode : {C D : CAT} (a : ObjAbs (Map C D)) → NatIso (nameMap (decodeMap a)) a
name-decode {C} a = mapReflect one-isAn _ a
  (comp-unitʳ (mapUncurry a) ∙
    ((mapUncurry a ◁ oneProduct-section C) ∙
      (comp-assoc pr₂ (oneProduct-in C) (mapUncurry a) ∙
        mapCurry-β one-isAn (decodeMap a ∘ pr₂))))

decodeMap-isoMap : {C D : CAT} (a b : ObjAbs (Map C D))
  → MAP (a ≅ b) (decodeMap a ≅ decodeMap b)
decodeMap-isoMap {C} a b = preWhisker (oneProduct-in C) ∘ mapUncurry-isoMap a b

decodeMap-isoMap-isEquiv : {C D : CAT} (a b : ObjAbs (Map C D))
  → IsEquiv (decodeMap-isoMap a b)
decodeMap-isoMap-isEquiv {C} a b =
  equiv-compose (mapUncurry-isoMap a b) (preWhisker (oneProduct-in C))
    (mapUncurry-isoMap-isEquiv one-isAn a b)
    (preWhisker-isEquiv (oneProduct-in C) (oneProduct-in-isEquiv C)
      (mapUncurry a) (mapUncurry b))

decodeMapIso : {C D : CAT} {a b : ObjAbs (Map C D)}
  → NatIso a b → NatIso (decodeMap a) (decodeMap b)
decodeMapIso {a = a} {b} α = decodeMap-isoMap a b ∘ α

decodeMapIso-at : {C D : CAT} {a b : ObjAbs (Map C D)} (α : NatIso a b)
  → Iso₂ (decodeMapIso α) (mapUncurryIso α ▷ oneProduct-in C)
decodeMapIso-at {C} {a = a} {b} α = comp-assoc α (mapUncurry-isoMap a b) (preWhisker (oneProduct-in C))

decodeMap-reflect : {C D : CAT} (a b : ObjAbs (Map C D))
  → NatIso (decodeMap a) (decodeMap b) → NatIso a b
decodeMap-reflect a b α = FunctorLift.lift (equiv-lift (decodeMap-isoMap-isEquiv a b) α)

decodeMap-reflect-β : {C D : CAT} (a b : ObjAbs (Map C D))
  (α : NatIso (decodeMap a) (decodeMap b))
  → Iso₂ (decodeMapIso (decodeMap-reflect a b α)) α
decodeMap-reflect-β a b α = FunctorLift.comparison (equiv-lift (decodeMap-isoMap-isEquiv a b) α)
```

Naming also has an actual action on isomorphism animae. Its endpoint changes
are the comparisons just proved for decoded names. Each factor in the
construction is an equivalence.

```agda
nameMap-isoMap : {C D : CAT} (f g : MAP C D) → MAP (f ≅ g) (nameMap f ≅ nameMap g)
nameMap-isoMap f g =
  IsEquiv.inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)) ∘
    (leftMultiply (invIso (decode-name g)) ∘ rightMultiply (decode-name f))

nameMap-isoMap-isEquiv : {C D : CAT} (f g : MAP C D) → IsEquiv (nameMap-isoMap f g)
nameMap-isoMap-isEquiv f g = equiv-compose
  (leftMultiply (invIso (decode-name g)) ∘ rightMultiply (decode-name f))
  (IsEquiv.inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)))
  (equiv-compose (rightMultiply (decode-name f)) (leftMultiply (invIso (decode-name g)))
    (rightMultiply-isEquiv (decode-name f)) (leftMultiply-isEquiv (invIso (decode-name g))))
  (equiv-inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)))

nameMapIso : {C D : CAT} {f g : MAP C D} → NatIso f g → NatIso (nameMap f) (nameMap g)
nameMapIso {f = f} {g} α = nameMap-isoMap f g ∘ α

decodeMap-Iso₂ : {C D : CAT} {a b : ObjAbs (Map C D)} {α β : NatIso a b}
  → Iso₂ α β → Iso₂ (decodeMapIso α) (decodeMapIso β)
decodeMap-Iso₂ {a = a} {b} p = decodeMap-isoMap a b ◁ p

decodeMap-reflect-Iso₂ : {C D : CAT} {a b : ObjAbs (Map C D)} (α β : NatIso a b)
  → Iso₂ (decodeMapIso α) (decodeMapIso β) → Iso₂ α β
decodeMap-reflect-Iso₂ {a = a} {b} α β = equiv-reflect (decodeMap-isoMap-isEquiv a b) α β

nameMap-Iso₂ : {C D : CAT} {f g : MAP C D} {α β : NatIso f g}
  → Iso₂ α β → Iso₂ (nameMapIso α) (nameMapIso β)
nameMap-Iso₂ {f = f} {g} p = nameMap-isoMap f g ◁ p
```
