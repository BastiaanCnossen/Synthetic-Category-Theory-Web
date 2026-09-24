# Functors as absolute points of mapping animae

`nameMap` sends a functor in `MAP C D` to an absolute point of `Map C D`;
`decodeMap` goes in the reverse direction. Their inverse comparisons are
`decode-name` and `name-decode`.

Naming curries the functor's composite with the second projection.
Decoding uses the explicit inverse `pair (terminate C) (id C)` of the
second projection from `One × C`. The inverse comparisons are natural
isomorphisms, rather than Agda equalities.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter01.Section04.Points
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

oneProduct-in : (C : CAT) → MAP C (One × C)
oneProduct-in C = pair (terminate C) (id C)

oneProduct-section : (C : CAT) → (oneProduct-in C ∘ pr₂) =₁ (id (One × C))
oneProduct-section C = pair-iso (terminal-iso _ _)
  ((comp-unitʳ pr₂) ⁻¹ ∙
    (comp-unitˡ pr₂ ∙ project-pair₂ (terminate C) (id C) pr₂))

oneProduct-retraction : (C : CAT) → (pr₂ ∘ oneProduct-in C) =₁ (id C)
oneProduct-retraction C = pair-β₂ (terminate C) (id C)

oneProduct-in-isEquiv : (C : CAT) → IsEquiv (oneProduct-in C)
oneProduct-in-isEquiv C = record
  { inverse = pr₂
  ; sectionIso = (oneProduct-retraction C) ⁻¹
  ; retractionIso = (oneProduct-section C) ⁻¹ }

oneProduct-pr₂-isEquiv : (C : CAT) → IsEquiv (pr₂ {One} {C})
oneProduct-pr₂-isEquiv C = equiv-inverse (oneProduct-in-isEquiv C)

nameMap : {C D : CAT} → MAP C D → Obj-abs (Map C D)
nameMap f = mapCurry one-isAn (f ∘ pr₂)

decodeMap : {C D : CAT} → Obj-abs (Map C D) → MAP C D
decodeMap {C} a = mapUncurry a ∘ oneProduct-in C

decode-name : {C D : CAT} (f : MAP C D) → (decodeMap (nameMap f)) =₁ f
decode-name {C} f = comp-unitʳ f ∙
  ((f ◁ oneProduct-retraction C) ∙
    (comp-assoc (oneProduct-in C) pr₂ f ∙
      (mapCurry-β one-isAn (f ∘ pr₂) ▷ oneProduct-in C)))

name-decode : {C D : CAT} (a : Obj-abs (Map C D)) → (nameMap (decodeMap a)) =₁ a
name-decode {C} a = mapReflect one-isAn _ a
  (comp-unitʳ (mapUncurry a) ∙
    ((mapUncurry a ◁ oneProduct-section C) ∙
      (comp-assoc pr₂ (oneProduct-in C) (mapUncurry a) ∙
        mapCurry-β one-isAn (decodeMap a ∘ pr₂))))

decodeMap-isoMap : {C D : CAT} (a b : Obj-abs (Map C D))
  → MAP (a ＝ b) (decodeMap a ＝ decodeMap b)
decodeMap-isoMap {C} a b = preWhisker (oneProduct-in C) ∘ mapUncurry-isoMap a b

decodeMap-isoMap-isEquiv : {C D : CAT} (a b : Obj-abs (Map C D))
  → IsEquiv (decodeMap-isoMap a b)
decodeMap-isoMap-isEquiv {C} a b =
  equiv-compose (mapUncurry-isoMap a b) (preWhisker (oneProduct-in C))
    (mapUncurry-isoMap-isEquiv one-isAn a b)
    (preWhisker-isEquiv (oneProduct-in C) (oneProduct-in-isEquiv C)
      (mapUncurry a) (mapUncurry b))

decodeMapIso : {C D : CAT} {a b : Obj-abs (Map C D)}
  → a =₁ b → (decodeMap a) =₁ (decodeMap b)
decodeMapIso {a = a} {b} α = decodeMap-isoMap a b ∘ α

decodeMapIso-at : {C D : CAT} {a b : Obj-abs (Map C D)} (α : a =₁ b)
  → (decodeMapIso α) =₂ (mapUncurryIso α ▷ oneProduct-in C)
decodeMapIso-at {C} {a = a} {b} α = comp-assoc α (mapUncurry-isoMap a b) (preWhisker (oneProduct-in C))

decodeMap-reflect : {C D : CAT} (a b : Obj-abs (Map C D))
  → (decodeMap a) =₁ (decodeMap b) → a =₁ b
decodeMap-reflect a b α = FunctorLift.lift (equiv-lift (decodeMap-isoMap-isEquiv a b) α)

decodeMap-reflect-β : {C D : CAT} (a b : Obj-abs (Map C D))
  (α : (decodeMap a) =₁ (decodeMap b))
  → (decodeMapIso (decodeMap-reflect a b α)) =₂ α
decodeMap-reflect-β a b α = FunctorLift.comparison (equiv-lift (decodeMap-isoMap-isEquiv a b) α)
```

Naming also has an actual action on isomorphism animae. Its endpoint changes
are the comparisons just proved for decoded names. Each factor in the
construction is an equivalence.

```agda
nameMap-isoMap : {C D : CAT} (f g : MAP C D) → MAP (f ＝ g) (nameMap f ＝ nameMap g)
nameMap-isoMap f g =
  IsEquiv.inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)) ∘
    (leftMultiply ((decode-name g) ⁻¹) ∘ rightMultiply (decode-name f))

nameMap-isoMap-isEquiv : {C D : CAT} (f g : MAP C D) → IsEquiv (nameMap-isoMap f g)
nameMap-isoMap-isEquiv f g = equiv-compose
  (leftMultiply ((decode-name g) ⁻¹) ∘ rightMultiply (decode-name f))
  (IsEquiv.inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)))
  (equiv-compose (rightMultiply (decode-name f)) (leftMultiply ((decode-name g) ⁻¹))
    (rightMultiply-isEquiv (decode-name f)) (leftMultiply-isEquiv ((decode-name g) ⁻¹)))
  (equiv-inverse (decodeMap-isoMap-isEquiv (nameMap f) (nameMap g)))

nameMapIso : {C D : CAT} {f g : MAP C D} → f =₁ g → (nameMap f) =₁ (nameMap g)
nameMapIso {f = f} {g} α = nameMap-isoMap f g ∘ α

decodeMap-Iso₂ : {C D : CAT} {a b : Obj-abs (Map C D)} {α β : a =₁ b}
  → α =₂ β → (decodeMapIso α) =₂ (decodeMapIso β)
decodeMap-Iso₂ {a = a} {b} p = decodeMap-isoMap a b ◁ p

decodeMap-reflect-Iso₂ : {C D : CAT} {a b : Obj-abs (Map C D)} (α β : a =₁ b)
  → (decodeMapIso α) =₂ (decodeMapIso β) → α =₂ β
decodeMap-reflect-Iso₂ {a = a} {b} α β = equiv-reflect (decodeMap-isoMap-isEquiv a b) α β

nameMap-Iso₂ : {C D : CAT} {f g : MAP C D} {α β : f =₁ g}
  → α =₂ β → (nameMapIso α) =₂ (nameMapIso β)
nameMap-Iso₂ {f = f} {g} p = nameMap-isoMap f g ◁ p
```
