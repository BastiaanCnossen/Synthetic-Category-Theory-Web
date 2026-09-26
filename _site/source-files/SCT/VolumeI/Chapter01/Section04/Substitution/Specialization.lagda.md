# Specializing functors between mapping animae

This implements `lem:Pair_Specific_Specialization`. Naming and decoding are
kept visible: a functor between mapping animae is applied to the name of an
external functor, and its resulting absolute point is decoded. The action on
isomorphisms is an actual composite of functors between isomorphism animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Points as Points

module SCT.VolumeI.Chapter01.Section04.Substitution.Specialization
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Points 𝒯 M

specializeMap : {A B C D : CAT} → MAP (Map A B) (Map C D) → MAP A B → MAP C D
specializeMap H f = decodeMap (H ∘ nameMap f)

specializeMap-id : {A B : CAT} (f : MAP A B)
  → (specializeMap (id (Map A B)) f) =₁ f
specializeMap-id f = decode-name f ∙ decodeMapIso (comp-unitˡ (nameMap f))

specializeMap-comp : {A B C D E F : CAT}
  (H : MAP (Map A B) (Map C D)) (K : MAP (Map C D) (Map E F)) (f : MAP A B)
  → (specializeMap (K ∘ H) f) =₁ (specializeMap K (specializeMap H f))
specializeMap-comp H K f = decodeMapIso
  ((K ◁ name-decode (H ∘ nameMap f)) ⁻¹ ∙ comp-assoc (nameMap f) H K)

specializeMap-isoMap : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  (f g : MAP A B) → MAP (f ＝ g) (specializeMap H f ＝ specializeMap H g)
specializeMap-isoMap H f g = decodeMap-isoMap (H ∘ nameMap f) (H ∘ nameMap g) ∘
  (postWhisker H ∘ nameMap-isoMap f g)

specializeMapIso : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  {f g : MAP A B} → f =₁ g → (specializeMap H f) =₁ (specializeMap H g)
specializeMapIso H {f} {g} α = specializeMap-isoMap H f g ∘ α

specializeMap-Iso₂ : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  {f g : MAP A B} {α β : f =₁ g}
  → α =₂ β → (specializeMapIso H α) =₂ (specializeMapIso H β)
specializeMap-Iso₂ H {f} {g} p = specializeMap-isoMap H f g ◁ p

specializeMap-changeMap : {A B C D : CAT} (H K : MAP (Map A B) (Map C D))
  (f : MAP A B) → MAP (H ＝ K) (specializeMap H f ＝ specializeMap K f)
specializeMap-changeMap H K f =
  decodeMap-isoMap (H ∘ nameMap f) (K ∘ nameMap f) ∘ preWhisker (nameMap f)

specializeMap-change : {A B C D : CAT} {H K : MAP (Map A B) (Map C D)}
  (τ : H =₁ K) (f : MAP A B) → (specializeMap H f) =₁ (specializeMap K f)
specializeMap-change {H = H} {K} τ f = specializeMap-changeMap H K f ∘ τ

specializeMap-isoMap-isEquiv : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  → IsEquiv H → (f g : MAP A B) → IsEquiv (specializeMap-isoMap H f g)
specializeMap-isoMap-isEquiv H e f g =
  equiv-compose (postWhisker H ∘ nameMap-isoMap f g)
    (decodeMap-isoMap (H ∘ nameMap f) (H ∘ nameMap g))
    (equiv-compose (nameMap-isoMap f g) (postWhisker H)
      (nameMap-isoMap-isEquiv f g) (postWhisker-isEquiv H e (nameMap f) (nameMap g)))
    (decodeMap-isoMap-isEquiv (H ∘ nameMap f) (H ∘ nameMap g))
```

When `H` is an equivalence, a functor and each specified comparison can be
lifted. Image witnesses are retained, including for higher identifications.

```agda
record SpecializationLift {A B C D : CAT}
  (H : MAP (Map A B) (Map C D)) (g : MAP C D) : Set m where
  field
    functor : MAP A B
    comparison : (specializeMap H functor) =₁ g

specializeMap-lift : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  → IsEquiv H → (g : MAP C D) → SpecializationLift H g
specializeMap-lift H e g =
  let pointLift = equiv-lift e (nameMap g)
      point = FunctorLift.lift pointLift
      image = FunctorLift.comparison pointLift
  in record
    { functor = decodeMap point
    ; comparison = decode-name g ∙ decodeMapIso (image ∙ (H ◁ name-decode point)) }

specializeMap-reflect : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  → IsEquiv H → (f g : MAP A B)
  → (specializeMap H f) =₁ (specializeMap H g) → f =₁ g
specializeMap-reflect H e f g α =
  FunctorLift.lift (equiv-lift (specializeMap-isoMap-isEquiv H e f g) α)

specializeMap-reflect-β : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  (e : IsEquiv H) (f g : MAP A B) (α : (specializeMap H f) =₁ (specializeMap H g))
  → (specializeMapIso H (specializeMap-reflect H e f g α)) =₂ α
specializeMap-reflect-β H e f g α =
  FunctorLift.comparison (equiv-lift (specializeMap-isoMap-isEquiv H e f g) α)

specializeMap-reflect-Iso₂ : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  → IsEquiv H → {f g : MAP A B} → (α β : f =₁ g)
  → (specializeMapIso H α) =₂ (specializeMapIso H β) → α =₂ β
specializeMap-reflect-Iso₂ H e {f} {g} α β =
  equiv-reflect (specializeMap-isoMap-isEquiv H e f g) α β

specializeMap-Iso₂-lift : {A B C D : CAT} (H : MAP (Map A B) (Map C D))
  (e : IsEquiv H) {f g : MAP A B} (α β : f =₁ g)
  (p : (specializeMapIso H α) =₂ (specializeMapIso H β))
  → FunctorLift (postWhisker (specializeMap-isoMap H f g)) p
specializeMap-Iso₂-lift H e {f} {g} α β p =
  postWhisker-lift (specializeMap-isoMap H f g) (specializeMap-isoMap-isEquiv H e f g) p
```
