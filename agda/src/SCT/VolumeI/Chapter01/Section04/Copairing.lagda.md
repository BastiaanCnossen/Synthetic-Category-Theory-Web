# Copairing functors

Following `con:Copairing`, apply the inverse of the coproduct restriction
equivalence to the pair of representing points, then decode the result.
The two restrictions are compared with the original functors explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section04.Copairing
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B

copairPoint : {C D E : CAT} → MAP C E → MAP D E → ObjAbs (Map (C ⊔ D) E)
copairPoint {C} {D} {E} f g =
  FunctorLift.lift (equiv-lift (coproductRestriction-isEquiv C D E) (pair (nameMap f) (nameMap g)))

copairPoint-β : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → NatIso (coproductRestriction C D E ∘ copairPoint f g) (pair (nameMap f) (nameMap g))
copairPoint-β {C} {D} {E} f g =
  FunctorLift.comparison (equiv-lift (coproductRestriction-isEquiv C D E) (pair (nameMap f) (nameMap g)))

copair : {C D E : CAT} → MAP C E → MAP D E → MAP (C ⊔ D) E
copair f g = decodeMap (copairPoint f g)

copair-β₁ : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → NatIso (copair f g ∘ in₁) f
copair-β₁ f g = unnamedIso
  (pair-β₁ (nameMap f) (nameMap g) ∙
  ((pr₁ ◁ copairPoint-β f g) ∙
  (invIso (project-pair₁ (mapPre in₁) (mapPre in₂) (copairPoint f g)) ∙
  ((mapPre in₁ ◁ name-decode (copairPoint f g)) ∙
   invIso (mapPre-name in₁ (copair f g))))))

copair-β₂ : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → NatIso (copair f g ∘ in₂) g
copair-β₂ f g = unnamedIso
  (pair-β₂ (nameMap f) (nameMap g) ∙
  ((pr₂ ◁ copairPoint-β f g) ∙
  (invIso (project-pair₂ (mapPre in₁) (mapPre in₂) (copairPoint f g)) ∙
  ((mapPre in₂ ◁ name-decode (copairPoint f g)) ∙
   invIso (mapPre-name in₂ (copair f g))))))
```

For comparisons between functors, reflect through the same restriction
equivalence on representing points. This first consequence supplies a
comparison; the stronger prescribed-image statement is treated separately.

```agda
restrict-name₁ : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → NatIso (pr₁ ∘ (coproductRestriction C D E ∘ nameMap h)) (nameMap (h ∘ in₁))
restrict-name₁ h = mapPre-name in₁ h ∙ project-pair₁ (mapPre in₁) (mapPre in₂) (nameMap h)

restrict-name₂ : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → NatIso (pr₂ ∘ (coproductRestriction C D E ∘ nameMap h)) (nameMap (h ∘ in₂))
restrict-name₂ h = mapPre-name in₂ h ∙ project-pair₂ (mapPre in₁) (mapPre in₂) (nameMap h)

coproduct-reflect : {C D E : CAT} (h k : MAP (C ⊔ D) E)
  → NatIso (h ∘ in₁) (k ∘ in₁) → NatIso (h ∘ in₂) (k ∘ in₂) → NatIso h k
coproduct-reflect {C} {D} {E} h k α β = unnamedIso
  (equiv-reflect (coproductRestriction-isEquiv C D E) (nameMap h) (nameMap k)
    (pair-iso
      (invIso (restrict-name₁ k) ∙ (nameMapIso α ∙ restrict-name₁ h))
      (invIso (restrict-name₂ k) ∙ (nameMapIso β ∙ restrict-name₂ h))))

copair-η : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → NatIso (copair (h ∘ in₁) (h ∘ in₂)) h
copair-η h = coproduct-reflect _ h (copair-β₁ (h ∘ in₁) (h ∘ in₂))
  (copair-β₂ (h ∘ in₁) (h ∘ in₂))

copair-cong : {C D E : CAT} {f f′ : MAP C E} {g g′ : MAP D E}
  → NatIso f f′ → NatIso g g′ → NatIso (copair f g) (copair f′ g′)
copair-cong {f = f} {f′} {g} {g′} α β = coproduct-reflect _ _
  (invIso (copair-β₁ f′ g′) ∙ (α ∙ copair-β₁ f g))
  (invIso (copair-β₂ f′ g′) ∙ (β ∙ copair-β₂ f g))

copair-post : {C D E F : CAT} (f : MAP C E) (g : MAP D E) (h : MAP E F)
  → NatIso (h ∘ copair f g) (copair (h ∘ f) (h ∘ g))
copair-post f g h = coproduct-reflect _ _
  (invIso (copair-β₁ (h ∘ f) (h ∘ g)) ∙ ((h ◁ copair-β₁ f g) ∙ comp-assoc in₁ (copair f g) h))
  (invIso (copair-β₂ (h ∘ f) (h ∘ g)) ∙ ((h ◁ copair-β₂ f g) ∙ comp-assoc in₂ (copair f g) h))
```
