# Copairing functors

Following `con:Copairing`, apply the inverse of the coproduct restriction
equivalence to the pair of representing points, then decode the result.
The two restrictions are compared with the original functors explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section05.Copairing
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B

-- The inverse restriction equivalence is itself a functor, so it can
-- combine mapping-anima-valued expressions with any common source X.
copairing : (C D E : CAT) → MAP (Map C E × Map D E) (Map (C ⊔ D) E)
copairing C D E = IsEquiv.inverse (coproductRestriction-isEquiv C D E)

copairFamily : {X C D E : CAT} → MAP X (Map C E) → MAP X (Map D E)
  → MAP X (Map (C ⊔ D) E)
copairFamily {C = C} {D} {E} u v = copairing C D E ∘ pair u v

copairPoint : {C D E : CAT} → MAP C E → MAP D E → Obj-abs (Map (C ⊔ D) E)
copairPoint {C} {D} {E} f g =
  FunctorLift.lift (equiv-lift (coproductRestriction-isEquiv C D E) (pair (nameMap f) (nameMap g)))

copairPoint-β : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → (coproductRestriction C D E ∘ copairPoint f g) =₁ (pair (nameMap f) (nameMap g))
copairPoint-β {C} {D} {E} f g =
  FunctorLift.comparison (equiv-lift (coproductRestriction-isEquiv C D E) (pair (nameMap f) (nameMap g)))

copair : {C D E : CAT} → MAP C E → MAP D E → MAP (C ⊔ D) E
copair f g = decodeMap (copairPoint f g)

copair-β₁ : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → (copair f g ∘ in₁) =₁ f
copair-β₁ f g = unnamedIso
  (pair-β₁ (nameMap f) (nameMap g) ∙
  ((pr₁ ◁ copairPoint-β f g) ∙
  ((project-pair₁ (mapPre in₁) (mapPre in₂) (copairPoint f g)) ⁻¹ ∙
  ((mapPre in₁ ◁ name-decode (copairPoint f g)) ∙
   (mapPre-name in₁ (copair f g)) ⁻¹))))

copair-β₂ : {C D E : CAT} (f : MAP C E) (g : MAP D E)
  → (copair f g ∘ in₂) =₁ g
copair-β₂ f g = unnamedIso
  (pair-β₂ (nameMap f) (nameMap g) ∙
  ((pr₂ ◁ copairPoint-β f g) ∙
  ((project-pair₂ (mapPre in₁) (mapPre in₂) (copairPoint f g)) ⁻¹ ∙
  ((mapPre in₂ ◁ name-decode (copairPoint f g)) ∙
   (mapPre-name in₂ (copair f g)) ⁻¹))))
```

For comparisons between functors, reflect through the same restriction
equivalence on representing points. This first consequence supplies a
comparison; the stronger prescribed-image statement is treated separately.

```agda
restrict-name₁ : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → (pr₁ ∘ (coproductRestriction C D E ∘ nameMap h)) =₁ (nameMap (h ∘ in₁))
restrict-name₁ h = mapPre-name in₁ h ∙ project-pair₁ (mapPre in₁) (mapPre in₂) (nameMap h)

restrict-name₂ : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → (pr₂ ∘ (coproductRestriction C D E ∘ nameMap h)) =₁ (nameMap (h ∘ in₂))
restrict-name₂ h = mapPre-name in₂ h ∙ project-pair₂ (mapPre in₁) (mapPre in₂) (nameMap h)

coproduct-reflect : {C D E : CAT} (h k : MAP (C ⊔ D) E)
  → (h ∘ in₁) =₁ (k ∘ in₁) → (h ∘ in₂) =₁ (k ∘ in₂) → h =₁ k
coproduct-reflect {C} {D} {E} h k α β = unnamedIso
  (equiv-reflect (coproductRestriction-isEquiv C D E) (nameMap h) (nameMap k)
    (pair-iso
      ((restrict-name₁ k) ⁻¹ ∙ (nameMapIso α ∙ restrict-name₁ h))
      ((restrict-name₂ k) ⁻¹ ∙ (nameMapIso β ∙ restrict-name₂ h))))

copair-η : {C D E : CAT} (h : MAP (C ⊔ D) E)
  → (copair (h ∘ in₁) (h ∘ in₂)) =₁ h
copair-η h = coproduct-reflect _ h (copair-β₁ (h ∘ in₁) (h ∘ in₂))
  (copair-β₂ (h ∘ in₁) (h ∘ in₂))

copair-cong : {C D E : CAT} {f f′ : MAP C E} {g g′ : MAP D E}
  → f =₁ f′ → g =₁ g′ → (copair f g) =₁ (copair f′ g′)
copair-cong {f = f} {f′} {g} {g′} α β = coproduct-reflect _ _
  ((copair-β₁ f′ g′) ⁻¹ ∙ (α ∙ copair-β₁ f g))
  ((copair-β₂ f′ g′) ⁻¹ ∙ (β ∙ copair-β₂ f g))

copair-post : {C D E F : CAT} (f : MAP C E) (g : MAP D E) (h : MAP E F)
  → (h ∘ copair f g) =₁ (copair (h ∘ f) (h ∘ g))
copair-post f g h = coproduct-reflect _ _
  ((copair-β₁ (h ∘ f) (h ∘ g)) ⁻¹ ∙ ((h ◁ copair-β₁ f g) ∙ comp-assoc in₁ (copair f g) h))
  ((copair-β₂ (h ∘ f) (h ∘ g)) ⁻¹ ∙ ((h ◁ copair-β₂ f g) ∙ comp-assoc in₂ (copair f g) h))
```
