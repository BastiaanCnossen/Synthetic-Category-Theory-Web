# Restricting and composing copairs

These short calculations keep the associators visible. They support the
coproduct exercises without choosing further primitive structure.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section05.CoproductCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B public

copair-pre₁ : {X C D E : CAT} (f : MAP C E) (g : MAP D E) (h : MAP X C)
  → (copair f g ∘ (in₁ ∘ h)) =₁ (f ∘ h)
copair-pre₁ f g h = (copair-β₁ f g ▷ h) ∙ (comp-assoc h in₁ (copair f g)) ⁻¹

copair-pre₂ : {X C D E : CAT} (f : MAP C E) (g : MAP D E) (h : MAP X D)
  → (copair f g ∘ (in₂ ∘ h)) =₁ (g ∘ h)
copair-pre₂ f g h = (copair-β₂ f g ▷ h) ∙ (comp-assoc h in₂ (copair f g)) ⁻¹

copair-inclusions : (C D : CAT) → (copair (in₁ {C} {D}) in₂) =₁ (id (C ⊔ D))
copair-inclusions C D = coproduct-reflect _ _
  ((comp-unitˡ in₁) ⁻¹ ∙ copair-β₁ in₁ in₂)
  ((comp-unitˡ in₂) ⁻¹ ∙ copair-β₂ in₁ in₂)

coproductMap : {C C′ D D′ : CAT} → MAP C C′ → MAP D D′ → MAP (C ⊔ D) (C′ ⊔ D′)
coproductMap f g = copair (in₁ ∘ f) (in₂ ∘ g)

coproductMap-cong : {C C′ D D′ : CAT} {f f′ : MAP C C′} {g g′ : MAP D D′}
  → f =₁ f′ → g =₁ g′ → (coproductMap f g) =₁ (coproductMap f′ g′)
coproductMap-cong α β = copair-cong (in₁ ◁ α) (in₂ ◁ β)

coproductMap-id : (C D : CAT) → (coproductMap (id C) (id D)) =₁ (id (C ⊔ D))
coproductMap-id C D = copair-inclusions C D ∙ copair-cong (comp-unitʳ in₁) (comp-unitʳ in₂)

coproductMap-comp : {C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
  → (coproductMap f′ g′ ∘ coproductMap f g) =₁ (coproductMap (f′ ∘ f) (g′ ∘ g))
coproductMap-comp f f′ g g′ =
  copair-cong (comp-assoc f f′ in₁ ∙ copair-pre₁ (in₁ ∘ f′) (in₂ ∘ g′) f)
    (comp-assoc g g′ in₂ ∙ copair-pre₂ (in₁ ∘ f′) (in₂ ∘ g′) g) ∙
  copair-post (in₁ ∘ f) (in₂ ∘ g) (coproductMap f′ g′)

coproductMap-isEquiv : {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′)
  → IsEquiv f → IsEquiv g → IsEquiv (coproductMap f g)
coproductMap-isEquiv {C} {C′} {D} {D′} f g ef eg = record
  { inverse = coproductMap (IsEquiv.inverse ef) (IsEquiv.inverse eg)
  ; sectionIso = (coproductMap-comp f (IsEquiv.inverse ef) g (IsEquiv.inverse eg)) ⁻¹ ∙
      (coproductMap-cong (IsEquiv.sectionIso ef) (IsEquiv.sectionIso eg) ∙ (coproductMap-id C D) ⁻¹)
  ; retractionIso = (coproductMap-comp (IsEquiv.inverse ef) f (IsEquiv.inverse eg) g) ⁻¹ ∙
      (coproductMap-cong (IsEquiv.retractionIso ef) (IsEquiv.retractionIso eg) ∙ (coproductMap-id C′ D′) ⁻¹) }
```
