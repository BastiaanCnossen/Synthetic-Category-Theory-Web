# Symmetry and units of coproducts

These are the commutativity and unitality parts of the coproduct exercise.
Only initiality is used for the unit, not strictness of the initial category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section05.CoproductEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (I : Initial.InitialStructure 𝒯 M) (B : Coproducts.CoproductStructure 𝒯 M) where

open Setup 𝒯 M
open Initial.Initiality 𝒯 M I
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B

coproductSwap : {C D : CAT} → MAP (C ⊔ D) (D ⊔ C)
coproductSwap = copair in₂ in₁

coproductSwap-swap : (C D : CAT) →
  (coproductSwap {D} {C} ∘ coproductSwap {C} {D}) =₁ (id (C ⊔ D))
coproductSwap-swap C D = copair-inclusions C D ∙
  (copair-cong (copair-β₂ in₂ in₁) (copair-β₁ in₂ in₁) ∙ copair-post in₂ in₁ coproductSwap)

coproductSwap-isEquiv : (C D : CAT) → IsEquiv (coproductSwap {C} {D})
coproductSwap-isEquiv C D = record
  { inverse = coproductSwap
  ; sectionIso = (coproductSwap-swap C D) ⁻¹
  ; retractionIso = (coproductSwap-swap D C) ⁻¹ }

coproduct-unitˡ : (C : CAT) → MAP (Zero ⊔ C) C
coproduct-unitˡ C = copair (initiate C) (id C)

coproduct-unitˡ-isEquiv : (C : CAT) → IsEquiv (coproduct-unitˡ C)
coproduct-unitˡ-isEquiv C = record
  { inverse = in₂
  ; sectionIso = (coproduct-reflect _ _ (initial-iso _ _)
      ((comp-unitˡ in₂) ⁻¹ ∙ (comp-unitʳ in₂ ∙
        ((in₂ ◁ copair-β₂ (initiate C) (id C)) ∙ comp-assoc in₂ (coproduct-unitˡ C) in₂)))) ⁻¹
  ; retractionIso = (copair-β₂ (initiate C) (id C)) ⁻¹ }

coproduct-unitʳ : (C : CAT) → MAP (C ⊔ Zero) C
coproduct-unitʳ C = copair (id C) (initiate C)

coproduct-unitʳ-isEquiv : (C : CAT) → IsEquiv (coproduct-unitʳ C)
coproduct-unitʳ-isEquiv C = record
  { inverse = in₁
  ; sectionIso = (coproduct-reflect _ _
      ((comp-unitˡ in₁) ⁻¹ ∙ (comp-unitʳ in₁ ∙
        ((in₁ ◁ copair-β₁ (id C) (initiate C)) ∙ comp-assoc in₁ (coproduct-unitʳ C) in₁)))
      (initial-iso _ _)) ⁻¹
  ; retractionIso = (copair-β₁ (id C) (initiate C)) ⁻¹ }
```
