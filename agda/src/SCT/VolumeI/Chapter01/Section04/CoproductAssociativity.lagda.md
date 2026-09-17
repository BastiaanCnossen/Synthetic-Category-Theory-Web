# Associativity of coproducts

The two maps are nested copairs. Each inverse comparison follows by
restricting to the three summands, keeping the intermediate copair beta
comparisons. This completes the associativity part of the Section 1.4 exercise.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section04.CoproductAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section04.CoproductCalculus 𝒯 M B

module CoproductAssociativity (C D E : CAT) where
  Source = (C ⊔ D) ⊔ E
  Target = C ⊔ (D ⊔ E)

  forward-left : MAP (C ⊔ D) Target
  forward-left = copair in₁ (in₂ ∘ in₁)

  backward-right : MAP (D ⊔ E) Source
  backward-right = copair (in₁ ∘ in₂) in₂

  forward : MAP Source Target
  forward = copair forward-left (in₂ ∘ in₂)

  backward : MAP Target Source
  backward = copair (in₁ ∘ in₁) backward-right

  backward-forward-left : NatIso (backward ∘ forward-left) in₁
  backward-forward-left = copair-η in₁ ∙
    (copair-cong (copair-β₁ (in₁ ∘ in₁) backward-right)
      (copair-β₁ (in₁ ∘ in₂) in₂ ∙ copair-pre₂ (in₁ ∘ in₁) backward-right in₁) ∙
      copair-post in₁ (in₂ ∘ in₁) backward)

  backward-forward-right : NatIso (backward ∘ (in₂ ∘ in₂)) in₂
  backward-forward-right = copair-β₂ (in₁ ∘ in₂) in₂ ∙
    copair-pre₂ (in₁ ∘ in₁) backward-right in₂

  backward-forward : NatIso (backward ∘ forward) (id Source)
  backward-forward = copair-inclusions (C ⊔ D) E ∙
    (copair-cong backward-forward-left backward-forward-right ∙
      copair-post forward-left (in₂ ∘ in₂) backward)

  forward-backward-left : NatIso (forward ∘ (in₁ ∘ in₁)) in₁
  forward-backward-left = copair-β₁ in₁ (in₂ ∘ in₁) ∙
    copair-pre₁ forward-left (in₂ ∘ in₂) in₁

  forward-backward-right : NatIso (forward ∘ backward-right) in₂
  forward-backward-right = copair-η in₂ ∙
    (copair-cong
      (copair-β₂ in₁ (in₂ ∘ in₁) ∙ copair-pre₁ forward-left (in₂ ∘ in₂) in₂)
      (copair-β₂ forward-left (in₂ ∘ in₂)) ∙
      copair-post (in₁ ∘ in₂) in₂ forward)

  forward-backward : NatIso (forward ∘ backward) (id Target)
  forward-backward = copair-inclusions C (D ⊔ E) ∙
    (copair-cong forward-backward-left forward-backward-right ∙
      copair-post (in₁ ∘ in₁) backward-right forward)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward }
```
