# Units for pasted change-of-parameter squares

The unit square for a functor is the right unitor followed by the inverse
left unitor. Pasting it with a change-of-parameter square respects the
unitors. The proof uses the primitive triangle and the already derived
compatibility of external unitors with composition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.ParameterSquareUnits
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; right-unitor-comp)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at)

unit-square : {X Y : CAT} (x : MAP X Y) → (x ∘ id X) =₁ (id Y ∘ x)
unit-square x = (comp-unitˡ x) ⁻¹ ∙ comp-unitʳ x

abstract
  unit-square-cancel : {X Y : CAT} (x : MAP X Y)
    → (comp-unitˡ x ∙ unit-square x) =₂ (comp-unitʳ x)
  unit-square-cancel x = isoComp-unitˡ-at (comp-unitʳ x) ∙
    (isoComp-cong (isoComp-inverseʳ-at (comp-unitˡ x)) (idIso (comp-unitʳ x)) ∙
      (isoComp-assoc-at (comp-unitˡ x) ((comp-unitˡ x) ⁻¹) (comp-unitʳ x)) ⁻¹)

  paste-unitʳ : {X₀ X₁ Y₀ Y₁ : CAT}
    {f : MAP X₀ X₁} {F : MAP Y₀ Y₁} {x₀ : MAP X₀ Y₀} {x₁ : MAP X₁ Y₁}
    (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    → ((comp-unitʳ F ▷ x₀) ∙ paste α (unit-square x₀)) =₂
        (α ∙ (x₁ ◁ comp-unitʳ f))
  paste-unitʳ {X₀} {f = f} {F} {x₀ = x} {x₁ = y} α =
    let u = comp-unitʳ F ▷ x
        A = comp-assoc x (id _) F
        B = F ◁ unit-square x
        C = comp-assoc (id X₀) x F
        D = α ▷ id X₀
        E = (comp-assoc (id X₀) f y) ⁻¹
        head = cancel-right A (F ◁ comp-unitˡ x) ∙
          isoComp-cong (triangle-whiskered x F) (idIso (A ⁻¹))
        middle = (postWhisker F ◁ unit-square-cancel x) ∙
          (postWhisker-isoComp-at F (comp-unitˡ x) (unit-square x)) ⁻¹
        finish = cancel-right (comp-assoc (id X₀) f y) (y ◁ comp-unitʳ f) ∙
          isoComp-cong (right-unitor-comp f y) (idIso E)
    in isoComp-cong (idIso α) finish ∙
      (isoComp-assoc-at α (comp-unitʳ (y ∘ f)) E ∙
      (isoComp-cong (preWhisker-id-at α) (idIso E) ∙
      ((isoComp-assoc-at (comp-unitʳ (F ∘ x)) D E) ⁻¹ ∙
      (isoComp-cong ((right-unitor-comp x F) ⁻¹) (idIso (D ∙ E)) ∙
      ((isoComp-assoc-at (F ◁ comp-unitʳ x) C (D ∙ E)) ⁻¹ ∙
      (isoComp-cong middle (idIso (C ∙ (D ∙ E))) ∙
      ((isoComp-assoc-at (F ◁ comp-unitˡ x) B (C ∙ (D ∙ E))) ⁻¹ ∙
      (isoComp-cong head (idIso (B ∙ (C ∙ (D ∙ E)))) ∙
        (isoComp-assoc-at u (A ⁻¹) (B ∙ (C ∙ (D ∙ E)))) ⁻¹))))))))

  paste-unitˡ : {X₀ X₁ Y₀ Y₁ : CAT}
    {f : MAP X₀ X₁} {F : MAP Y₀ Y₁} {x₀ : MAP X₀ Y₀} {x₁ : MAP X₁ Y₁}
    (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    → ((comp-unitˡ F ▷ x₀) ∙ paste (unit-square x₁) α) =₂
        (α ∙ (x₁ ◁ comp-unitˡ f))
  paste-unitˡ {Y₁ = Y₁} {f = f} {F} {x₀ = x} {x₁ = y} α =
    let u = comp-unitˡ F ▷ x
        A = comp-assoc x F (id Y₁)
        B = id Y₁ ◁ α
        C = comp-assoc f y (id Y₁)
        D = unit-square y ▷ f
        E = (comp-assoc f (id _) y) ⁻¹
        head = cancel-right A (comp-unitˡ (F ∘ x)) ∙
          isoComp-cong ((left-unitor-comp x F) ⁻¹) (idIso (A ⁻¹))
        middle = (preWhisker f ◁ unit-square-cancel y) ∙
          (preWhisker-isoComp-at (comp-unitˡ y) (unit-square y) f) ⁻¹
        finish = cancel-right (comp-assoc f (id _) y) (y ◁ comp-unitˡ f) ∙
          isoComp-cong (triangle-whiskered f y) (idIso E)
        tail = finish ∙
          (isoComp-cong middle (idIso E) ∙
          ((isoComp-assoc-at (comp-unitˡ y ▷ f) D E) ⁻¹ ∙
          (isoComp-cong (left-unitor-comp f y) (idIso (D ∙ E)) ∙
            (isoComp-assoc-at (comp-unitˡ (y ∘ f)) C (D ∙ E)) ⁻¹)))
    in isoComp-cong (idIso α) tail ∙
      (isoComp-assoc-at α (comp-unitˡ (y ∘ f)) (C ∙ (D ∙ E)) ∙
      (isoComp-cong (postWhisker-id-at α) (idIso (C ∙ (D ∙ E))) ∙
      ((isoComp-assoc-at (comp-unitˡ (F ∘ x)) B (C ∙ (D ∙ E))) ⁻¹ ∙
      (isoComp-cong head (idIso (B ∙ (C ∙ (D ∙ E)))) ∙
        (isoComp-assoc-at u (A ⁻¹) (B ∙ (C ∙ (D ∙ E)))) ⁻¹))))
```
