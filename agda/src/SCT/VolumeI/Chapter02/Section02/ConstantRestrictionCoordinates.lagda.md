# The coordinates of a constant restriction

Both ways of evaluating a constant restriction preserve the parameter
coordinate. Their second coordinates are the images under the chosen
object of two terminal identifications. Uniqueness is used only for those
identifications into `One`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.SectionComparisonEvaluation as Evaluation
import SCT.VolumeI.Chapter02.Section02.UniversalArrowEvaluation as Units

module SCT.VolumeI.Chapter02.Section02.ConstantRestrictionCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (lift-base; compose-base)
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (lift-assoc)
open import SCT.VolumeI.Chapter01.Section04.IdentityParameterChange 𝒯 M using (terminal-Iso₂)

module At {A B : CAT} (X : CAT) (x : Obj-abs A) (z : Obj-abs B) where
  π = pr₁ {C = X} {D = A}
  ρ = pr₂ {C = X} {D = A}
  i = insert {X = X} x
  t = terminate X
  s = terminate A
  b₁ = pair-β₁ (id X) (const {P = X} x)
  b₂ = pair-β₂ (id X) (const {P = X} x)
  ε = terminal-iso (s ∘ ρ) (t ∘ π)
  εx = terminal-iso (s ∘ x) (id One)
  point = section-image s x εx z
  constant-comparison = (comp-assoc π t z) ⁻¹ ∙
    ((z ◁ ε) ∙ comp-assoc ρ s z)
  terminal-source = section-image π i b₁ t ∙ (ε ▷ i)
  terminal-middle = compose-base s x εx t (comp-unitˡ t)
  terminal-target = terminal-middle ∙ lift-base s ρ i b₂
  inner-assoc = comp-assoc i (s ∘ ρ) z
  outer-assoc = comp-assoc ρ s z ▷ i
  prefix = (point ▷ t) ∙ (comp-assoc t x (z ∘ s)) ⁻¹
  restriction = lift-base (z ∘ s) ρ i b₂
  left-second = section-image π i b₁ (z ∘ t) ∙ (constant-comparison ▷ i)
  right-second = (point ▷ t) ∙ ((comp-assoc t x (z ∘ s)) ⁻¹ ∙ restriction)
  module Change = Evaluation.At 𝒯 π i b₁ t (s ∘ ρ) ε z

  abstract
    left-normalization : left-second =₂
      (((z ◁ terminal-source) ∙ inner-assoc) ∙ outer-assoc)
    left-normalization = isoComp-cong Change.comparison (idIso outer-assoc) ∙
      ((isoComp-assoc-at (section-image π i b₁ (z ∘ t)) (Change.δ ▷ i) outer-assoc) ⁻¹ ∙
      isoComp-cong (idIso (section-image π i b₁ (z ∘ t)))
        (preWhisker-isoComp-at Change.δ (comp-assoc ρ s z) i ∙
          (preWhisker i ◁ ((isoComp-assoc-at ((comp-assoc π t z) ⁻¹)
            (z ◁ ε) (comp-assoc ρ s z)) ⁻¹))))

    point-normalization : prefix =₂ lift-base z s (x ∘ t) terminal-middle
    point-normalization = section-pre s x εx t z ∙ (isoComp-unitˡ-at prefix) ⁻¹

    right-normalization : right-second =₂
      (((z ◁ terminal-target) ∙ inner-assoc) ∙ outer-assoc)
    right-normalization = isoComp-cong
        (isoComp-cong ((postWhisker-isoComp-at z terminal-middle (lift-base s ρ i b₂)) ⁻¹)
            (idIso inner-assoc) ∙
          (isoComp-assoc-at (z ◁ terminal-middle) (z ◁ lift-base s ρ i b₂) inner-assoc) ⁻¹) (idIso outer-assoc) ∙
      ((isoComp-assoc-at (z ◁ terminal-middle)
        (lift-base z (s ∘ ρ) i (lift-base s ρ i b₂)) outer-assoc) ⁻¹ ∙
      (isoComp-cong (idIso (z ◁ terminal-middle)) (lift-assoc ρ (x ∘ t) i b₂ s z) ∙
      (isoComp-assoc-at (z ◁ terminal-middle) (comp-assoc (x ∘ t) s z) restriction ∙
      (isoComp-cong point-normalization (idIso restriction) ∙
        (isoComp-assoc-at (point ▷ t) ((comp-assoc t x (z ∘ s)) ⁻¹) restriction) ⁻¹))))

    second-coordinate : left-second =₂ right-second
    second-coordinate = right-normalization ⁻¹ ∙
      (isoComp-cong (isoComp-cong (postWhisker z ◁ terminal-Iso₂ terminal-source terminal-target)
        (idIso inner-assoc)) (idIso outer-assoc) ∙ left-normalization)

    first-coordinate :
      (section-image π i b₁ (id X) ∙ (idIso (id X ∘ π) ▷ i)) =₂
      (comp-unitˡ (id X) ∙ lift-base (id X) π i b₁)
    first-coordinate = isoComp-cong ((Units.identity-unitors 𝒯 M ℱ X) ⁻¹)
        (idIso (lift-base (id X) π i b₁)) ∙
      (isoComp-unitʳ-at (section-image π i b₁ (id X)) ∙
        isoComp-cong (idIso (section-image π i b₁ (id X)))
          (preWhisker-idIso (id X ∘ π) i))
```
