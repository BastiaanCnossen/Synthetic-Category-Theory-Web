# Adjoint sections from normalized transformations

A specified section identification and a counit over the base, restricting
to the identity on the section, determine a left adjoint section. The dual
construction uses a normalized unit. The triangle equations follow from
the inverse laws for the same section identification, with all endpoint
frames retained. This formalizes the description immediately after
`def:Left_Adjoint_Section`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-post; isomorphism-restrict; isomorphism-retarget; isomorphism-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.NormalizedIdentityExpressions 𝒯 M ℱ P I E
  using (normalized-identity)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.PrimitiveInverses 𝒯 M ℱ P I E S
  using (identification-right-inverse; identification-invertible)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)

module WithSection {C D : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  section-frame : ((s ∘ p) ∘ s) =₁ s
  section-frame = comp-unitʳ s ∙ ((s ◁ ρ) ∙ comp-assoc s p s)
  base-frame : ((p ∘ s) ∘ p) =₁ p
  base-frame = comp-unitˡ p ∙ (ρ ▷ p)

  module Left (ε : MorphismExpression (s ∘ p) (id C)) where
    unit = isomorphism-expression (ρ ⁻¹)
    left-unit = retarget-expression (post-expression s unit)
      (comp-unitʳ s) ((comp-assoc s p s) ⁻¹)
    left-counit = retarget-expression (restrict-expression ε s)
      (idIso ((s ∘ p) ∘ s)) (comp-unitˡ s)
    right-unit = retarget-expression (restrict-expression unit p)
      (comp-unitˡ p) (idIso ((p ∘ s) ∘ p))
    right-counit = retarget-expression (post-expression p ε)
      ((comp-assoc p s p) ⁻¹) (comp-unitʳ p)

    abstract
      left-unit-frame :
        (((comp-assoc s p s) ⁻¹ ∙ (s ◁ ρ ⁻¹)) ∙ (comp-unitʳ s) ⁻¹) =₂ (section-frame ⁻¹)
      left-unit-frame = (inverse-composite (comp-unitʳ s) ((s ◁ ρ) ∙ comp-assoc s p s)) ⁻¹ ∙
        isoComp-cong
          ((inverse-composite (s ◁ ρ) (comp-assoc s p s)) ⁻¹ ∙
            isoComp-cong (idIso ((comp-assoc s p s) ⁻¹)) (post-inverse s ρ))
          (idIso ((comp-unitʳ s) ⁻¹))

      right-unit-frame :
        ((idIso ((p ∘ s) ∘ p) ∙ (ρ ⁻¹ ▷ p)) ∙ (comp-unitˡ p) ⁻¹) =₂ (base-frame ⁻¹)
      right-unit-frame = (inverse-composite (comp-unitˡ p) (ρ ▷ p)) ⁻¹ ∙
        isoComp-cong (pre-inverse ρ p ∙ isoComp-unitˡ-at (ρ ⁻¹ ▷ p))
          (idIso ((comp-unitˡ p) ⁻¹))

    abstract
      left-unit-identified : ExpressionIso left-unit (isomorphism-expression (section-frame ⁻¹))
      left-unit-identified = expressionIso-compose (isomorphism-cong left-unit-frame)
        (expressionIso-compose (isomorphism-retarget (s ◁ ρ ⁻¹)
          (comp-unitʳ s) ((comp-assoc s p s) ⁻¹))
          (retarget-expressionIso (isomorphism-post s (ρ ⁻¹))
            (comp-unitʳ s) ((comp-assoc s p s) ⁻¹)))

      right-unit-identified : ExpressionIso right-unit (isomorphism-expression (base-frame ⁻¹))
      right-unit-identified = expressionIso-compose (isomorphism-cong right-unit-frame)
        (expressionIso-compose (isomorphism-retarget (ρ ⁻¹ ▷ p)
          (comp-unitˡ p) (idIso ((p ∘ s) ∘ p)))
          (retarget-expressionIso (isomorphism-restrict (ρ ⁻¹) p)
            (comp-unitˡ p) (idIso ((p ∘ s) ∘ p))))

    module Normalized
      (on-section : ExpressionIso (retarget-expression left-counit section-frame (idIso s))
        (identity-expression s))
      (over-base : ExpressionIso (retarget-expression right-counit base-frame (idIso p))
        (identity-expression p)) where

      abstract
        left-counit-identified : ExpressionIso left-counit (isomorphism-expression section-frame)
        left-counit-identified = expressionIso-compose
          (isomorphism-cong (isoComp-unitˡ-at section-frame ∙
            isoComp-cong (inverse-identity s) (idIso section-frame)))
          (normalized-identity left-counit section-frame (idIso s) on-section)

        right-counit-identified : ExpressionIso right-counit (isomorphism-expression base-frame)
        right-counit-identified = expressionIso-compose
          (isomorphism-cong (isoComp-unitˡ-at base-frame ∙
            isoComp-cong (inverse-identity p) (idIso base-frame)))
          (normalized-identity right-counit base-frame (idIso p) over-base)

      abstract
        adjunction : Adjunction s p
        adjunction = record
          { unit = unit ; counit = ε
          ; left-triangle = expressionIso-compose (identification-right-inverse section-frame)
              (compose-expression-cong left-unit-identified left-counit-identified)
          ; right-triangle = expressionIso-compose (identification-right-inverse base-frame)
              (compose-expression-cong right-unit-identified right-counit-identified) }

        adjoint-section : LeftAdjointSection p s
        adjoint-section = record
          { adjunction = adjunction ; unit-invertible = identification-invertible (ρ ⁻¹) }

  module Right (η : MorphismExpression (id C) (s ∘ p)) where
    counit = isomorphism-expression ρ
    left-unit = retarget-expression (post-expression p η)
      (comp-unitʳ p) ((comp-assoc p s p) ⁻¹)
    left-counit = retarget-expression (restrict-expression counit p)
      (idIso ((p ∘ s) ∘ p)) (comp-unitˡ p)
    right-unit = retarget-expression (restrict-expression η s)
      (comp-unitˡ s) (idIso ((s ∘ p) ∘ s))
    right-counit = retarget-expression (post-expression s counit)
      ((comp-assoc s p s) ⁻¹) (comp-unitʳ s)

    abstract
      left-counit-frame :
        ((comp-unitˡ p ∙ (ρ ▷ p)) ∙ (idIso ((p ∘ s) ∘ p)) ⁻¹) =₂ base-frame
      left-counit-frame = isoComp-unitʳ-at base-frame ∙
        isoComp-cong (idIso base-frame) (inverse-identity ((p ∘ s) ∘ p))

      right-counit-frame :
        ((comp-unitʳ s ∙ (s ◁ ρ)) ∙ ((comp-assoc s p s) ⁻¹) ⁻¹) =₂ section-frame
      right-counit-frame = isoComp-assoc-at (comp-unitʳ s) (s ◁ ρ) (comp-assoc s p s) ∙
        isoComp-cong (idIso (comp-unitʳ s ∙ (s ◁ ρ))) (inverse-inverse (comp-assoc s p s))

    abstract
      left-counit-identified : ExpressionIso left-counit (isomorphism-expression base-frame)
      left-counit-identified = expressionIso-compose (isomorphism-cong left-counit-frame)
        (expressionIso-compose (isomorphism-retarget (ρ ▷ p)
          (idIso ((p ∘ s) ∘ p)) (comp-unitˡ p))
          (retarget-expressionIso (isomorphism-restrict ρ p)
            (idIso ((p ∘ s) ∘ p)) (comp-unitˡ p)))

      right-counit-identified : ExpressionIso right-counit (isomorphism-expression section-frame)
      right-counit-identified = expressionIso-compose (isomorphism-cong right-counit-frame)
        (expressionIso-compose (isomorphism-retarget (s ◁ ρ)
          ((comp-assoc s p s) ⁻¹) (comp-unitʳ s))
          (retarget-expressionIso (isomorphism-post s ρ)
            ((comp-assoc s p s) ⁻¹) (comp-unitʳ s)))

    module Normalized
      (over-base : ExpressionIso (retarget-expression left-unit (idIso p) base-frame)
        (identity-expression p))
      (on-section : ExpressionIso (retarget-expression right-unit (idIso s) section-frame)
        (identity-expression s)) where

      abstract
        left-unit-identified : ExpressionIso left-unit (isomorphism-expression (base-frame ⁻¹))
        left-unit-identified = expressionIso-compose
          (isomorphism-cong (isoComp-unitʳ-at (base-frame ⁻¹)))
          (normalized-identity left-unit (idIso p) base-frame over-base)

        right-unit-identified : ExpressionIso right-unit (isomorphism-expression (section-frame ⁻¹))
        right-unit-identified = expressionIso-compose
          (isomorphism-cong (isoComp-unitʳ-at (section-frame ⁻¹)))
          (normalized-identity right-unit (idIso s) section-frame on-section)

      abstract
        adjunction : Adjunction p s
        adjunction = record
          { unit = η ; counit = counit
          ; left-triangle = expressionIso-compose (identification-right-inverse base-frame)
              (compose-expression-cong left-unit-identified left-counit-identified)
          ; right-triangle = expressionIso-compose (identification-right-inverse section-frame)
              (compose-expression-cong right-unit-identified right-counit-identified) }

        adjoint-section : RightAdjointSection p s
        adjoint-section = record
          { adjunction = adjunction ; counit-invertible = identification-invertible ρ }
```
