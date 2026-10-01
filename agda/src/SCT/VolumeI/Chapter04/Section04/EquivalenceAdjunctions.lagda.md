# Equivalences give adjunctions

An equivalence is left adjoint to any specified inverse with a section
identification. The unit is chosen with a prescribed image, so the
triangle equations follow from the normalized section frames. Both unit
and counit are invertible. This proves `prop:Equivalence_Is_Adjoint` and
`lem:Trivial_Fibrations_Are_Left_Reflectors`, without using Rezk or the
square axiom.

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

module SCT.VolumeI.Chapter04.Section04.EquivalenceAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-post; isomorphism-restrict; isomorphism-retarget; isomorphism-cong; isomorphism-id)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.PrimitiveInverses 𝒯 M ℱ P I E S
  using (identification-invertible; identification-right-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.EquivalenceSectionFrames as Frames
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized

module WithInverse {C D : CAT} (p : MAP C D) (ep : IsEquiv p)
  (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  module F = Frames.At 𝒯 p ep s ρ
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ
  χ = F.χ
  η = isomorphism-expression χ
  module Unit = N.Right η
  aa = N.section-frame
  vv = N.base-frame ∙ (comp-assoc p s p) ⁻¹

  abstract
    over-base : ExpressionIso
      (retarget-expression (post-expression p η) (comp-unitʳ p) vv)
      (identity-expression p)
    over-base = expressionIso-compose (isomorphism-id p)
      (expressionIso-compose
        (isomorphism-cong (isoComp-inverseʳ-at (comp-unitʳ p) ∙
          isoComp-cong F.base-triangle (idIso ((comp-unitʳ p) ⁻¹))))
        (expressionIso-compose (isomorphism-retarget (p ◁ χ) (comp-unitʳ p) vv)
          (retarget-expressionIso (isomorphism-post p χ) (comp-unitʳ p) vv)))

    on-section : ExpressionIso
      (retarget-expression (restrict-expression η s) (comp-unitˡ s) aa)
      (identity-expression s)
    on-section = expressionIso-compose (isomorphism-id s)
      (expressionIso-compose
        (isomorphism-cong (isoComp-inverseʳ-at (comp-unitˡ s) ∙
          isoComp-cong F.section-triangle (idIso ((comp-unitˡ s) ⁻¹))))
        (expressionIso-compose (isomorphism-retarget (χ ▷ s) (comp-unitˡ s) aa)
          (retarget-expressionIso (isomorphism-restrict χ s) (comp-unitˡ s) aa)))

    normalized-base : ExpressionIso
      (retarget-expression Unit.left-unit (idIso p) N.base-frame) (identity-expression p)
    normalized-base = expressionIso-compose over-base
      (expressionIso-compose
        (retarget-cong (post-expression p η)
          (isoComp-unitˡ-at (comp-unitʳ p)) (idIso vv))
        (retarget-assoc (post-expression p η)
          (comp-unitʳ p) ((comp-assoc p s p) ⁻¹) (idIso p) N.base-frame))

    normalized-section : ExpressionIso
      (retarget-expression Unit.right-unit (idIso s) N.section-frame) (identity-expression s)
    normalized-section = expressionIso-compose on-section
      (expressionIso-compose
        (retarget-cong (restrict-expression η s)
          (isoComp-unitˡ-at (comp-unitˡ s)) (isoComp-unitʳ-at N.section-frame))
        (retarget-assoc (restrict-expression η s)
          (comp-unitˡ s) (idIso ((s ∘ p) ∘ s)) (idIso s) N.section-frame))

  module Result = Unit.Normalized normalized-base normalized-section

  abstract
    adjunction : Adjunction p s
    adjunction = record
      { unit = η ; counit = isomorphism-expression ρ
      ; left-triangle = expressionIso-compose (identification-right-inverse N.base-frame)
          (compose-expression-cong Result.left-unit-identified Unit.left-counit-identified)
      ; right-triangle = expressionIso-compose (identification-right-inverse N.section-frame)
          (compose-expression-cong Result.right-unit-identified Unit.right-counit-identified) }

    unit-invertible : IsInvertibleExpression (Adjunction.unit adjunction)
    unit-invertible = identification-invertible χ

    counit-invertible : IsInvertibleExpression (Adjunction.counit adjunction)
    counit-invertible = identification-invertible ρ

    right-adjoint-section : RightAdjointSection p s
    right-adjoint-section = record
      { adjunction = adjunction ; counit-invertible = counit-invertible }

    left-adjoint-section : LeftAdjointSection s p
    left-adjoint-section = record
      { adjunction = adjunction ; unit-invertible = unit-invertible }

equivalence-adjunction : {C D : CAT} (p : MAP C D) (ep : IsEquiv p) →
  Adjunction p (IsEquiv.inverse ep)
equivalence-adjunction p ep = WithInverse.adjunction p ep (IsEquiv.inverse ep) ((IsEquiv.retractionIso ep) ⁻¹)

equivalence-right-adjoint-section : {C D : CAT} (p : MAP C D) (ep : IsEquiv p) →
  RightAdjointSection p (IsEquiv.inverse ep)
equivalence-right-adjoint-section p ep = WithInverse.right-adjoint-section p ep
  (IsEquiv.inverse ep) ((IsEquiv.retractionIso ep) ⁻¹)

equivalence-left-adjoint-section : {C D : CAT} (p : MAP C D) (ep : IsEquiv p) →
  LeftAdjointSection p (IsEquiv.inverse ep)
equivalence-left-adjoint-section p ep = WithInverse.left-adjoint-section
  (IsEquiv.inverse ep) (equiv-inverse ep) p ((IsEquiv.sectionIso ep) ⁻¹)

equivalence-left-localization : {C D : CAT} (p : MAP C D) → IsEquiv p → LeftBousfieldLocalization p
equivalence-left-localization p ep = record
  { section = IsEquiv.inverse ep ; right-adjoint-section = equivalence-right-adjoint-section p ep }

equivalence-right-localization : {C D : CAT} (p : MAP C D) → IsEquiv p → RightBousfieldLocalization p
equivalence-right-localization p ep = record
  { section = IsEquiv.inverse ep ; left-adjoint-section = equivalence-left-adjoint-section p ep }
```
