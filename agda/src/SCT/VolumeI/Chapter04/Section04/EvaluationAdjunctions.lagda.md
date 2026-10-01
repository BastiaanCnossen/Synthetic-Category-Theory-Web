# The adjunctions of source and target evaluation

The constant-arrow functor is a right adjoint section of target evaluation
and a left adjoint section of source evaluation. Maximum supplies the unit
of the first adjunction; minimum supplies the counit of the second. Their
normalizations are comparisons of expressions, retaining both endpoints.
This proves `lem:Evaluation_Map_Is_Left_Reflector` in the absolute
theory, with Segal, square, and Rezk assumptions displayed explicitly.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.EvaluationAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformations as Deformations
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformationDiagrams as Diagrams
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationOverBase as OverBase
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalization as Transfer
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationSectionIdentity as Recognize

module At (C : CAT) where
  s : MAP C (Ar C)
  s = identityArrow
  module D = Deformations.At 𝒯 M ℱ P I E C using (target-unit; source-counit)
  module Diag = Diagrams.At 𝒯 M ℱ P I E C using (target-section-diagram; source-section-diagram)

  module Target where
    p : MAP (Ar C) C
    p = ev₁
    ρ : (p ∘ s) =₁ id C
    ρ = identity-target
    module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ
    module Unit = N.Right D.target-unit
    module T = Transfer.WithSection.Right 𝒯 M ℱ P I E p s ρ D.target-unit
    module B = OverBase.At.Maximum 𝒯 M ℱ P I E S Q R C using (over-base)

    abstract
      over-base : ExpressionIso T.over-base (identity-expression p)
      over-base = expressionIso-compose B.over-base
        (retarget-cong (post-expression p D.target-unit) (idIso (comp-unitʳ p))
          (isoComp-assoc-at (comp-unitˡ p) (ρ ▷ p) ((comp-assoc p s p) ⁻¹)))

    module Recognition = Recognize.At 𝒯 M ℱ P I E S Q R p ρ T.on-section Diag.target-section-diagram
    module SectionIdentity = Recognition.Evaluated (T.identity over-base)

    abstract
      normalized-base : ExpressionIso
        (retarget-expression Unit.left-unit (idIso p) N.base-frame) (identity-expression p)
      normalized-base = expressionIso-compose over-base
        (expressionIso-compose
          (retarget-cong (post-expression p D.target-unit)
            (isoComp-unitˡ-at (comp-unitʳ p)) (idIso (N.base-frame ∙ (comp-assoc p s p) ⁻¹)))
          (retarget-assoc (post-expression p D.target-unit)
            (comp-unitʳ p) ((comp-assoc p s p) ⁻¹) (idIso p) N.base-frame))

      normalized-section : ExpressionIso
        (retarget-expression Unit.right-unit (idIso s) N.section-frame) (identity-expression s)
      normalized-section = expressionIso-compose SectionIdentity.comparison
        (expressionIso-compose
          (retarget-cong (restrict-expression D.target-unit s)
            (isoComp-unitˡ-at (comp-unitˡ s)) (isoComp-unitʳ-at N.section-frame))
          (retarget-assoc (restrict-expression D.target-unit s)
            (comp-unitˡ s) (idIso ((s ∘ p) ∘ s)) (idIso s) N.section-frame))

    module Result = Unit.Normalized normalized-base normalized-section

    abstract
      adjunction : Adjunction p s
      adjunction = Result.adjunction

      adjoint-section : RightAdjointSection p s
      adjoint-section = Result.adjoint-section

  module Source where
    p : MAP (Ar C) C
    p = ev₀
    ρ : (p ∘ s) =₁ id C
    ρ = identity-source
    module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ
    module Counit = N.Left D.source-counit
    module T = Transfer.WithSection.Left 𝒯 M ℱ P I E p s ρ D.source-counit
    module B = OverBase.At.Minimum 𝒯 M ℱ P I E S Q R C using (over-base)

    abstract
      over-base : ExpressionIso T.over-base (identity-expression p)
      over-base = expressionIso-compose B.over-base
        (retarget-cong (post-expression p D.source-counit)
          (isoComp-assoc-at (comp-unitˡ p) (ρ ▷ p) ((comp-assoc p s p) ⁻¹))
          (idIso (comp-unitʳ p)))

    module Recognition = Recognize.At 𝒯 M ℱ P I E S Q R p ρ T.on-section Diag.source-section-diagram
    module SectionIdentity = Recognition.Evaluated (T.identity over-base)

    abstract
      normalized-section : ExpressionIso
        (retarget-expression Counit.left-counit N.section-frame (idIso s)) (identity-expression s)
      normalized-section = expressionIso-compose SectionIdentity.comparison
        (expressionIso-compose
          (retarget-cong (restrict-expression D.source-counit s)
            (isoComp-unitʳ-at N.section-frame) (isoComp-unitˡ-at (comp-unitˡ s)))
          (retarget-assoc (restrict-expression D.source-counit s)
            (idIso ((s ∘ p) ∘ s)) (comp-unitˡ s) N.section-frame (idIso s)))

      normalized-base : ExpressionIso
        (retarget-expression Counit.right-counit N.base-frame (idIso p)) (identity-expression p)
      normalized-base = expressionIso-compose over-base
        (expressionIso-compose
          (retarget-cong (post-expression p D.source-counit)
            (idIso (N.base-frame ∙ (comp-assoc p s p) ⁻¹)) (isoComp-unitˡ-at (comp-unitʳ p)))
          (retarget-assoc (post-expression p D.source-counit)
            ((comp-assoc p s p) ⁻¹) (comp-unitʳ p) N.base-frame (idIso p)))

    module Result = Counit.Normalized normalized-section normalized-base

    abstract
      adjunction : Adjunction s p
      adjunction = Result.adjunction

      adjoint-section : LeftAdjointSection p s
      adjoint-section = Result.adjoint-section

target-evaluation-adjunction : (C : CAT) → Adjunction (ev₁ {C}) identityArrow
target-evaluation-adjunction C = At.Target.adjunction C

source-evaluation-adjunction : (C : CAT) → Adjunction (identityArrow {C}) ev₀
source-evaluation-adjunction C = At.Source.adjunction C

target-evaluation-right-adjoint-section : (C : CAT) → RightAdjointSection (ev₁ {C}) identityArrow
target-evaluation-right-adjoint-section C = At.Target.adjoint-section C

source-evaluation-left-adjoint-section : (C : CAT) → LeftAdjointSection (ev₀ {C}) identityArrow
source-evaluation-left-adjoint-section C = At.Source.adjoint-section C

target-evaluation-left-localization : (C : CAT) → LeftBousfieldLocalization (ev₁ {C})
target-evaluation-left-localization C = record
  { section = identityArrow
  ; right-adjoint-section = target-evaluation-right-adjoint-section C }

source-evaluation-right-localization : (C : CAT) → RightBousfieldLocalization (ev₀ {C})
source-evaluation-right-localization C = record
  { section = identityArrow
  ; left-adjoint-section = source-evaluation-left-adjoint-section C }
```
