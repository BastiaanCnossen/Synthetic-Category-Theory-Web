# Normalized deformations as transformations over the base

The normalized base equation can be flattened into the native relative
transformation interface. This retains the section identification and
both endpoint frames, and supplies its interval diagram over the base.
Normalization on the section is a separate condition.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedRelativeDeformations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagrams as Diagrams

module WithSection {C D : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ using (base-frame; module Left; module Right)
  source-frame : (p ∘ (s ∘ p)) =₁ p
  source-frame = N.base-frame ∙ (comp-assoc p s p) ⁻¹
  section-composite : FunctorOver p p
  section-composite = record { lift = s ∘ p ; comparison = source-frame }

  module Left (ε : MorphismExpression (s ∘ p) (id C)) where
    module Old = N.Left ε using (right-counit)
    NormalizedOver : Set m
    NormalizedOver = ExpressionIso
      (retarget-expression Old.right-counit N.base-frame (idIso p)) (identity-expression p)

    abstract
      flatten : ExpressionIso
        (retarget-expression Old.right-counit N.base-frame (idIso p))
        (retarget-expression (post-expression p ε) source-frame (comp-unitʳ p))
      flatten = expressionIso-compose
        (retarget-cong (post-expression p ε) (idIso source-frame) (isoComp-unitˡ-at (comp-unitʳ p)))
        (retarget-assoc (post-expression p ε) ((comp-assoc p s p) ⁻¹) (comp-unitʳ p)
          N.base-frame (idIso p))

      over-base : NormalizedOver → Over.IsOver p p section-composite (identity-over p) ε
      over-base given = expressionIso-compose given (expressionIso-inverse flatten)

    module WithOver (given : NormalizedOver) where
      value : Over.MorphismOver p p section-composite (identity-over p)
      value = record { underlying = ε ; over-base = over-base given }
      module Diagram = Diagrams.Diagram 𝒯 M ℱ P I E S value using (family; module Source; module Target)

  module Right (η : MorphismExpression (id C) (s ∘ p)) where
    module Old = N.Right η using (left-unit)
    NormalizedOver : Set m
    NormalizedOver = ExpressionIso
      (retarget-expression Old.left-unit (idIso p) N.base-frame) (identity-expression p)

    abstract
      flatten : ExpressionIso
        (retarget-expression Old.left-unit (idIso p) N.base-frame)
        (retarget-expression (post-expression p η) (comp-unitʳ p) source-frame)
      flatten = expressionIso-compose
        (retarget-cong (post-expression p η) (isoComp-unitˡ-at (comp-unitʳ p)) (idIso source-frame))
        (retarget-assoc (post-expression p η) (comp-unitʳ p) ((comp-assoc p s p) ⁻¹)
          (idIso p) N.base-frame)

      over-base : NormalizedOver → Over.IsOver p p (identity-over p) section-composite η
      over-base given = expressionIso-compose given (expressionIso-inverse flatten)

    module WithOver (given : NormalizedOver) where
      value : Over.MorphismOver p p (identity-over p) section-composite
      value = record { underlying = η ; over-base = over-base given }
      module Diagram = Diagrams.Diagram 𝒯 M ℱ P I E S value using (family; module Source; module Target)
```
