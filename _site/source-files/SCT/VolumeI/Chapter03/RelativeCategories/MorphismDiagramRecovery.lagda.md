# Recovery of a relative transformation's underlying expression

Passing to an interval diagram and back recovers the underlying
transformation, with both endpoint frames. This statement does not assert
an identification of the witnesses that the transformations lie over the
base; that requires a further comparison.

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

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagramRecovery
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagrams as Diagrams
import SCT.VolumeI.Chapter03.RelativeCategories.DiagramMorphisms as Morphisms
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Recovery

module Roundtrip {C D B : CAT} {p : MAP C B} {q : MAP D B} {u v : FunctorOver p q}
  (α : Over.MorphismOver p q u v) where
  module Diagram = Diagrams.Diagram 𝒯 M ℱ P I E S α
  module Recovered = Morphisms.FromDiagram.WithEndpoints 𝒯 M ℱ P I E S
    Diagram.family u v Diagram.Source.comparison Diagram.Target.comparison
  module Raw = Recovery.Recovery 𝒯 M ℱ P I E (Over.MorphismOver.underlying α)

  abstract
    frames : ExpressionIso Raw.result Recovered.underlying
    frames = record
      { comparison = idIso (funCurry Diagram.H)
      ; source-compatible =
          isoComp-cong Diagram.Source.underlying-comparison (idIso (evaluate-curry zero Diagram.H)) ∙
          isoComp-unitʳ-at (MorphismExpression.source-frame Recovered.underlying) ∙
          isoComp-cong (idIso (MorphismExpression.source-frame Recovered.underlying))
            (postWhisker-idIso ev₀ (funCurry Diagram.H))
      ; target-compatible =
          isoComp-cong Diagram.Target.underlying-comparison (idIso (evaluate-curry one Diagram.H)) ∙
          isoComp-unitʳ-at (MorphismExpression.target-frame Recovered.underlying) ∙
          isoComp-cong (idIso (MorphismExpression.target-frame Recovered.underlying))
            (postWhisker-idIso ev₁ (funCurry Diagram.H)) }

    underlying-comparison : ExpressionIso (Over.MorphismOver.underlying α) Recovered.underlying
    underlying-comparison = expressionIso-compose frames Raw.comparison
```
