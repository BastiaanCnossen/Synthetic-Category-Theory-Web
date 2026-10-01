# Expressions built from the global composition functor

An input pair first maps to `Composable C` and then through `compose C`.
The source and target use exactly `Completion.compose-source` and
`Completion.compose-target`, followed by the input cone's beta comparisons.
The comparison with `compose-expression` preserves both of these frames.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GlobalCompositionExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.CompositionEndpointComparison as Endpoints
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P

module Pair {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) where
  t = expression-pair f g
  module F = MorphismExpression f
  module G = MorphismExpression g
    using (target-frame)
  module Boundary = Endpoints.At 𝒯 M ℱ P I E S t
    using (source-comparison; target-comparison; module Source; module Target)

  value : MorphismExpression x z
  value = record
    { arrow = compose C ∘ pullbackLift t
    ; source-frame = F.source-frame ∙ Boundary.Source.restricted-global
    ; target-frame = G.target-frame ∙ Boundary.Target.restricted-global }

  comparison : ExpressionIso value (compose-expression f g)
  comparison = record
    { comparison = Complete.composition-comparison t
    ; source-compatible = isoComp-cong (idIso F.source-frame) Boundary.source-comparison ∙
        isoComp-assoc-at F.source-frame (Complete.source-boundary t)
          (ev₀ ◁ Complete.composition-comparison t)
    ; target-compatible = isoComp-cong (idIso G.target-frame) Boundary.target-comparison ∙
        isoComp-assoc-at G.target-frame (Complete.target-boundary t)
          (ev₁ ◁ Complete.composition-comparison t) }

global-compose-expression : {Γ C : CAT} {x y z : MAP Γ C} →
  MorphismExpression x y → MorphismExpression y z → MorphismExpression x z
global-compose-expression = Pair.value

global-composition-comparison : {Γ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) →
  ExpressionIso (global-compose-expression f g) (compose-expression f g)
global-composition-comparison = Pair.comparison
```
