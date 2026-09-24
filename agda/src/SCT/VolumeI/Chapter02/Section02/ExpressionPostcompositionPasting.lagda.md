# Successive postcomposition with specified endpoints

Uncurry the original expression, compare the postcomposed diagrams,
and curry again. The endpoint changes are precisely those prescribed
by the given comparison of functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.ExpressionPostcompositionPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
import SCT.VolumeI.Chapter02.Section02.CurryPostcomposition as CurriedPost
import SCT.VolumeI.Chapter02.Section02.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter02.Section02.PostcompositionDiagramFrames as Frames

module Curried {Γ B A D : CAT} (r : MAP B A) (s : MAP A D) (t : MAP B D)
  (η : (s ∘ r) =₁ t) {x y : MAP Γ B}
  (H : MAP (Γ × [1]) B) (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y) where
  module First = CurriedPost.At 𝒯 M ℱ P I E r H p q
  module Second = CurriedPost.At 𝒯 M ℱ P I E s (r ∘ H)
    ((r ◁ p) ∙ comp-assoc (insert zero) H r)
    ((r ◁ q) ∙ comp-assoc (insert one) H r)
  module Last = CurriedPost.At 𝒯 M ℱ P I E t H p q
  module Source = Frames.At 𝒯 (insert zero) H r s t η p
  module Target = Frames.At 𝒯 (insert one) H r s t η q
  module Diagram = Diagrams.At 𝒯 M ℱ P I E (s ∘ (r ∘ H)) (t ∘ H) Source.diagram
    (Source.change ∙ Source.twice) (Target.change ∙ Target.twice)
    Source.output Target.output Source.comparison Target.comparison

  comparison : ExpressionIso
    (retarget-expression (post-expression s (post-expression r (expression H p q)))
      Source.change Target.change)
    (post-expression t (expression H p q))
  comparison = expressionIso-compose (expressionIso-inverse Last.comparison)
    (expressionIso-compose Diagram.comparison
      (expressionIso-compose
        (Diagrams.retarget-curried 𝒯 M ℱ P I E (s ∘ (r ∘ H)) Source.twice Target.twice Source.change Target.change)
        (retarget-expressionIso
          (expressionIso-compose Second.comparison (post-expressionIso s First.comparison))
          Source.change Target.change)))

module At {Γ B A D : CAT} (r : MAP B A) (s : MAP A D) (t : MAP B D)
  (η : (s ∘ r) =₁ t) {x y : MAP Γ B} (f : MorphismExpression x y) where
  module Recover = Diagrams.Recovery 𝒯 M ℱ P I E f
  module Compared = Curried r s t η Recover.H Recover.p Recover.q
  source-change = (η ▷ x) ∙ (comp-assoc x r s) ⁻¹
  target-change = (η ▷ y) ∙ (comp-assoc y r s) ⁻¹

  comparison : ExpressionIso
    (retarget-expression (post-expression s (post-expression r f)) source-change target-change)
    (post-expression t f)
  comparison = expressionIso-compose (post-expressionIso t (expressionIso-inverse Recover.comparison))
    (expressionIso-compose Compared.comparison
      (retarget-expressionIso (post-expressionIso s (post-expressionIso r Recover.comparison))
        source-change target-change))
```
