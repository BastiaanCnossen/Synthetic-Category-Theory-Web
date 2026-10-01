# The two composites across a square

Restricting a square to its two triangles presents its diagonal in two
ways. The six endpoint cone comparisons retain all three vertices of
each presentation. Segal uniqueness therefore compares the two composites
with their specified source and target.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.SquareCompositePresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E using (j₀; j₁; diagonal)
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareBoundaryCones as Boundaries

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) where
  module B = Boundaries.At 𝒯 M ℱ P I E W
    using (module LowerMiddle; module LowerSource; module LowerTarget; module UpperMiddle; module UpperSource; module UpperTarget)
  vertex : Obj-abs [1] → Obj-abs [1] → MAP Γ C
  vertex u v = evaluate (pair u v) ∘ W

  top : MorphismExpression (vertex zero zero) (vertex zero one)
  top = record { arrow = funPre (coinsert zero) ∘ W
    ; source-frame = B.UpperSource.Framing.Restricted.right-frame
    ; target-frame = B.UpperMiddle.Framing.Restricted.left-frame }
  right : MorphismExpression (vertex zero one) (vertex one one)
  right = record { arrow = funPre (insert one) ∘ W
    ; source-frame = B.UpperMiddle.Framing.Restricted.right-frame
    ; target-frame = B.UpperTarget.Framing.Restricted.right-frame }
  left : MorphismExpression (vertex zero zero) (vertex one zero)
  left = record { arrow = funPre (insert zero) ∘ W
    ; source-frame = B.LowerSource.Framing.Restricted.right-frame
    ; target-frame = B.LowerMiddle.Framing.Restricted.left-frame }
  bottom : MorphismExpression (vertex one zero) (vertex one one)
  bottom = record { arrow = funPre (coinsert one) ∘ W
    ; source-frame = B.LowerMiddle.Framing.Restricted.right-frame
    ; target-frame = B.LowerTarget.Framing.Restricted.right-frame }
  diagonal-expression : MorphismExpression (vertex zero zero) (vertex one one)
  diagonal-expression = record { arrow = funPre diagonal ∘ W
    ; source-frame = B.UpperSource.Framing.Restricted.left-frame
    ; target-frame = B.UpperTarget.Framing.Restricted.left-frame }

  upper-middle = coneIso-inverse B.UpperMiddle.comparison
  upper-source = coneIso-inverse B.UpperSource.comparison
  upper-target = coneIso-inverse B.UpperTarget.comparison
  lower-middle = coneIso-inverse B.LowerMiddle.comparison
  lower-source = coneIso-inverse B.LowerSource.comparison
  lower-target = coneIso-inverse B.LowerTarget.comparison
  module Upper = Vertices top right diagonal-expression (funPre j₀ ∘ W)
    (ConeIso.leftIso upper-middle) (ConeIso.rightIso upper-middle) (ConeIso.leftIso upper-source)
    using (presentation)
  module Lower = Vertices left bottom diagonal-expression (funPre j₁ ∘ W)
    (ConeIso.leftIso lower-middle) (ConeIso.rightIso lower-middle) (ConeIso.leftIso lower-source)
    using (presentation)

  upper : CompositePresentation top right diagonal-expression
  upper = Upper.presentation (ConeIso.compatible upper-middle)
    (ConeIso.compatible upper-source) (ConeIso.compatible upper-target)
  lower : CompositePresentation left bottom diagonal-expression
  lower = Lower.presentation (ConeIso.compatible lower-middle)
    (ConeIso.compatible lower-source) (ConeIso.compatible lower-target)

  commutes : ExpressionIso (compose-expression top right) (compose-expression left bottom)
  commutes = expressionIso-compose (expressionIso-inverse (recognize-composite lower))
    (recognize-composite upper)
```
