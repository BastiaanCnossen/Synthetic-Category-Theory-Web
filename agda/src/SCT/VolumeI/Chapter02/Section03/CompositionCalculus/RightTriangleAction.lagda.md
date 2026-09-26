# Right-inverse triangles and composition

Fix the second edge of a triangle. Segal and pullback pasting identify
the remaining data with an arrow ending at its source. Under this
identification the long edge is composition with the fixed arrow. When
that arrow is invertible, the resulting long-edge cone is a pullback.

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

module SCT.VolumeI.Chapter02.Section03.CompositionCalculus.RightTriangleAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneSwap-swap; coneSwap-pre; coneIso-swap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (compositeCone)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UniversalInverseExpressions 𝒯 M ℱ P I E S using (IsInvertibleExpression)
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.TargetCompositionCones as Actions
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.TargetCompositionEquivalence as Equivalence
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Operations as Operations

module At {B C : CAT} (f : MAP B (Ar C)) where
  arrow : MorphismExpression (ev₀ ∘ f) (ev₁ ∘ f)
  arrow = record { arrow = f ; source-frame = idIso (ev₀ ∘ f) ; target-frame = idIso (ev₁ ∘ f) }

  T = Pullback f (edge₀ {C})
  triangle : MAP T (Triangles C)
  triangle = pullback₂
  base : MAP T B
  base = pullback₁

  private
    raw = pullbackCone f (edge₀ {C})
    swapped-segal = coneSwap (triangle-cone C)
    module Paste = Pasting f ev₀ ev₁ swapped-segal
      (pullback-swap (triangle-cone C) (Segal.SegalAxiom.segal-isPullback S C))
    outer = Paste.Paste.flatten raw

  input-cone : Cone (ev₁ {C}) (ev₀ ∘ f) T
  input-cone = coneSwap outer

  input-isPullback : IsPullback input-cone
  input-isPullback = pullback-swap outer
    (Paste.paste-isPullback raw (pullbackCone-isPullback f edge₀))

  private
    module Action = Actions.Action 𝒯 M ℱ P I E S arrow
    first = Action.input input-cone
    second = restrict-expression arrow base
    pair-cone = expression-pair first second
    u = comp-assoc base f ev₀
    n = Cone.match outer

    normalized-pair : Cone.match (coneSwap (compositeCone f ev₀ outer)) =₂ Cone.match pair-cone
    normalized-pair =
      isoComp-cong (＝-inv ◁
        ((isoComp-unitˡ-at (u ⁻¹) ∙ isoComp-cong (preWhisker-idIso (ev₀ ∘ f) base) (idIso (u ⁻¹))) ⁻¹))
        (idIso (n ⁻¹)) ∙
      inverse-composite n (u ⁻¹)

    pair-comparison : ConeIso (coneSwap (compositeCone f ev₀ outer)) pair-cone
    pair-comparison = cone-match-change _ _ _ _ normalized-pair

    short-edges : ConeIso (conePre triangle (triangle-cone C)) pair-cone
    short-edges = coneIso-compose pair-comparison
      (coneIso-compose (coneIso-inverse (coneIso-swap (Paste.Paste.flatten-composite raw)))
        (coneIso-compose (coneIso-inverse (coneIso-swap (coneSwap-pre triangle (triangle-cone C))))
          (coneIso-inverse (coneSwap-swap (conePre triangle (triangle-cone C))))))

    presented = presented-expression first second triangle short-edges
    long-comparison : ExpressionIso (Action.composite input-cone) presented
    long-comparison = retarget-expressionIso
      (Compare.long-comparison pair-cone (Complete.triangle pair-cone) triangle
        (Complete.short-edges pair-cone) short-edges)
      (MorphismExpression.source-frame first) (MorphismExpression.target-frame second)

  long-cone : Cone (ev₁ {C}) (ev₁ ∘ f) T
  long-cone = record { left = edge₁ ∘ triangle ; right = base
    ; match = MorphismExpression.target-frame presented }

  private
    long-cone-comparison : ConeIso (Action.act input-cone) long-cone
    long-cone-comparison = record
      { leftIso = ExpressionIso.comparison long-comparison ; rightIso = idIso base
      ; compatible =
          (isoComp-unitˡ-at (Cone.match (Action.act input-cone)) ∙
            isoComp-cong (postWhisker-idIso (ev₁ ∘ f) base) (idIso (Cone.match (Action.act input-cone)))) ⁻¹ ∙
          ExpressionIso.target-compatible long-comparison }

    module ActionFunctor = Equivalence.At 𝒯 M ℱ P I E S Q arrow
    module Realized = Operations.Realize 𝒯 P (Equivalence.operation 𝒯 M ℱ P I E S Q arrow)

  long-isPullback : IsInvertibleExpression arrow → IsPullback long-cone
  long-isPullback inverse-data = pullback-cone-invariant long-cone-comparison
    (Realized.preserves-pullback (ActionFunctor.compose-at-target-isEquiv inverse-data)
      input-cone input-isPullback)
```
