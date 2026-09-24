# Left-inverse triangles and composition

Fix the first edge of a triangle. Segal and pullback pasting identify
the remaining data with an arrow starting at its target. Under this
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

module SCT.VolumeI.Chapter02.Section03.LeftTriangleAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
  using (coneSwap; coneSwap-swap; coneSwap-pre; coneIso-swap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConePasting 𝒯 using (compositeCone)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter02.Section03.UniversalInverseExpressions 𝒯 M ℱ P I E S using (IsInvertibleExpression)
import SCT.VolumeI.Chapter02.Section03.SourceCompositionCones as Actions
import SCT.VolumeI.Chapter02.Section03.SourceCompositionEquivalence as Equivalence
import SCT.VolumeI.Chapter02.Section03.ConeOperations as Operations

module At {B C : CAT} (f : MAP B (Ar C)) where
  arrow : MorphismExpression (ev₀ ∘ f) (ev₁ ∘ f)
  arrow = record { arrow = f ; source-frame = idIso (ev₀ ∘ f) ; target-frame = idIso (ev₁ ∘ f) }

  T = Pullback f (edge₂ {C})
  triangle : MAP T (Triangles C)
  triangle = pullback₂
  base : MAP T B
  base = pullback₁

  private
    raw = pullbackCone f (edge₂ {C})
    swapped-segal = triangle-cone C
    module Paste = Pasting f ev₁ ev₀ swapped-segal
      (Segal.SegalAxiom.segal-isPullback S C)
    outer = Paste.Paste.flatten raw

  input-cone : Cone (ev₀ {C}) (ev₁ ∘ f) T
  input-cone = coneSwap outer

  input-isPullback : IsPullback input-cone
  input-isPullback = pullback-swap outer
    (Paste.paste-isPullback raw (pullbackCone-isPullback f edge₂))

  private
    module Action = Actions.Action 𝒯 M ℱ P I E S arrow
    first = Action.input input-cone
    second = restrict-expression arrow base
    pair-cone = expression-pair second first
    u = comp-assoc base f ev₁
    n = Cone.match outer

    normalized-pair : Cone.match (compositeCone f ev₁ outer) =₂ Cone.match pair-cone
    normalized-pair = isoComp-cong ((inverse-inverse n) ⁻¹)
      ((isoComp-unitˡ-at (u ⁻¹) ∙
        isoComp-cong (preWhisker-idIso (ev₁ ∘ f) base) (idIso (u ⁻¹))) ⁻¹)

    pair-comparison : ConeIso (compositeCone f ev₁ outer) pair-cone
    pair-comparison = cone-match-change _ _ _ _ normalized-pair

    short-edges : ConeIso (conePre triangle (triangle-cone C)) pair-cone
    short-edges = coneIso-compose pair-comparison
      (coneIso-inverse (Paste.Paste.flatten-composite raw))

    presented = presented-expression second first triangle short-edges
    long-comparison : ExpressionIso (Action.composite input-cone) presented
    long-comparison = retarget-expressionIso
      (Compare.long-comparison pair-cone (Complete.triangle pair-cone) triangle
        (Complete.short-edges pair-cone) short-edges)
      (MorphismExpression.source-frame second) (MorphismExpression.target-frame first)

  long-cone : Cone (ev₀ {C}) (ev₀ ∘ f) T
  long-cone = record { left = edge₁ ∘ triangle ; right = base
    ; match = MorphismExpression.source-frame presented }

  private
    long-cone-comparison : ConeIso (Action.act input-cone) long-cone
    long-cone-comparison = record
      { leftIso = ExpressionIso.comparison long-comparison ; rightIso = idIso base
      ; compatible =
          (isoComp-unitˡ-at (Cone.match (Action.act input-cone)) ∙
            isoComp-cong (postWhisker-idIso (ev₀ ∘ f) base) (idIso (Cone.match (Action.act input-cone)))) ⁻¹ ∙
          ExpressionIso.source-compatible long-comparison }

    module ActionFunctor = Equivalence.At 𝒯 M ℱ P I E S Q arrow
    module Realized = Operations.Realize 𝒯 P (Equivalence.operation 𝒯 M ℱ P I E S Q arrow)

  long-isPullback : IsInvertibleExpression arrow → IsPullback long-cone
  long-isPullback inverse-data = pullback-cone-invariant long-cone-comparison
    (Realized.preserves-pullback (ActionFunctor.compose-at-source-isEquiv inverse-data)
      input-cone input-isPullback)
```
