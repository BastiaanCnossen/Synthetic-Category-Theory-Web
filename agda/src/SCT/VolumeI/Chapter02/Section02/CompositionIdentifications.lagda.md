# Composition acts on identifications with fixed endpoints

The identifications of the two input arrows give a comparison of their
composable-pair cones. Lift it through the Segal equivalence with its
short-edge images prescribed. The endpoint equations of the input
identifications then extend across the outer vertices of the triangles.

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

module SCT.VolumeI.Chapter02.Section02.CompositionIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.TriangleComparisons 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.UniversalConeLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (quotient-square)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

pair-identification : {Γ C : CAT} {x y z : MAP Γ C}
  {f f′ : MorphismExpression x y} {g g′ : MorphismExpression y z} →
  ExpressionIso f f′ → ExpressionIso g g′ →
  ConeIso (expression-pair f g) (expression-pair f′ g′)
pair-identification {y = y} {f = f} {f′} {g} {g′} α β = record
  { leftIso = ExpressionIso.comparison α
  ; rightIso = ExpressionIso.comparison β
  ; compatible = quotient-square
      (MorphismExpression.target-frame f) (MorphismExpression.source-frame g)
      (MorphismExpression.target-frame f′) (MorphismExpression.source-frame g′)
      (ev₁ ◁ ExpressionIso.comparison α) (ev₀ ◁ ExpressionIso.comparison β) (idIso y)
      ((isoComp-unitˡ-at (MorphismExpression.target-frame f)) ⁻¹ ∙ ExpressionIso.target-compatible α)
      ((isoComp-unitˡ-at (MorphismExpression.source-frame g)) ⁻¹ ∙ ExpressionIso.source-compatible β) }

module ComposeIdentification {Γ C : CAT} {x y z : MAP Γ C}
  {f f′ : MorphismExpression x y} {g g′ : MorphismExpression y z}
  (α : ExpressionIso f f′) (β : ExpressionIso g g′) where
  module Before = Complete (expression-pair f g)
  module After = Complete (expression-pair f′ g′)
  pair-comparison = pair-identification α β
  short-comparison = coneIso-compose (coneIso-inverse After.short-edges)
    (coneIso-compose pair-comparison Before.short-edges)
  module Lift = UniversalLift (triangle-cone C) (SegalAxiom.segal-isPullback S C)
    Before.triangle After.triangle short-comparison
  δ = Lift.lift

  endpoint : (v : MAP (Ar C) C) (e : MAP (Triangles C) (Ar C))
    (ν : (v ∘ edge₁) =₁ (v ∘ e)) {u u′ : MAP Γ (Ar C)} {w : MAP Γ C}
    (p : (e ∘ Before.triangle) =₁ u) (q : (e ∘ After.triangle) =₁ u′)
    (d : u =₁ u′) (s : (v ∘ u) =₁ w) (t : (v ∘ u′) =₁ w) →
    (e ◁ δ) =₂ (q ⁻¹ ∙ (d ∙ p)) → (t ∙ (v ◁ d)) =₂ s →
    let corner : Cone v v (Triangles C)
        corner = record { left = edge₁ ; right = e ; match = ν }
        before = Cone.match (conePre Before.triangle corner)
        after = Cone.match (conePre After.triangle corner)
    in ((t ∙ ((v ◁ q) ∙ after)) ∙ (v ◁ (edge₁ ◁ δ))) =₂
      (s ∙ ((v ◁ p) ∙ before))
  endpoint v e ν p q d s t image compatible =
    isoComp-assoc-at s (v ◁ p) before ∙
    (VertexFrame.extend δ v e ν (s ∙ (v ◁ p)) (t ∙ (v ◁ q)) edge-compatible ∙
      isoComp-cong ((isoComp-assoc-at t (v ◁ q) after) ⁻¹) (idIso (v ◁ (edge₁ ◁ δ))))
    where
    corner : Cone v v (Triangles C)
    corner = record { left = edge₁ ; right = e ; match = ν }
    before = Cone.match (conePre Before.triangle corner)
    after = Cone.match (conePre After.triangle corner)

    edge-image : (q ∙ (e ◁ δ)) =₂ (d ∙ p)
    edge-image = cancel-inverse q (d ∙ p) ∙ isoComp-cong (idIso q) image

    projected : ((v ◁ q) ∙ (v ◁ (e ◁ δ))) =₂ ((v ◁ d) ∙ (v ◁ p))
    projected = postWhisker-isoComp-at v d p ∙
      ((postWhisker v ◁ edge-image) ∙ (postWhisker-isoComp-at v q (e ◁ δ)) ⁻¹)

    edge-compatible : ((t ∙ (v ◁ q)) ∙ (v ◁ (e ◁ δ))) =₂ (s ∙ (v ◁ p))
    edge-compatible = isoComp-cong compatible (idIso (v ◁ p)) ∙
      ((isoComp-assoc-at t (v ◁ d) (v ◁ p)) ⁻¹ ∙
        (isoComp-cong (idIso t) projected ∙ isoComp-assoc-at t (v ◁ q) (v ◁ (e ◁ δ))))

  comparison : ExpressionIso (compose-expression f g) (compose-expression f′ g′)
  comparison = record
    { comparison = edge₁ ◁ δ
    ; source-compatible = endpoint ev₀ edge₂ (Completion.source-vertex C)
        (ConeIso.leftIso Before.short-edges) (ConeIso.leftIso After.short-edges)
        (ExpressionIso.comparison α) (MorphismExpression.source-frame f) (MorphismExpression.source-frame f′)
        Lift.left-image (ExpressionIso.source-compatible α)
    ; target-compatible = endpoint ev₁ edge₀ (Completion.target-vertex C)
        (ConeIso.rightIso Before.short-edges) (ConeIso.rightIso After.short-edges)
        (ExpressionIso.comparison β) (MorphismExpression.target-frame g) (MorphismExpression.target-frame g′)
        Lift.right-image (ExpressionIso.target-compatible β) }

compose-expression-cong : {Γ C : CAT} {x y z : MAP Γ C}
  {f f′ : MorphismExpression x y} {g g′ : MorphismExpression y z} →
  ExpressionIso f f′ → ExpressionIso g g′ →
  ExpressionIso (compose-expression f g) (compose-expression f′ g′)
compose-expression-cong = ComposeIdentification.comparison
```
