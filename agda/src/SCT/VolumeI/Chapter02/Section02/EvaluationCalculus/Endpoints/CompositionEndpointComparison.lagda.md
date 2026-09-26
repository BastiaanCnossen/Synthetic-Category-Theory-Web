# The global composition has the specified expression endpoints

The associator comparing the chosen global composition with completion
of an input cone also preserves the prescribed source and target paths.
The short-edge computation is shared; each outer vertex is then a pasting
of projection witnesses.

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

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.CompositionEndpointComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (compose-base; lift-base; lift-compose; associator-square)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.CompositionShortEdges as Edges
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P

module At {Γ C : CAT} (t : Cone (ev₁ {C}) ev₀ Γ) where
  module Short = Edges.At 𝒯 M ℱ P I E S t
  j = completeTriangle C
  k = pullbackLift t
  h = edge₁ {C}
  β = pullbackLift-β t

  module Endpoint (v : MAP (Ar C) C) (e : MAP (Triangles C) (Ar C))
    (vertex : (v ∘ h) =₁ (v ∘ e))
    (r : MAP (Composable C) (Ar C)) (p : MAP Γ (Ar C))
    (short : (e ∘ j) =₁ r) (input : (r ∘ k) =₁ p)
    (completed : (e ∘ (j ∘ k)) =₁ p)
    (short-image : completed =₂ compose-base e j short k input) where

    Lⱼ = lift-base v e j short
    Lₖ = lift-base v r k input
    vertex-frame = (vertex ▷ j) ∙ (comp-assoc j h v) ⁻¹
    global-frame = (v ◁ short) ∙ (comp-assoc j e v ∙ vertex-frame)
    complete-frame = (v ◁ completed) ∙
      (comp-assoc (j ∘ k) e v ∙ ((vertex ▷ (j ∘ k)) ∙ (comp-assoc (j ∘ k) h v) ⁻¹))
    restricted-global = (v ◁ input) ∙
      (comp-assoc k r v ∙ ((global-frame ▷ k) ∙ (comp-assoc k (h ∘ j) v) ⁻¹))
    nested = compose-base v (h ∘ j) (compose-base v h vertex j Lⱼ) k Lₖ
    combined = compose-base v h vertex (j ∘ k) (compose-base (v ∘ e) j Lⱼ k Lₖ)

    abstract
      global-normalization : nested =₂ restricted-global
      global-normalization =
        isoComp-assoc-at (v ◁ input) (comp-assoc k r v)
          ((global-frame ▷ k) ∙ (comp-assoc k (h ∘ j) v) ⁻¹) ∙
        isoComp-cong (idIso Lₖ)
          (isoComp-cong (preWhisker k ◁ isoComp-assoc-at (v ◁ short) (comp-assoc j e v) vertex-frame)
            (idIso ((comp-assoc k (h ∘ j) v) ⁻¹)))

      complete-normalization : complete-frame =₂ combined
      complete-normalization =
        isoComp-cong ((lift-compose v e j k short input) ⁻¹)
          (idIso ((vertex ▷ (j ∘ k)) ∙ (comp-assoc (j ∘ k) h v) ⁻¹)) ∙
        (isoComp-cong
          (isoComp-cong (postWhisker v ◁ short-image) (idIso (comp-assoc (j ∘ k) e v)))
          (idIso ((vertex ▷ (j ∘ k)) ∙ (comp-assoc (j ∘ k) h v) ⁻¹)) ∙
          (isoComp-assoc-at (v ◁ completed) (comp-assoc (j ∘ k) e v)
            ((vertex ▷ (j ∘ k)) ∙ (comp-assoc (j ∘ k) h v) ⁻¹)) ⁻¹)

      comparison : (complete-frame ∙ (v ◁ comp-assoc k j h)) =₂ restricted-global
      comparison = global-normalization ∙
        (associator-square v h j k vertex Lⱼ Lₖ ∙
          isoComp-cong complete-normalization (idIso (v ◁ comp-assoc k j h)))

  module Source = Endpoint ev₀ edge₂ (Completion.source-vertex C)
    pullback₁ (Cone.left t) (Completion.first-edge C) (ConeIso.leftIso β)
    (ConeIso.leftIso (Complete.short-edges t)) Short.first-edge
  module Target = Endpoint ev₁ edge₀ (Completion.target-vertex C)
    pullback₂ (Cone.right t) (Completion.second-edge C) (ConeIso.rightIso β)
    (ConeIso.rightIso (Complete.short-edges t)) Short.second-edge

  source-comparison :
    (Complete.source-boundary t ∙ (ev₀ ◁ Complete.composition-comparison t)) =₂
    ((ev₀ ◁ ConeIso.leftIso β) ∙
      (comp-assoc k pullback₁ ev₀ ∙ ((Completion.compose-source C ▷ k) ∙
        (comp-assoc k (compose C) ev₀) ⁻¹)))
  source-comparison = Source.comparison

  target-comparison :
    (Complete.target-boundary t ∙ (ev₁ ◁ Complete.composition-comparison t)) =₂
    ((ev₁ ◁ ConeIso.rightIso β) ∙
      (comp-assoc k pullback₂ ev₁ ∙ ((Completion.compose-target C ▷ k) ∙
        (comp-assoc k (compose C) ev₁) ⁻¹)))
  target-comparison = Target.comparison
```
