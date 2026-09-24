# Uniqueness with specified outer vertices

The Segal equivalence lifts a comparison of short edges. We retain its
specified images under both edge restrictions. Interchange with the two
outer vertex comparisons then proves that the induced comparison of long
edges preserves the source and target.

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

module SCT.VolumeI.Chapter02.Section02.TriangleComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.UniversalConeLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (cone-action)

source-cone : (C : CAT) → Cone (ev₀ {C}) ev₀ (Triangles C)
source-cone C = record
  { left = edge₁ ; right = edge₂ ; match = Completion.source-vertex C }

target-cone : (C : CAT) → Cone (ev₁ {C}) ev₁ (Triangles C)
target-cone C = record
  { left = edge₁ ; right = edge₀ ; match = Completion.target-vertex C }

module VertexFrame {Γ C : CAT} {h k : MAP Γ (Triangles C)} (δ : h =₁ k)
  (v : MAP (Ar C) C) (e : MAP (Triangles C) (Ar C))
  (ν : (v ∘ edge₁) =₁ (v ∘ e)) {x : MAP Γ C}
  (p : (v ∘ (e ∘ h)) =₁ x) (q : (v ∘ (e ∘ k)) =₁ x) where
  corner : Cone v v (Triangles C)
  corner = record { left = edge₁ ; right = e ; match = ν }
  before = Cone.match (conePre h corner)
  after = Cone.match (conePre k corner)

  extend : (q ∙ (v ◁ (e ◁ δ))) =₂ p →
    ((q ∙ after) ∙ (v ◁ (edge₁ ◁ δ))) =₂ (p ∙ before)
  extend compatible = isoComp-cong compatible (idIso before) ∙
    ((isoComp-assoc-at q (v ◁ (e ◁ δ)) before) ⁻¹ ∙
      (isoComp-cong (idIso q) (ConeIso.compatible (cone-action corner δ)) ∙
        isoComp-assoc-at q after (v ◁ (edge₁ ◁ δ))))

module Presented {Γ C : CAT} (t : Cone (ev₁ {C}) ev₀ Γ)
  (h : MAP Γ (Triangles C)) (β : ConeIso (conePre h (triangle-cone C)) t) where

  long-expression : MorphismExpression (ev₀ ∘ Cone.left t) (ev₁ ∘ Cone.right t)
  long-expression = record
    { arrow = edge₁ ∘ h
    ; source-frame = (ev₀ ◁ ConeIso.leftIso β) ∙ Cone.match (conePre h (source-cone C))
    ; target-frame = (ev₁ ◁ ConeIso.rightIso β) ∙ Cone.match (conePre h (target-cone C)) }

module Compare {Γ C : CAT} (t : Cone (ev₁ {C}) ev₀ Γ)
  (h k : MAP Γ (Triangles C))
  (β : ConeIso (conePre h (triangle-cone C)) t)
  (γ : ConeIso (conePre k (triangle-cone C)) t) where

  short-edges = coneIso-compose (coneIso-inverse γ) β
  module Lift = UniversalLift (triangle-cone C) (SegalAxiom.segal-isPullback S C) h k short-edges

  triangle-comparison : h =₁ k
  triangle-comparison = Lift.lift

  edge-equation : {A B : CAT} {u v w : MAP A B}
    (p : u =₁ w) (q : v =₁ w) (δ : u =₁ v) →
    δ =₂ (q ⁻¹ ∙ p) → (q ∙ δ) =₂ p
  edge-equation p q δ image = isoComp-unitˡ-at p ∙
    (isoComp-cong (isoComp-inverseʳ-at q) (idIso p) ∙
      ((isoComp-assoc-at q (q ⁻¹) p) ⁻¹ ∙ isoComp-cong (idIso q) image))

  endpoint : (v : MAP (Ar C) C) (e : MAP (Triangles C) (Ar C))
    (ν : (v ∘ edge₁) =₁ (v ∘ e)) {u : MAP Γ (Ar C)}
    (p : (e ∘ h) =₁ u) (q : (e ∘ k) =₁ u) →
    (e ◁ triangle-comparison) =₂ (q ⁻¹ ∙ p) →
    let corner : Cone v v (Triangles C)
        corner = record { left = edge₁ ; right = e ; match = ν }
        before = Cone.match (conePre h corner)
        after = Cone.match (conePre k corner)
    in ((v ◁ q ∙ after) ∙ (v ◁ (edge₁ ◁ triangle-comparison))) =₂
      (v ◁ p ∙ before)
  endpoint v e ν p q image =
    isoComp-cong ((postWhisker v ◁ edge-equation p q (e ◁ triangle-comparison) image) ∙
      (postWhisker-isoComp-at v q (e ◁ triangle-comparison)) ⁻¹) (idIso before) ∙
    ((isoComp-assoc-at (v ◁ q) (v ◁ (e ◁ triangle-comparison)) before) ⁻¹ ∙
    (isoComp-cong (idIso (v ◁ q)) (ConeIso.compatible (cone-action corner triangle-comparison)) ∙
      isoComp-assoc-at (v ◁ q) after (v ◁ (edge₁ ◁ triangle-comparison))))
    where
    corner : Cone v v (Triangles C)
    corner = record { left = edge₁ ; right = e ; match = ν }
    before = Cone.match (conePre h corner)
    after = Cone.match (conePre k corner)

  long-comparison : ExpressionIso
    (Presented.long-expression t h β) (Presented.long-expression t k γ)
  long-comparison = record
    { comparison = edge₁ ◁ triangle-comparison
    ; source-compatible = endpoint ev₀ edge₂ (Completion.source-vertex C)
        (ConeIso.leftIso β) (ConeIso.leftIso γ) Lift.left-image
    ; target-compatible = endpoint ev₁ edge₀ (Completion.target-vertex C)
        (ConeIso.rightIso β) (ConeIso.rightIso γ) Lift.right-image }
```
