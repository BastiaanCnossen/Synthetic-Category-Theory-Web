# Changing the displayed vertices of a composite

A morphism may have specified endpoint identifications with objects other
than its literal evaluations. Transporting a triangle to these displayed
vertices changes the endpoint frames on its edges together. This extends
the unit examples to every `Morphism x y` with its given frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.VertexTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.IdentityComposites 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DegenerateCocones 𝒯 M ℱ P I E
  using (triangle-edges; triangle-source; upper-edges)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (quotient-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at; preWhisker-id-at)

reframe-morphism : {C : CAT} {x y x′ y′ : Obj-abs C} →
  (f : Morphism x y) → x =₁ x′ → y =₁ y′ → Morphism x′ y′
reframe-morphism f α β = record
  { diagram = Morphism.diagram f
  ; source-identification = α ∙ Morphism.source-identification f
  ; target-identification = β ∙ Morphism.target-identification f }

vertex-comparison : {C : CAT} {u v : Obj-abs [1]} {p q : Mor C} {z z′ : Obj-abs C}
  (α : (p ∘ u) =₁ z) (β : (q ∘ v) =₁ z) (η : z =₁ z′) →
  CoconeIso (framed-cocone p q α β) (framed-cocone p q (η ∙ α) (η ∙ β))
vertex-comparison {u = u} {v} {p} {q} α β η = record
  { leftIso = idIso p ; rightIso = idIso q
  ; compatible = quotient-square α β (η ∙ α) (η ∙ β) (idIso p ▷ u) (idIso q ▷ v) η
      (isoComp-unitʳ-at (η ∙ α) ∙ isoComp-cong (idIso (η ∙ α)) (preWhisker-idIso p u))
      (isoComp-unitʳ-at (η ∙ β) ∙ isoComp-cong (idIso (η ∙ β)) (preWhisker-idIso q v)) }

reframe-witness : {C : CAT} {x y z x′ y′ z′ : Obj-abs C}
  {f : Morphism x y} {g : Morphism y z} {h : Morphism x z} →
  (α : x =₁ x′) (β : y =₁ y′) (γ : z =₁ z′) → CompositeWitness f g h →
  CompositeWitness (reframe-morphism f α β) (reframe-morphism g β γ) (reframe-morphism h α γ)
reframe-witness {f = f} {g} {h} α β γ w = record
  { triangle = W.triangle
  ; first-edge = W.first-edge ; second-edge = W.second-edge ; long-edge = W.long-edge
  ; middle-vertex = CoconeIso.compatible middle
  ; source-vertex = CoconeIso.compatible source-corner
  ; target-vertex = CoconeIso.compatible target-corner }
  where
  module W = CompositeWitness w
  middle = coconeIso-adjust (coconeIso-compose
      (vertex-comparison (Morphism.target-identification f) (Morphism.source-identification g) β)
      W.middle-comparison) W.first-edge W.second-edge
    (isoComp-unitˡ-at W.first-edge) (isoComp-unitˡ-at W.second-edge)
  source-corner = coconeIso-adjust (coconeIso-compose
      (vertex-comparison (Morphism.source-identification h) (Morphism.source-identification f) α)
      W.source-comparison) W.long-edge W.first-edge
    (isoComp-unitˡ-at W.long-edge) (isoComp-unitˡ-at W.first-edge)
  target-corner = coconeIso-adjust (coconeIso-compose
      (vertex-comparison (Morphism.target-identification g) (Morphism.target-identification h) γ)
      W.target-comparison) W.second-edge W.long-edge
    (isoComp-unitˡ-at W.second-edge) (isoComp-unitˡ-at W.long-edge)

recover-morphism : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) →
  MorphismIso (reframe-morphism (underlying-morphism (Morphism.diagram f))
    (Morphism.source-identification f) (Morphism.target-identification f)) f
recover-morphism f = record
  { comparison = idIso (Morphism.diagram f)
  ; source-compatible = isoComp-cong (idIso (Morphism.source-identification f))
      (preWhisker-idIso (Morphism.diagram f) zero)
  ; target-compatible = isoComp-cong (idIso (Morphism.target-identification f))
      (preWhisker-idIso (Morphism.diagram f) one) }

module ConstantBoundary {C : CAT} {x y : Obj-abs C} (η : x =₁ y) (i : Obj-abs [1]) where
  terminal-boundary = terminal-iso (terminate [1] ∘ i) (id One)
  inner = η ▷ (terminate [1] ∘ i)
  outer = η ▷ id One
  abstract
    natural : (constant-boundary i y ∙ ((η ▷ terminate [1]) ▷ i)) =₂
      (η ∙ constant-boundary i x)
    natural = paste-squares ((x ◁ terminal-boundary) ∙ comp-assoc i (terminate [1]) x)
      ((y ◁ terminal-boundary) ∙ comp-assoc i (terminate [1]) y)
      (comp-unitʳ x) (comp-unitʳ y) ((η ▷ terminate [1]) ▷ i) outer η
      (paste-squares (comp-assoc i (terminate [1]) x) (comp-assoc i (terminate [1]) y)
        (x ◁ terminal-boundary) (y ◁ terminal-boundary)
        ((η ▷ terminate [1]) ▷ i) inner outer
        (preWhisker-comp-at η (terminate [1]) i) ((interchange-at η terminal-boundary) ⁻¹))
      (preWhisker-id-at η)
reframe-identity : {C : CAT} {x y : Obj-abs C} (η : x =₁ y) →
  MorphismIso (reframe-morphism (identity-morphism x) η η) (identity-morphism y)
reframe-identity η = record
  { comparison = η ▷ terminate [1]
  ; source-compatible = ConstantBoundary.natural η zero
  ; target-compatible = ConstantBoundary.natural η one }

morphism-left-unit : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) →
  CompositeWitness (identity-morphism x) f f
morphism-left-unit f = retarget-witness
  (reframe-identity (Morphism.source-identification f)) (recover-morphism f) (recover-morphism f)
  (reframe-witness (Morphism.source-identification f) (Morphism.source-identification f)
    (Morphism.target-identification f) (compose-left-identity (Morphism.diagram f)))

morphism-right-unit : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) →
  CompositeWitness f (identity-morphism y) f
morphism-right-unit f = retarget-witness
  (recover-morphism f) (reframe-identity (Morphism.target-identification f)) (recover-morphism f)
  (reframe-witness (Morphism.source-identification f) (Morphism.target-identification f)
    (Morphism.target-identification f) (compose-right-identity (Morphism.diagram f)))
```

