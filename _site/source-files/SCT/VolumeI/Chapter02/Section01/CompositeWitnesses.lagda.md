# Composite witnesses with all three vertices

This is the first description in `def:Composite`: a triangle with the
specified short and long edges. Each edge comparison retains its vertex
data. The three equations below say that the comparisons agree at the
source, the common vertex, and the target.

The category `Comp` is constructed in `TrianglesAndComposites`. Here we
use the explicit triangle description; a comparison between this record
and named objects of that pullback is not needed for the examples below.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.CompositeWitnesses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.TrianglesAndComposites 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.MorphismComparisons 𝒯 M ℱ P I public using (MorphismIso; post-morphism; post-identity-morphism; identity-morphism; underlying-morphism; interval-morphism; post-interval-morphism)
open import SCT.VolumeI.Chapter02.Section01.DegenerateCocones 𝒯 M ℱ P I E
  using (triangle-edges; triangle-source; upper-edges)
open import SCT.VolumeI.Chapter02.Section01.FramedCocones 𝒯 public

module Boundary {C : CAT} {x y z : Obj-abs C}
  (f : Morphism x y) (g : Morphism y z) (h : Morphism x z) where
  middle : Cocone one zero C
  middle = framed-cocone (Morphism.diagram f) (Morphism.diagram g)
    (Morphism.target-identification f) (Morphism.source-identification g)
  source-corner : Cocone zero zero C
  source-corner = framed-cocone (Morphism.diagram h) (Morphism.diagram f)
    (Morphism.source-identification h) (Morphism.source-identification f)
  target-corner : Cocone one one C
  target-corner = framed-cocone (Morphism.diagram g) (Morphism.diagram h)
    (Morphism.target-identification g) (Morphism.target-identification h)

record CompositeWitness {C : CAT} {x y z : Obj-abs C}
  (f : Morphism x y) (g : Morphism y z) (h : Morphism x z) : Set m where
  module B = Boundary f g h
  field
    triangle : Triangle C
    first-edge : (triangle ∘ d₂) =₁ (Morphism.diagram f)
    second-edge : (triangle ∘ d₀) =₁ (Morphism.diagram g)
    long-edge : (triangle ∘ d₁) =₁ (Morphism.diagram h)
    middle-vertex : (Cocone.match B.middle ∙ (first-edge ▷ one)) =₂
      ((second-edge ▷ zero) ∙ Cocone.match (coconePost triangle triangle-edges))
    source-vertex : (Cocone.match B.source-corner ∙ (long-edge ▷ zero)) =₂
      ((first-edge ▷ zero) ∙ Cocone.match (coconePost triangle triangle-source))
    target-vertex : (Cocone.match B.target-corner ∙ (second-edge ▷ one)) =₂
      ((long-edge ▷ one) ∙ Cocone.match (coconePost triangle upper-edges))

  middle-comparison : CoconeIso (coconePost triangle triangle-edges) B.middle
  middle-comparison = record { leftIso = first-edge ; rightIso = second-edge ; compatible = middle-vertex }
  source-comparison : CoconeIso (coconePost triangle triangle-source) B.source-corner
  source-comparison = record { leftIso = long-edge ; rightIso = first-edge ; compatible = source-vertex }
  target-comparison : CoconeIso (coconePost triangle upper-edges) B.target-corner
  target-comparison = record { leftIso = second-edge ; rightIso = long-edge ; compatible = target-vertex }
```

Applying a functor to a composite witness retains the three equations.
Changing any of the edge representatives is also allowed, provided its
comparison respects the specified endpoints.

```agda
post-witness : {C D : CAT} {x y z : Obj-abs C}
  {f : Morphism x y} {g : Morphism y z} {h : Morphism x z} →
  (F : MAP C D) → CompositeWitness f g h →
  CompositeWitness (post-morphism F f) (post-morphism F g) (post-morphism F h)
post-witness {f = f} {g} {h} F w = record
  { triangle = F ∘ W.triangle
  ; first-edge = (F ◁ W.first-edge) ∙ comp-assoc d₂ W.triangle F
  ; second-edge = (F ◁ W.second-edge) ∙ comp-assoc d₀ W.triangle F
  ; long-edge = (F ◁ W.long-edge) ∙ comp-assoc d₁ W.triangle F
  ; middle-vertex = CoconeIso.compatible middle
  ; source-vertex = CoconeIso.compatible source-corner
  ; target-vertex = CoconeIso.compatible target-corner }
  where
  module W = CompositeWitness w
  middle = PostFramedComparison.comparison triangle-edges W.triangle F
    (Morphism.diagram f) (Morphism.diagram g)
    (Morphism.target-identification f) (Morphism.source-identification g) W.middle-comparison
  source-corner = PostFramedComparison.comparison triangle-source W.triangle F
    (Morphism.diagram h) (Morphism.diagram f)
    (Morphism.source-identification h) (Morphism.source-identification f) W.source-comparison
  target-corner = PostFramedComparison.comparison upper-edges W.triangle F
    (Morphism.diagram g) (Morphism.diagram h)
    (Morphism.target-identification g) (Morphism.target-identification h) W.target-comparison

retarget-witness : {C : CAT} {x y z : Obj-abs C}
  {f f′ : Morphism x y} {g g′ : Morphism y z} {h h′ : Morphism x z} →
  MorphismIso f f′ → MorphismIso g g′ → MorphismIso h h′ →
  CompositeWitness f g h → CompositeWitness f′ g′ h′
retarget-witness {f = f} {f′} {g} {g′} {h} {h′} α β γ w = record
  { triangle = W.triangle
  ; first-edge = MorphismIso.comparison α ∙ W.first-edge
  ; second-edge = MorphismIso.comparison β ∙ W.second-edge
  ; long-edge = MorphismIso.comparison γ ∙ W.long-edge
  ; middle-vertex = CoconeIso.compatible (coconeIso-compose middle W.middle-comparison)
  ; source-vertex = CoconeIso.compatible (coconeIso-compose source-corner W.source-comparison)
  ; target-vertex = CoconeIso.compatible (coconeIso-compose target-corner W.target-comparison) }
  where
  module W = CompositeWitness w
  middle = framed-comparison
    (Morphism.target-identification f) (Morphism.source-identification g)
    (Morphism.target-identification f′) (Morphism.source-identification g′)
    (MorphismIso.comparison α) (MorphismIso.comparison β)
    (MorphismIso.target-compatible α) (MorphismIso.source-compatible β)
  source-corner = framed-comparison
    (Morphism.source-identification h) (Morphism.source-identification f)
    (Morphism.source-identification h′) (Morphism.source-identification f′)
    (MorphismIso.comparison γ) (MorphismIso.comparison α)
    (MorphismIso.source-compatible γ) (MorphismIso.source-compatible α)
  target-corner = framed-comparison
    (Morphism.target-identification g) (Morphism.target-identification h)
    (Morphism.target-identification g′) (Morphism.target-identification h′)
    (MorphismIso.comparison β) (MorphismIso.comparison γ)
    (MorphismIso.target-compatible β) (MorphismIso.target-compatible γ)
```

