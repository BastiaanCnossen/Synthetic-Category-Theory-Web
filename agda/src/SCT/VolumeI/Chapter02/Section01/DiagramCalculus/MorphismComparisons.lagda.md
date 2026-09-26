# Comparisons of morphisms with specified endpoints

A comparison of interval diagrams must respect both endpoint
identifications. Postcomposition carries these frames along with the
diagram. In particular, its comparison with the constant identity
morphism respects both endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.MorphismComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.AbsoluteMorphisms 𝒯 M ℱ P I public
import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.IdentityBoundaries as Boundaries
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairUnits
open PairUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)

record MorphismIso {C : CAT} {x y : Obj-abs C} (f g : Morphism x y) : Set m where
  field
    comparison : (Morphism.diagram f) =₁ (Morphism.diagram g)
    source-compatible :
      (Morphism.source-identification g ∙ (comparison ▷ zero)) =₂ (Morphism.source-identification f)
    target-compatible :
      (Morphism.target-identification g ∙ (comparison ▷ one)) =₂ (Morphism.target-identification f)

morphismIso-id : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) → MorphismIso f f
morphismIso-id f = record
  { comparison = idIso (Morphism.diagram f)
  ; source-compatible = isoComp-unitʳ-at (Morphism.source-identification f) ∙
      isoComp-cong (idIso (Morphism.source-identification f)) (preWhisker-idIso (Morphism.diagram f) zero)
  ; target-compatible = isoComp-unitʳ-at (Morphism.target-identification f) ∙
      isoComp-cong (idIso (Morphism.target-identification f)) (preWhisker-idIso (Morphism.diagram f) one) }

post-morphism : {C D : CAT} {x y : Obj-abs C} → (F : MAP C D) →
  Morphism x y → Morphism (F ∘ x) (F ∘ y)
post-morphism F f = record
  { diagram = F ∘ Morphism.diagram f
  ; source-identification = (F ◁ Morphism.source-identification f) ∙ comp-assoc zero (Morphism.diagram f) F
  ; target-identification = (F ◁ Morphism.target-identification f) ∙ comp-assoc one (Morphism.diagram f) F }

post-identity-morphism : {C D : CAT} (F : MAP C D) (x : Obj-abs C) →
  MorphismIso (post-morphism F (identity-morphism x)) (identity-morphism (F ∘ x))
post-identity-morphism F x = record
  { comparison = (comp-assoc (terminate [1]) x F) ⁻¹
  ; source-compatible = Boundaries.EvaluationBoundary.comparison 𝒯 M ℱ I
      zero (terminate [1]) (terminal-iso (terminate [1] ∘ zero) (id One)) F x
  ; target-compatible = Boundaries.EvaluationBoundary.comparison 𝒯 M ℱ I
      one (terminate [1]) (terminal-iso (terminate [1] ∘ one) (id One)) F x }

interval-morphism : Morphism zero one
interval-morphism = record
  { diagram = id [1]
  ; source-identification = comp-unitˡ zero
  ; target-identification = comp-unitˡ one }

post-interval-morphism : {C : CAT} (F : Mor C) →
  MorphismIso (post-morphism F interval-morphism) (underlying-morphism F)
post-interval-morphism F = record
  { comparison = comp-unitʳ F
  ; source-compatible = triangle-whiskered zero F ∙ isoComp-unitˡ-at (comp-unitʳ F ▷ zero)
  ; target-compatible = triangle-whiskered one F ∙ isoComp-unitˡ-at (comp-unitʳ F ▷ one) }
```

