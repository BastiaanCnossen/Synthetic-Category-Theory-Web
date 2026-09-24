# The two universal inverse triangles

The defining pullbacks of `Iso C` give the common short edge and both
constant long edges. These comparisons precede Segal and Rezk.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InverseTriangleData
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

module UniversalData (C : CAT) where
  private
    q = isoTriangles {C}
    o = isoObjects {C}
    p₁ : MAP (InverseTriangles C) (Triangles C)
    p₁ = pullback₁
    p₂ : MAP (InverseTriangles C) (Triangles C)
    p₂ = pullback₂

  arrow : MorphismExpression (ev₀ ∘ isoArrow {C}) (ev₁ ∘ isoArrow)
  arrow = record { arrow = isoArrow
    ; source-frame = idIso (ev₀ ∘ isoArrow) ; target-frame = idIso (ev₁ ∘ isoArrow) }

  right-triangle left-triangle : MAP (Iso C) (Triangles C)
  right-triangle = p₁ ∘ q
  left-triangle = p₂ ∘ q

  common-edge : (edge₀ ∘ right-triangle) =₁ (edge₂ ∘ left-triangle)
  common-edge = Cone.match (conePre q (pullbackCone (edge₀ {C}) edge₂))

  right-short : (edge₀ ∘ right-triangle) =₁ (isoArrow {C})
  right-short = (comp-assoc q p₁ edge₀) ⁻¹

  left-short : (edge₂ ∘ left-triangle) =₁ (isoArrow {C})
  left-short = right-short ∙ common-edge ⁻¹

  right-long : (edge₁ ∘ right-triangle) =₁ (identityArrow ∘ (pr₂ ∘ o))
  right-long = comp-assoc o pr₂ identityArrow ∙
    (project-pair₁ (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) o ∙
    ((pr₁ ◁ pullbackMatch {f = inverseLongEdges C} {inverseIdentityEdges C}) ∙
    ((project-pair₁ (edge₁ ∘ p₁) (edge₁ ∘ p₂) q) ⁻¹ ∙
      (comp-assoc q p₁ edge₁) ⁻¹)))

  left-long : (edge₁ ∘ left-triangle) =₁ (identityArrow ∘ (pr₁ ∘ o))
  left-long = comp-assoc o pr₁ identityArrow ∙
    (project-pair₂ (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) o ∙
    ((pr₂ ◁ pullbackMatch {f = inverseLongEdges C} {inverseIdentityEdges C}) ∙
    ((project-pair₂ (edge₁ ∘ p₁) (edge₁ ∘ p₂) q) ⁻¹ ∙
      (comp-assoc q p₂ edge₁) ⁻¹)))

```
