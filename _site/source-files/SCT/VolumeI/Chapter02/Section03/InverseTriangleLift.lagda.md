# From inverse triangles to the category of isomorphisms

The two witnesses in `IsInvertible` give a lift to `Iso C`, as asserted
in `rmk:Lift_To_Iso_Iff_Invertible`. Here we construct this direction
explicitly: name the two triangles, identify their common edge with the
given arrow, and identify their long edges with the two identity arrows.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InverseTriangleLift
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)

open import SCT.VolumeI.Chapter02.Section02.DiagramNames 𝒯 M ℱ using (name-cong; named-restriction)

module LiftInverse {C : CAT} {x y : Obj-abs C}
  (f : Morphism x y) (w : IsInvertible f) where
  module W = IsInvertible w
  module Right = CompositeWitness W.right-inverse-triangle
  module Left = CompositeWitness W.left-inverse-triangle

  right-triangle left-triangle : Obj-abs (Triangles C)
  right-triangle = nameFun Right.triangle
  left-triangle = nameFun Left.triangle

  right-common : (edge₀ ∘ right-triangle) =₁ (nameFun (Morphism.diagram f))
  right-common = name-cong Right.second-edge ∙ named-restriction d₀ Right.triangle

  left-common : (edge₂ ∘ left-triangle) =₁ (nameFun (Morphism.diagram f))
  left-common = name-cong Left.first-edge ∙ named-restriction d₂ Left.triangle

  common : Cone (edge₀ {C}) edge₂ One
  common = record
    { left = right-triangle ; right = left-triangle
    ; match = left-common ⁻¹ ∙ right-common }

  triangles : Obj-abs (InverseTriangles C)
  triangles = pullbackLift common

  right-long : ((edge₁ ∘ pullback₁) ∘ triangles) =₁ (identityArrow ∘ y)
  right-long = (constantDiagram-point y) ⁻¹ ∙
    (name-cong Right.long-edge ∙ (named-restriction d₁ Right.triangle ∙
      ((edge₁ ◁ pullbackLift-β₁ common) ∙ comp-assoc triangles pullback₁ edge₁)))

  left-long : ((edge₁ ∘ pullback₂) ∘ triangles) =₁ (identityArrow ∘ x)
  left-long = (constantDiagram-point x) ⁻¹ ∙
    (name-cong Left.long-edge ∙ (named-restriction d₁ Left.triangle ∙
      ((edge₁ ◁ pullbackLift-β₂ common) ∙ comp-assoc triangles pullback₂ edge₁)))

  identities-at-objects : (inverseIdentityEdges C ∘ pair x y) =₁
    (pair (identityArrow ∘ y) (identityArrow ∘ x))
  identities-at-objects = pair-cong
    (((identityArrow ◁ pair-β₂ x y) ∙ comp-assoc (pair x y) pr₂ identityArrow))
    (((identityArrow ◁ pair-β₁ x y) ∙ comp-assoc (pair x y) pr₁ identityArrow)) ∙
    pair-pre (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) (pair x y)

  inverse-cone : Cone (inverseLongEdges C) (inverseIdentityEdges C) One
  inverse-cone = record
    { left = triangles ; right = pair x y
    ; match = identities-at-objects ⁻¹ ∙
        (pair-cong right-long left-long ∙ pair-pre (edge₁ ∘ pullback₁) (edge₁ ∘ pullback₂) triangles) }

  value : Obj-abs (Iso C)
  value = pullbackLift inverse-cone

  arrow-comparison : (isoArrow ∘ value) =₁ (nameFun (Morphism.diagram f))
  arrow-comparison = right-common ∙
    ((edge₀ ◁ pullbackLift-β₁ common) ∙
    (comp-assoc triangles pullback₁ edge₀ ∙
      (((edge₀ ∘ pullback₁) ◁ pullbackLift-β₁ inverse-cone) ∙
        comp-assoc value isoTriangles (edge₀ ∘ pullback₁))))

invertible-lift : {C : CAT} {x y : Obj-abs C} (f : Morphism x y) →
  IsInvertible f → IsoLift (nameFun (Morphism.diagram f))
invertible-lift f w = record
  { lift = LiftInverse.value f w ; comparison = LiftInverse.arrow-comparison f w }
```
