# Triangles and categories of composites

The three edges of a triangle are restrictions along the face maps.
The middle face identity supplies the matching needed to map into the
pullback of composable arrows. The category in `def:Composite` is the
fiber over the specified composable pair, including this matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.TrianglesAndComposites
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle 𝒯 M ℱ P I E public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

Triangle : CAT → Set m
Triangle C = MAP [2] C

Triangles : CAT → CAT
Triangles C = Fun [2] C

edge₀ edge₁ edge₂ : {C : CAT} → MAP (Triangles C) (Ar C)
edge₀ = funPre d₀
edge₁ = funPre d₁
edge₂ = funPre d₂

Composable : CAT → CAT
Composable C = Pullback (ev₁ {C}) ev₀

triangle-cone : (C : CAT) → Cone (ev₁ {C}) ev₀ (Triangles C)
triangle-cone C = record
  { left = edge₂ ; right = edge₀
  ; match = (evaluate-pre d₀ zero) ⁻¹ ∙
      (evaluate-cong (face-middle ⁻¹) ∙ evaluate-pre d₂ one) }

composable-restriction : (C : CAT) → MAP (Triangles C) (Composable C)
composable-restriction C = pullbackLift (triangle-cone C)

composable-restriction-β : (C : CAT) →
  ConeIso (conePre (composable-restriction C) (pullbackCone ev₁ ev₀)) (triangle-cone C)
composable-restriction-β C = pullbackLift-β (triangle-cone C)

module PairOfMorphisms {C : CAT} {x y z : Obj-abs C} (f : Morphism x y) (g : Morphism y z) where
  cone : Cone (ev₁ {C}) ev₀ One
  cone = record
    { left = nameFun (Morphism.diagram f) ; right = nameFun (Morphism.diagram g)
    ; match = (evaluate-name zero (Morphism.diagram g)) ⁻¹ ∙
        ((Morphism.source-identification g) ⁻¹ ∙
        (Morphism.target-identification f ∙ evaluate-name one (Morphism.diagram f))) }

  value : Obj-abs (Composable C)
  value = pullbackLift cone

Composites : (C : CAT) → Obj-abs (Composable C) → CAT
Composites C pair = Pullback (composable-restriction C) pair

Comp : {C : CAT} {x y z : Obj-abs C} → Morphism x y → Morphism y z → CAT
Comp {C} f g = Composites C (PairOfMorphisms.value f g)

composite-triangle : {C : CAT} (p : Obj-abs (Composable C)) → MAP (Composites C p) (Triangles C)
composite-triangle p = pullback₁

composite-arrow : {C : CAT} (p : Obj-abs (Composable C)) → MAP (Composites C p) (Ar C)
composite-arrow p = edge₁ ∘ composite-triangle p
```

For `ex:Composite_With_Identity`, precomposition by the two degeneracies
gives triangles whose short and long edges have the indicated forms.
The triangles themselves retain the common-vertex identification.

```agda
module IdentityComposites {C : CAT} (f : Mor C) where
  left-unit-triangle right-unit-triangle : Triangle C
  left-unit-triangle = f ∘ s₀
  right-unit-triangle = f ∘ s₁

  left-first : (left-unit-triangle ∘ d₂) =₁ (const (source f))
  left-first = (comp-assoc (terminate [1]) zero f) ⁻¹ ∙
    ((f ◁ s₀-d₂) ∙ comp-assoc d₂ s₀ f)
  left-second : (left-unit-triangle ∘ d₀) =₁ f
  left-second = comp-unitʳ f ∙ ((f ◁ s₀-d₀) ∙ comp-assoc d₀ s₀ f)
  left-long : (left-unit-triangle ∘ d₁) =₁ f
  left-long = comp-unitʳ f ∙ ((f ◁ s₀-d₁) ∙ comp-assoc d₁ s₀ f)

  right-first : (right-unit-triangle ∘ d₂) =₁ f
  right-first = comp-unitʳ f ∙ ((f ◁ s₁-d₂) ∙ comp-assoc d₂ s₁ f)
  right-second : (right-unit-triangle ∘ d₀) =₁ (const (target f))
  right-second = (comp-assoc (terminate [1]) one f) ⁻¹ ∙
    ((f ◁ s₁-d₀) ∙ comp-assoc d₀ s₁ f)
  right-long : (right-unit-triangle ∘ d₁) =₁ f
  right-long = comp-unitʳ f ∙ ((f ◁ s₁-d₁) ∙ comp-assoc d₁ s₁ f)
```

