# Composition with specified endpoints

Two morphism expressions with a common endpoint define a cone to the
category of composable arrows. Completing this cone gives their composite.
The construction works on an absolute category of parameters, so it also
constructs the fixed-endpoint composition functor in
`cons:Composition_Functor`.

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

module SCT.VolumeI.Chapter02.Section02.CompositionExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open Laws.PullbackStructure P

expression-pair : {Γ C : CAT} {x y z : MAP Γ C} →
  MorphismExpression x y → MorphismExpression y z → Cone (ev₁ {C}) ev₀ Γ
expression-pair f g = record
  { left = MorphismExpression.arrow f
  ; right = MorphismExpression.arrow g
  ; match = (MorphismExpression.source-frame g) ⁻¹ ∙ MorphismExpression.target-frame f }

module Complete {Γ C : CAT} (t : Cone (ev₁ {C}) ev₀ Γ) where
  module U = UniversalCone (triangle-cone C) (SegalAxiom.segal-isPullback S C)

  triangle : MAP Γ (Triangles C)
  triangle = U.factor t

  short-edges : ConeIso (conePre triangle (triangle-cone C)) t
  short-edges = U.factor-β t

  long-edge : MAP Γ (Ar C)
  long-edge = edge₁ ∘ triangle

  composition-comparison : (compose C ∘ pullbackLift t) =₁ long-edge
  composition-comparison = comp-assoc (pullbackLift t) (completeTriangle C) edge₁

  source-boundary : (ev₀ ∘ long-edge) =₁ (ev₀ ∘ Cone.left t)
  source-boundary = (ev₀ ◁ ConeIso.leftIso short-edges) ∙
    (comp-assoc triangle edge₂ ev₀ ∙
      ((Completion.source-vertex C ▷ triangle) ∙ (comp-assoc triangle edge₁ ev₀) ⁻¹))

  target-boundary : (ev₁ ∘ long-edge) =₁ (ev₁ ∘ Cone.right t)
  target-boundary = (ev₁ ◁ ConeIso.rightIso short-edges) ∙
    (comp-assoc triangle edge₀ ev₁ ∙
      ((Completion.target-vertex C ▷ triangle) ∙ (comp-assoc triangle edge₁ ev₁) ⁻¹))

compose-expression : {Γ C : CAT} {x y z : MAP Γ C} →
  MorphismExpression x y → MorphismExpression y z → MorphismExpression x z
compose-expression f g = record
  { arrow = Complete.long-edge (expression-pair f g)
  ; source-frame = MorphismExpression.source-frame f ∙ Complete.source-boundary (expression-pair f g)
  ; target-frame = MorphismExpression.target-frame g ∙ Complete.target-boundary (expression-pair f g) }

hom-compose : {C : CAT} (x y z : Obj-abs C) →
  MAP (Hom C y z × Hom C x y) (Hom C x z)
hom-compose x y z = hom-intro
  (compose-expression (hom-expression pr₂) (hom-expression pr₁))
```
