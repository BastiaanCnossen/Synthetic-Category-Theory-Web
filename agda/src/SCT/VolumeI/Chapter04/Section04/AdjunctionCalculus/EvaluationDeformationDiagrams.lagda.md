# Constant diagrams obtained by evaluating the deformations

At its absorbing endpoint, each interval deformation becomes a constant
diagram. The comparisons use the full universal-endpoint choices from
`OuterVertices`, so their endpoint equations remain available for the
subsequent normalization proof. This module constructs the uncurried
comparisons; it does not yet assert the normalized expression equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Squares
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles as Units

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformationDiagrams
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.OuterVertices 𝒯 M ℱ P I E
  using (module Top; module Bottom)
open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair; product-first)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramEvaluation 𝒯 M ℱ
  using (evaluate-constant-at)

row-restriction : {X C : CAT} (h : MAP X (Ar C)) (x : Obj-abs X) →
  decodeFun (h ∘ x) =₁ (funUncurry h ∘ pair (const x) (id [1]))
row-restriction h x = (funUncurry h ◁
  (pair-cong (idIso (const x)) (comp-unitˡ (id [1])) ∙
    productMap-pair x (id [1]) (terminate [1]) (id [1]))) ∙
  (comp-assoc (oneProduct-in [1]) (productMap x (id [1])) (funUncurry h) ∙
    (funUncurry-restrict h x ▷ oneProduct-in [1]))

constant-row : {C : CAT} (x : Obj-abs C) → decodeFun (identityArrow ∘ x) =₁ const x
constant-row {C} x = (x ◁ pair-β₁ (terminate [1]) (id [1])) ∙
  (comp-assoc (oneProduct-in [1]) pr₁ x ∙
    ((pair-β₁ (x ∘ pr₁) (id [1] ∘ pr₂) ∙
      ((funCurry-β (pr₁ {C} {[1]}) ▷ productMap x (id [1])) ∙
        funUncurry-restrict identityArrow x)) ▷ oneProduct-in [1]))

maximum-absorbing : (max ∘ pair (const one) (id [1])) =₁ const one
maximum-absorbing = constant-row one ∙
  ((funUncurryIso Top.value ▷ oneProduct-in [1]) ∙ (row-restriction max̄ one) ⁻¹)

minimum-absorbing : (min ∘ pair (const zero) (id [1])) =₁ const zero
minimum-absorbing = constant-row zero ∙
  ((funUncurryIso (Bottom.value ⁻¹) ▷ oneProduct-in [1]) ∙ (row-restriction min̄ zero) ⁻¹)

module At (C : CAT) where
  module Universal = Units.Universal 𝒯 M ℱ P I E C using (constant-evaluation)

  module Absorbing (h : MAP ([1] × [1]) [1]) (u : Obj-abs [1])
    (β : (h ∘ pair (const u) (id [1])) =₁ const u) where
    module Curry = Squares.At 𝒯 M ℱ (funPre {D = C} h) using (nested; module Horizontal)
    co = pair (const u) (id [1])
    side = funPre co ∘ funPre {D = C} h

    side-image : funUncurry side =₁ (funEval ∘ productMap (id (Ar C)) (h ∘ co))
    side-image = (funEval ◁ productRestriction-comp (Ar C) co h) ∙
      (comp-assoc (productMap (id (Ar C)) co) (productMap (id (Ar C)) h) funEval ∙
        ((funPre-β h ▷ productMap (id (Ar C)) co) ∙ funPre-uncurry co (funPre h)))

    diagram-comparison : funUncurry (funPost (evaluate u) ∘ Curry.nested) =₁ (evaluate u ∘ pr₁)
    diagram-comparison = Universal.constant-evaluation u ∙
      ((funEval ◁ productMap-cong (idIso (id (Ar C))) β) ∙
        (side-image ∙ funUncurryIso (Curry.Horizontal.comparison u)))

  target-diagram = Absorbing.diagram-comparison max one maximum-absorbing
  source-diagram = Absorbing.diagram-comparison min zero minimum-absorbing

  module OnSection (h : MAP ([1] × [1]) [1]) where
    module Curry = Squares.At 𝒯 M ℱ (funPre {D = C} h)
      using (nested; first-curry; diagram; H; module Coordinates)
    s : MAP C (Ar C)
    s = identityArrow
    r = productMap s (id [1])
    change = productMap r (id [1])
    K = Curry.Coordinates.permute ∘ change
    parameter : MAP ((C × [1]) × [1]) C
    parameter = pr₁ ∘ pr₁

    parameter-comparison : (pr₁ ∘ K) =₁ (s ∘ parameter)
    parameter-comparison = product-first s (id [1]) pr₁ ∙
      ((pr₁ ◁ pair-β₁ (r ∘ pr₁) (id [1] ∘ pr₂)) ∙
        (comp-assoc change pr₁ pr₁ ∙
          ((pair-β₁ Curry.Coordinates.parameter Curry.Coordinates.rectangle ▷ change) ∙
            (comp-assoc change Curry.Coordinates.permute pr₁) ⁻¹)))

    evaluation-comparison : (funEval ∘ (productMap (id (Ar C)) h ∘ K)) =₁ parameter
    evaluation-comparison = evaluate-constant-at parameter ((h ∘ pr₂) ∘ K) ∙
      (funEval ◁ (pair-cong
        (parameter-comparison ∙ (comp-unitˡ (pr₁ ∘ K) ∙ comp-assoc K pr₁ (id (Ar C))))
        (idIso ((h ∘ pr₂) ∘ K)) ∙
        pair-pre (id (Ar C) ∘ pr₁) (h ∘ pr₂) K))

    source-double : funUncurry (funUncurry (Curry.nested ∘ s)) =₁ parameter
    source-double = evaluation-comparison ∙
      (comp-assoc K (productMap (id (Ar C)) h) funEval ∙
        ((funPre-β h ▷ K) ∙
          (comp-assoc change Curry.Coordinates.permute Curry.H ∙
            ((funCurry-β Curry.diagram ▷ change) ∙
              (funUncurry-restrict Curry.first-curry r ∙
                funUncurryIso ((funCurry-β Curry.first-curry ▷ r) ∙
                  funUncurry-restrict Curry.nested s))))))

    target-double : funUncurry (s ∘ pr₁ {C} {[1]}) =₁ parameter
    target-double = pair-β₁ (pr₁ ∘ pr₁) (id [1] ∘ pr₂) ∙
      ((funCurry-β (pr₁ {C} {[1]}) ▷ productMap pr₁ (id [1])) ∙
        funUncurry-restrict s pr₁)

    abstract
      diagram-comparison : funUncurry (Curry.nested ∘ s) =₁ (s ∘ pr₁)
      diagram-comparison = funIsoReflect _ _ (target-double ⁻¹ ∙ source-double)

      diagram-comparison-β : funUncurryIso diagram-comparison =₂ (target-double ⁻¹ ∙ source-double)
      diagram-comparison-β = funIsoReflect-β _ _ (target-double ⁻¹ ∙ source-double)

  target-section-diagram = OnSection.diagram-comparison max
  source-section-diagram = OnSection.diagram-comparison min
```
