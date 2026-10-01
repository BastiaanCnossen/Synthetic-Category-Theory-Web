# The interval deformations of the arrow category

Precomposition with maximum and minimum, followed by currying the square,
gives the transformations used in `lem:Evaluation_Map_Is_Left_Reflector`.
The endpoint comparisons below identify their sources and targets with the
identity and the constant-arrow functors. Their normalized evaluation and
section equations are separate proof obligations.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)

open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)

module At (C : CAT) where
  module Universal = Units.Universal 𝒯 M ℱ P I E C using (identity-evaluation; constant-evaluation)
  module Constant (v : Obj-abs [1]) where
    pre : MAP (Ar C) (Ar C)
    pre = funPre (const v)
    constants : MAP (Ar C) (Ar C)
    constants = identityArrow ∘ evaluate v

    coordinate : (productMap (id (Ar C)) (const {P = [1]} v)) =₁ (insert v ∘ pr₁)
    coordinate = (pair-pre (id (Ar C)) (const v) pr₁) ⁻¹ ∙
      pair-cong (idIso (id (Ar C) ∘ pr₁)) ((const-pre v pr₁) ⁻¹ ∙ const-pre v pr₂)

    pre-uncurried : funUncurry pre =₁ (evaluate v ∘ pr₁)
    pre-uncurried = (comp-assoc pr₁ (insert v) funEval) ⁻¹ ∙
      ((funEval ◁ coordinate) ∙ funPre-β (const v))

    constants-uncurried : funUncurry constants =₁ (evaluate v ∘ pr₁)
    constants-uncurried = pair-β₁ (evaluate v ∘ pr₁) (id [1] ∘ pr₂) ∙
      ((funCurry-β (pr₁ {C} {[1]}) ▷ productMap (evaluate v) (id [1])) ∙
        funUncurry-restrict identityArrow (evaluate v))

    abstract
      comparison : pre =₁ constants
      comparison = funIsoReflect pre constants (constants-uncurried ⁻¹ ∙ pre-uncurried)

      comparison-β : funUncurryIso comparison =₂ (constants-uncurried ⁻¹ ∙ pre-uncurried)
      comparison-β = funIsoReflect-β pre constants (constants-uncurried ⁻¹ ∙ pre-uncurried)

  module Deformation (h : MAP ([1] × [1]) [1]) where
    module Curry = Squares.At 𝒯 M ℱ (funPre {D = C} h) using (nested; module Vertical)
    arrow : MAP (Ar C) (Ar (Ar C))
    arrow = Curry.nested

    module Side (v : Obj-abs [1]) where
      side : MAP (Ar C) (Ar C)
      side = funPre (insert v) ∘ funPre h
      image : funUncurry side =₁ (funEval ∘ productMap (id (Ar C)) (h ∘ insert v))
      image = (funEval ◁ productRestriction-comp (Ar C) (insert v) h) ∙
        (comp-assoc (productMap (id (Ar C)) (insert v)) (productMap (id (Ar C)) h) funEval ∙
          ((funPre-β h ▷ productMap (id (Ar C)) (insert v)) ∙
            funPre-uncurry (insert v) (funPre h)))

      module Identity (α : (h ∘ insert v) =₁ id [1]) where
        diagram-image : funUncurry side =₁ funEval
        diagram-image = Universal.identity-evaluation ∙
          ((funEval ◁ productMap-cong (idIso (id (Ar C))) α) ∙ image)
        raw = (funUncurry-id [1] C) ⁻¹ ∙ diagram-image
        abstract
          comparison : side =₁ id (Ar C)
          comparison = funIsoReflect side (id (Ar C)) raw
          comparison-β : funUncurryIso comparison =₂ raw
          comparison-β = funIsoReflect-β side (id (Ar C)) raw

      module ConstantAt (x : Obj-abs [1]) (α : (h ∘ insert v) =₁ const x) where
        diagram-image : funUncurry side =₁ (evaluate x ∘ pr₁)
        diagram-image = Universal.constant-evaluation x ∙
          ((funEval ◁ productMap-cong (idIso (id (Ar C))) α) ∙ image)
        raw = (Constant.constants-uncurried x) ⁻¹ ∙ diagram-image
        abstract
          comparison : side =₁ (identityArrow ∘ evaluate x)
          comparison = funIsoReflect side (identityArrow ∘ evaluate x) raw
          comparison-β : funUncurryIso comparison =₂ raw
          comparison-β = funIsoReflect-β side (identityArrow ∘ evaluate x) raw

  module Maximum = Deformation max using (arrow; module Curry; module Side)
  module Minimum = Deformation min using (arrow; module Curry; module Side)
  module MaximumSource = Maximum.Side.Identity zero max-right-zero using (comparison; comparison-β)
  module MaximumTarget = Maximum.Side.ConstantAt one one max-right-one using (comparison; comparison-β)
  module MinimumSource = Minimum.Side.ConstantAt zero zero min-right-zero using (comparison; comparison-β)
  module MinimumTarget = Minimum.Side.Identity one min-right-one using (comparison; comparison-β)

  target-unit : MorphismExpression (id (Ar C)) (identityArrow ∘ ev₁)
  target-unit = record
    { arrow = Maximum.arrow
    ; source-frame = MaximumSource.comparison ∙ Maximum.Curry.Vertical.boundary zero
    ; target-frame = MaximumTarget.comparison ∙ Maximum.Curry.Vertical.boundary one }

  source-counit : MorphismExpression (identityArrow ∘ ev₀) (id (Ar C))
  source-counit = record
    { arrow = Minimum.arrow
    ; source-frame = MinimumSource.comparison ∙ Minimum.Curry.Vertical.boundary zero
    ; target-frame = MinimumTarget.comparison ∙ Minimum.Curry.Vertical.boundary one }
```
