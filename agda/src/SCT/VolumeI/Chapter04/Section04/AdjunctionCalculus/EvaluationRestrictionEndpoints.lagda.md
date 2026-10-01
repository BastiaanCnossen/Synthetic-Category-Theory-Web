# Endpoint frames of normalized restriction maps

Identity and constant shape restrictions have the expected evaluated
frames. The normalization uses the retained uncurried comparisons and the
existing restriction-endpoint calculus, including the constant-arrow
frame rather than only the constant diagram.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationRestrictionEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformations as Deformations
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationRestrictionFactorization as Factors
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles as Units
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEdgeEndpoints as Routes
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.IdentityRestrictionEvaluation as IdentityBase
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.ConstantRestrictionEvaluation as ConstantBase
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.UniversalArrowEvaluation as Universal
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison as ConstantIdentity
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I using (constant-frame)

module At (C : CAT) (d : MAP [1] ([1] × [1])) (h : MAP ([1] × [1]) [1]) where
  module U = Units.Universal 𝒯 M ℱ P I E C using (identity-evaluation; constant-evaluation)
  module D = Deformations.At 𝒯 M ℱ P I E C using (module Constant)
  X = Ar C

  module Identity (α : (h ∘ d) =₁ id [1]) (x : Obj-abs [1]) where
    module F = Factors.At.Restriction 𝒯 M ℱ P I E C d h (id [1]) α
    module N = F.Normalized (id X) funEval (funUncurry-id [1] C) U.identity-evaluation
    diagram = U.identity-evaluation ∙ (F.shape-image ∙ F.image)
    module Reflected = Units.ReflectedEndpoint 𝒯 M ℱ P I E x F.side (id X)
      (funUncurry-id [1] C) diagram N.direct N.direct-β
    module Route = Routes.At 𝒯 M ℱ P {C = C} d h x (id [1]) α x (comp-unitˡ x)
    module Base = IdentityBase.At 𝒯 M ℱ {C = C} x
    module Output = Route.Output U.identity-evaluation (idIso (evaluate {C = C} x))
      (Base.comparison ∙ isoComp-unitˡ-at (U.identity-evaluation ▷ insert {X = X} x))

    abstract
      endpoint : (comp-unitʳ (evaluate {C = C} x) ∙ (evaluate x ◁ N.direct)) =₂
        (evaluate-cong Route.endpoint ∙ Route.route)
      endpoint = Output.normalize ∙
        ((isoComp-unitˡ-at ((diagram ▷ insert x) ∙ evaluate-uncurry x F.side)) ⁻¹ ∙
          (Reflected.endpoint ∙
            isoComp-cong ((Universal.Universal.endpoint 𝒯 M ℱ {C = C} x) ⁻¹)
              (idIso (evaluate x ◁ N.direct))))

  module Constant (z : Obj-abs [1]) (α : (h ∘ d) =₁ const z) (x : Obj-abs [1]) where
    module F = Factors.At.Restriction 𝒯 M ℱ P I E C d h (const z) α
    β = D.Constant.constants-uncurried z
    module N = F.Normalized (identityArrow ∘ evaluate z) (evaluate z ∘ pr₁) β (U.constant-evaluation z)
    diagram = U.constant-evaluation z ∙ (F.shape-image ∙ F.image)
    module Reflected = Units.ReflectedEndpoint 𝒯 M ℱ P I E x F.side (identityArrow ∘ evaluate z)
      β diagram N.direct N.direct-β
    module Route = Routes.At 𝒯 M ℱ P {C = C} d h x (const z) α z (constant-boundary x z)
    module Base = ConstantBase.At 𝒯 M ℱ {C = C} x z
    finish = identity-boundary x (evaluate {C = C} z)
    frame = constant-frame (evaluate x) (evaluate-constant x) (evaluate {C = C} z)
    middle = (β ▷ insert x) ∙ evaluate-uncurry x (identityArrow ∘ evaluate {C = C} z)
    module Output = Route.Output (U.constant-evaluation z) finish Base.comparison

    abstract
      frame-normal : (finish ∙ middle) =₂ frame
      frame-normal = ConstantIdentity.At.Endpoint.normalized 𝒯 M ℱ P I E (evaluate {C = C} z) x

      endpoint : (frame ∙ (evaluate x ◁ N.direct)) =₂
        (evaluate-cong Route.endpoint ∙ Route.route)
      endpoint = Output.normalize ∙
        (isoComp-cong (idIso finish) Reflected.endpoint ∙
          (isoComp-assoc-at finish middle (evaluate x ◁ N.direct) ∙
            isoComp-cong (frame-normal ⁻¹) (idIso (evaluate x ◁ N.direct))))
```
