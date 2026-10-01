# The specified endpoints of the direct unit edges

The directly reflected identity and constant edges retain their original
frames. Their endpoint images are now expressed using the restriction
route and the specified shape endpoint identification. These formulas
apply to either degeneracy and to each of its three edges.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles as Direct
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEdgeEndpoints as Routes
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.IdentityRestrictionEvaluation as Identity
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.ConstantRestrictionEvaluation as Constant

module SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DegenerateCocones 𝒯 M ℱ P I E

-- Restructured: every module application is restricted to the names used
-- here or downstream (DirectUnitPresentations uses `endpoint` and
-- `Route.endpoint`). `Route` and `Output` stay module applications, so that
-- the type of `Output.normalize` is stated in the same copied names as the
-- statement of `endpoint`; with direct calls the two only agree after
-- unfolding, which made this module almost twice as slow.
module Universal (C : CAT) where
  module Original = Direct.Universal 𝒯 M ℱ P I E C
    using (constant-evaluation; identity-evaluation; module Degeneracy)
  X = Ar C

  module Degeneracy (s : MAP [2] [1]) where
    module Triangle = Original.Degeneracy s
      using (triangle; module ConstantEdge; module IdentityEdge)

    module IdentityEdge (d : MAP [1] [2]) (α : (s ∘ d) =₁ id [1])
      (x : Obj-abs [1]) where
      module Edge = Triangle.IdentityEdge d α
        using (comparison; diagram-image; endpoint)
      module Route = Routes.At 𝒯 M ℱ P {C = C} d s x (id [1]) α x (comp-unitˡ x)
        using (endpoint; route; module Output)
      module Base = Identity.At 𝒯 M ℱ {C = C} x
        using (comparison)
      module Output = Route.Output Original.identity-evaluation (idIso (evaluate {C = C} x))
        (Base.comparison ∙ isoComp-unitˡ-at (Original.identity-evaluation ▷ insert {X = X} x))
        using (normalize)

      abstract
        endpoint :
          (comp-unitʳ (evaluate {C = C} x) ∙ (evaluate x ◁ Edge.comparison)) =₂
          (evaluate-cong Route.endpoint ∙ Route.route)
        endpoint = Output.normalize ∙
          ((isoComp-unitˡ-at ((Edge.diagram-image ▷ insert x) ∙
            evaluate-uncurry x (funPre d ∘ Triangle.triangle))) ⁻¹ ∙ Edge.endpoint x)

    module ConstantEdge (d : MAP [1] [2]) (z : Obj-abs [1])
      (α : (s ∘ d) =₁ const z) (x : Obj-abs [1]) where
      module Edge = Triangle.ConstantEdge d z α
        using (comparison; endpoint)
      module Route = Routes.At 𝒯 M ℱ P {C = C} d s x (const z) α z (constant-boundary x z)
        using (endpoint; route; module Output)
      module Base = Constant.At 𝒯 M ℱ {C = C} x z
        using (comparison)
      finish = identity-boundary x (evaluate {C = C} z)
      frame = finish ∙ evaluate-curry x (evaluate {C = C} z ∘ pr₁)
      module Output = Route.Output (Original.constant-evaluation z) finish Base.comparison
        using (normalize)

      abstract
        endpoint : (frame ∙ (evaluate {C = C} x ◁ Edge.comparison)) =₂
          (evaluate-cong Route.endpoint ∙ Route.route)
        endpoint = Output.normalize ∙
          (isoComp-cong (idIso finish) (Edge.endpoint x) ∙
            isoComp-assoc-at finish (evaluate-curry x (evaluate z ∘ pr₁))
              (evaluate x ◁ Edge.comparison))
```
