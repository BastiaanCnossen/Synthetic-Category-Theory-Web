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
import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles as Direct
import SCT.VolumeI.Chapter02.Section02.RestrictionEdgeEndpoints as Routes
import SCT.VolumeI.Chapter02.Section02.IdentityRestrictionEvaluation as Identity
import SCT.VolumeI.Chapter02.Section02.ConstantRestrictionEvaluation as Constant

module SCT.VolumeI.Chapter02.Section02.DirectUnitEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.DegenerateCocones 𝒯 M ℱ P I E

module Universal (C : CAT) where
  module Original = Direct.Universal 𝒯 M ℱ P I E C
  X = Ar C

  module Degeneracy (s : MAP [2] [1]) where
    module Triangle = Original.Degeneracy s

    module IdentityEdge (d : MAP [1] [2]) (α : (s ∘ d) =₁ id [1])
      (x : Obj-abs [1]) where
      module Edge = Triangle.IdentityEdge d α
      module Route = Routes.At 𝒯 M ℱ P {C = C} d s x (id [1]) α x (comp-unitˡ x)
      module Base = Identity.At 𝒯 M ℱ {C = C} x
      module Output = Route.Output Original.identity-evaluation (idIso (evaluate {C = C} x))
        (Base.comparison ∙ isoComp-unitˡ-at (Original.identity-evaluation ▷ insert {X = X} x))

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
      module Route = Routes.At 𝒯 M ℱ P {C = C} d s x (const z) α z (constant-boundary x z)
      module Base = Constant.At 𝒯 M ℱ {C = C} x z
      finish = identity-boundary x (evaluate {C = C} z)
      frame = finish ∙ evaluate-curry x (evaluate {C = C} z ∘ pr₁)
      module Output = Route.Output (Original.constant-evaluation z) finish Base.comparison

      abstract
        endpoint : (frame ∙ (evaluate {C = C} x ◁ Edge.comparison)) =₂
          (evaluate-cong Route.endpoint ∙ Route.route)
        endpoint = Output.normalize ∙
          (isoComp-cong (idIso finish) (Edge.endpoint x) ∙
            isoComp-assoc-at finish (evaluate-curry x (evaluate z ∘ pr₁))
              (evaluate x ◁ Edge.comparison))
```
