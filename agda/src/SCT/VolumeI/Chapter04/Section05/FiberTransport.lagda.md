# Transport between fibers

Restrict the parameterized lift to a fixed morphism of the base and to
the whole source fiber. Its endpoint comparison gives an actual functor
to the target fiber. The construction retains the full pullback cone
comparison, hence its matching over the base as well as both projections.

This implements the fiber transport functors in
`sec:Covariant_Transport_For_Cocartesian_Fibrations`, in both variances.
Identity and composition laws for transport are separate results.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.FiberTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Transport 𝒯 M ℱ P I E S R public
open import SCT.VolumeI.Chapter02.Section01.AbsoluteMorphisms 𝒯 M ℱ P I
  using (morphism-expression)

module CovariantFiber {A B : CAT} (f : MAP A B) (w : Fibration.CocartesianFibration f)
  {x y : Obj-abs B} (β : Morphism x y) where
  source-fiber = Pullback f x
  target-fiber = Pullback f y
  object = pullback₁ {f = f} {x}
  parameter = pullback₂ {f = f} {x}
  absolute = retarget-expression (morphism-expression β) (const-One x) (const-One y)
  family = retarget-expression (restrict-expression absolute parameter)
    (pullbackMatch ⁻¹) (idIso (y ∘ parameter))
  module Lift = Covariant f w object (y ∘ parameter) family
    using (transport; target-frame; lifted-expression; lift-β)

  transport-cone : Cone f y source-fiber
  transport-cone = record
    { left = Lift.transport ; right = parameter ; match = Lift.target-frame }

  transport : MAP source-fiber target-fiber
  transport = pullbackLift transport-cone

  transport-β : ConeIso (conePre transport (pullbackCone f y)) transport-cone
  transport-β = pullbackLift-β transport-cone

  underlying : (pullback₁ ∘ transport) =₁ Lift.transport
  underlying = ConeIso.leftIso transport-β

  parameter-comparison : (pullback₂ ∘ transport) =₁ parameter
  parameter-comparison = ConeIso.rightIso transport-β

module ContravariantFiber {A B : CAT} (f : MAP A B) (w : Fibration.CartesianFibration f)
  {x y : Obj-abs B} (β : Morphism x y) where
  source-fiber = Pullback f y
  target-fiber = Pullback f x
  object = pullback₁ {f = f} {y}
  parameter = pullback₂ {f = f} {y}
  absolute = retarget-expression (morphism-expression β) (const-One x) (const-One y)
  family = retarget-expression (restrict-expression absolute parameter)
    (idIso (x ∘ parameter)) (pullbackMatch ⁻¹)
  module Lift = Contravariant f w (x ∘ parameter) object family
    using (transport; source-frame; lifted-expression; lift-β)

  transport-cone : Cone f x source-fiber
  transport-cone = record
    { left = Lift.transport ; right = parameter ; match = Lift.source-frame }

  transport : MAP source-fiber target-fiber
  transport = pullbackLift transport-cone

  transport-β : ConeIso (conePre transport (pullbackCone f x)) transport-cone
  transport-β = pullbackLift-β transport-cone

  underlying : (pullback₁ ∘ transport) =₁ Lift.transport
  underlying = ConeIso.leftIso transport-β

  parameter-comparison : (pullback₂ ∘ transport) =₁ parameter
  parameter-comparison = ConeIso.rightIso transport-β
```
