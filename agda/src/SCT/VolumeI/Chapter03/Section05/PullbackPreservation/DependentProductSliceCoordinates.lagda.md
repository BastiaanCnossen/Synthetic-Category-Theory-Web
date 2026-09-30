# Mapping coordinates for sliced evaluation

A relative functor to the pulled-back target projects to a functor to C
with a specified triangle in D. Restrict that triangle along the
cartesian base-change comparison. The resulting base functor is the
native evaluation of the specified map to the target dependent product.

The comparison is an equivalence, and its computation is recorded on
arbitrary families, with their triangles retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentProductSliceCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; family-identification)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Squares 𝒯 M ℱ P using (module Cartesian)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)

module PullbackCoordinates {A B C D Q : CAT} (ε : MAP Q D) (u : MAP C D)
  (r : MAP A Q) (e : MAP B D) (argument : FunctorOver e (ε ∘ r))
  (argument-isEquiv : IsEquiv (FunctorLift.lift argument)) where
  projection : MAP (Pullback u ε) Q
  projection = pullback₂
  module Arg = Argument argument using (family)
  module Target = PullbackTarget ε u r using (functor; functor-isEquiv; family-comparison)
  module Native = Families ε u r using (forward)
  module Restricted = Precompose u argument using (functor; family-comparison)
  module RestrictionEquivalence = Precompose.Equivalence u argument argument-isEquiv using (functor-isEquiv)
  functor : MAP (FunOver r projection) (FunOver e u)
  functor = Restricted.functor ∘ Target.functor
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = equiv-compose Target.functor Restricted.functor Target.functor-isEquiv
      RestrictionEquivalence.functor-isEquiv
    family-comparison : {X : CAT} (F : MAP X (FunOver r projection)) → FunctorOverIso
      (family e u (functor ∘ F))
      (compose-over (Native.forward (family r projection F)) (Arg.family X))
    family-comparison {X} F = compose-iso-over (prewhisker-over (Arg.family X) (Target.family-comparison F))
      (compose-iso-over (Restricted.family-comparison (Target.functor ∘ F))
        (family-identification e u (comp-assoc F Target.functor Restricted.functor)))
  maps : MAP (MapOver r projection) (MapOver e u)
  maps = mapPost functor
  abstract
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv

module Coordinates {S T C D K : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠD : DependentProduct p g) (u : FunctorOver f g)
  (k : MAP K (DependentProduct.category ΠD)) where
  πD : MAP (DependentProduct.category ΠD) T
  πD = DependentProduct.projection ΠD
  εD : MAP (Pullback πD p) D
  εD = FunctorLift.lift (DependentProduct.evaluation ΠD)
  q : MAP (Pullback πD p) (DependentProduct.category ΠD)
  q = pullback₁
  t : MAP K T
  t = πD ∘ k
  x : FunctorOver t πD
  x = record { lift = k ; comparison = idIso t }
  e : MAP (Pullback t p) D
  e = FunctorLift.lift (Currying.evaluate p g ΠD x)
  r : MAP (Pullback k q) (Pullback πD p)
  r = pullback₂
  target : CAT
  target = Pullback (FunctorLift.lift u) εD
  projection : MAP target (Pullback πD p)
  projection = pullback₂
  module Domain = Cartesian p x using (square; square-isPullback)
  abstract
    argument : FunctorOver e (εD ∘ r)
    argument = record { lift = pullbackLift Domain.square
      ; comparison = (εD ◁ pullbackLift-β₂ Domain.square) ∙ comp-assoc (pullbackLift Domain.square) r εD }
    argument-isEquiv : IsEquiv (FunctorLift.lift argument)
    argument-isEquiv = Domain.square-isPullback
    argument-underlying : FunctorLift.lift argument =₁ pullbackLift Domain.square
    argument-underlying = idIso (pullbackLift Domain.square)
    argument-computation : FunctorOverIso argument
      (record { lift = pullbackLift Domain.square
        ; comparison = (εD ◁ pullbackLift-β₂ Domain.square) ∙ comp-assoc (pullbackLift Domain.square) r εD })
    argument-computation = identity-iso-over argument
  open PullbackCoordinates εD (FunctorLift.lift u) r e argument argument-isEquiv public
    using (functor; functor-isEquiv; family-comparison; maps; maps-isEquiv)
```
