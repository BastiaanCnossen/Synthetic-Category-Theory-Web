# The Beck–Chevalley comparison on whole families

Restrict a family across the pullback pasting equivalence, or first
base-change it and then enter the original evaluation domain. These
operations agree over the old base. The proof combines the arbitrary
cone-pasting calculation with the parameterized pasting comparison;
no evaluation functor is needed for this geometric step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.Currying.ChangedConeAction 𝒯 M ℱ P using (module Changed)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RestrictedConeLifts 𝒯 M ℱ P using (module Restriction)
import SCT.VolumeI.Chapter03.Section05.Currying.ParameterizedPullbackPasting as ParameterPasting
import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyCones as Cones

module Family {S T S′ T′ D K X : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (g : MAP D T) (k : MAP K T′)
  (u : FunctorOver (k ∘ pr₂ {C = X}) (pullback₂ {f = g} {b})) where
  h = Cone.left square
  p′ = Cone.right square
  t : MAP (Pullback g b) T′
  t = pullback₂
  module Parameters = ParameterPasting.Pasted 𝒯 M ℱ P p b square square-isPullback k X
  module Source = Families b g k
  v = Source.forward u
  native-v = Target.forward b g (k ∘ pr₂ {C = X}) u
  module New = Change.At p′ k t u
  module Old = Change.At p (b ∘ k) g v
  module Geometric = Cones.Pasted 𝒯 M ℱ P p b square g (k ∘ pr₂ {C = X}) u New.parameter-cone
  open Parameters using (H; N; O; rN; rO; flatten-over)
  J = comp-assoc (pr₂ {C = X} {D = N}) rN h
  α = comp-assoc (pr₂ {C = X} {D = K}) k b
  argument = Parameters.Arg.family X
  source-argument = change-source J argument
  target-cone = Geometric.target
  flattened = PasteCones.flatten (k ∘ pr₂ {C = X}) b (coneSwap square) New.parameter-cone

  restriction-cones : ConeIso (conePre H Old.acted-cone) target-cone
  restriction-cones = coneIso-compose (Changed.comparison p (α ⁻¹) native-v flattened)
    (coneIso-compose (Action.map-iso p v Parameters.comparison)
      (Action.restriction p v H Old.parameter-cone))

  abstract
    restriction-right : ConeIso.rightIso restriction-cones =₂ FunctorLift.comparison source-argument
    restriction-right = isoComp-unitʳ-at (FunctorLift.comparison source-argument) ∙
      isoComp-unitˡ-at (FunctorLift.comparison source-argument ∙ idIso (Cone.right Old.parameter-cone ∘ H))

    restricted-lift : FunctorOverIso
      (compose-over (lift-triangle Old.acted-cone) source-argument) (lift-triangle target-cone)
    restricted-lift = Restriction.comparison Old.acted-cone target-cone source-argument restriction-cones restriction-right

    comparison : FunctorOverIso
      (change-source J (compose-over Old.pulled argument))
      (compose-over Geometric.Dom.into-over (postbase h New.pulled))
    comparison = compose-iso-over
      (inverse-iso-over (postwhisker-over Geometric.Dom.into-over (postbase-iso h New.action-comparison)))
      (compose-iso-over (inverse-iso-over Geometric.native-comparison)
        (compose-iso-over restricted-lift
          (compose-iso-over (inverse-iso-over (compose-source-change J argument (lift-triangle Old.acted-cone)))
            (change-source-iso J (prewhisker-over argument Old.action-comparison)))))
```
