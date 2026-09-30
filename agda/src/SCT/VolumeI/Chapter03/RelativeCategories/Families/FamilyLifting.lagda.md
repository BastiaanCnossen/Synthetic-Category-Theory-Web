# Lifting a family identification with its prescribed image

The cone-recovery proof of relative family reflection can retain its
image. Lift the recovered cone comparison using the pullback's specified
identification lift, then apply the uncurrying beta rule to its left
projection. The resulting identification evaluates to the originally
specified native comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect-β)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (module Lift)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (evaluated-comparison)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (module Cones)

action : {X C D S : CAT} (f : MAP C S) (g : MAP D S) {F G : MAP X (FunOver f g)} →
  F =₁ G → FunctorOverIso (family f g F) (family f g G)
action f g α = evaluated-comparison (cone-action (pullbackCone (funPost g) (nameFun f)) α)

module Identification {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (F G : MAP X (FunOver f g)) (Φ : FunctorOverIso (family f g F) (family f g G)) where
  source = conePre F (pullbackCone (funPost g) (nameFun f))
  target = conePre G (pullbackCone (funPost g) (nameFun f))
  module Recovered = Cones source target Φ
  module Lifted = Lift F G Recovered.comparison
  comparison : F =₁ G
  comparison = Lifted.lift
  abstract
    image : FunctorOverIso.underlying (action f g comparison) =₂ FunctorOverIso.underlying Φ
    image = funIsoReflect-β (Cone.left source) (Cone.left target) (FunctorOverIso.underlying Φ) ∙
      (funUncurry-isoMap (Cone.left source) (Cone.left target) ◁ Lifted.left-image)
```
