# Uncurrying composition of triangles

Uncurrying a triangle after changing its source agrees with composing
the two uncurried triangles. The comparison is the usual substitution
comparison on the underlying functors, with its base triangle retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (compose-source-change; compose-source-change-underlying)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingRestriction 𝒯 M ℱ P using (module Restrict)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)

abstract
  change-structure : {K S C B : CAT} (r : MAP C B)
    {f g : MAP K (Fun S B)} (α : f =₁ g) (v : FunctorOver f (funPost r)) →
    FunctorOverIso (Triangle.value r g (change-source α v))
      (change-source (funUncurryIso α) (Triangle.value r f v))
  change-structure r {f} {g} α v = triangle-identification _ _ _
    (isoComp-assoc-at (funUncurryIso α) (funUncurryIso (FunctorLift.comparison v))
      ((funPost-uncurry r (FunctorLift.lift v)) ⁻¹) ∙
      isoComp-cong (funUncurryIso-comp α (FunctorLift.comparison v))
        (idIso ((funPost-uncurry r (FunctorLift.lift v)) ⁻¹)))

  change-structure-underlying : {K S C B : CAT} (r : MAP C B)
    {f g : MAP K (Fun S B)} (α : f =₁ g) (v : FunctorOver f (funPost r)) →
    FunctorOverIso.underlying (change-structure r α v) =₂ idIso (funUncurry (FunctorLift.lift v))
  change-structure-underlying r α v = idIso _

module Composite {K L S C B : CAT} (r : MAP C B)
  {f : MAP K (Fun S B)} {g : MAP L (Fun S B)}
  (u : FunctorOver g f) (v : FunctorOver f (funPost r)) where
  h = FunctorLift.lift u
  α = FunctorLift.comparison u
  module Restricted = Restrict r f h v using (restricted; insertion; comparison; comparison-underlying)

  abstract
    comparison : FunctorOverIso (Triangle.value r g (compose-over v u))
      (compose-over (Triangle.value r f v) (Uncurry.value S B u))
    comparison = compose-iso-over
      (inverse-iso-over (compose-source-change (funUncurryIso α) Restricted.insertion (Triangle.value r f v)))
      (compose-iso-over (change-source-iso (funUncurryIso α) Restricted.comparison)
        (change-structure r α Restricted.restricted))
    comparison-underlying : FunctorOverIso.underlying comparison =₂
      funUncurry-restrict (FunctorLift.lift v) h
    comparison-underlying =
      let ℓ = funUncurry-restrict (FunctorLift.lift v) h
      in isoComp-unitˡ-at ℓ ∙
        isoComp-cong
          (inverse-identity _ ∙ (＝-inv ◁ compose-source-change-underlying
            (funUncurryIso α) Restricted.insertion (Triangle.value r f v)))
          (isoComp-unitʳ-at ℓ ∙
            isoComp-cong Restricted.comparison-underlying (change-structure-underlying r α Restricted.restricted))
```
