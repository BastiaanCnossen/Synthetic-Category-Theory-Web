# The projection of an uncurried family

After reassociating the parameter product, the uncurried source
projection agrees over the base with the ordinary second projection.
This retains the image used when comparing two parameter substitutions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.UncurriedFamilyProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection 𝒯 M ℱ P using (projection)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Family)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Project {K S C B : CAT} (r : MAP C B) (f : MAP K (Fun S B)) (X : CAT) where
  module Flat = Family r f X using (insertion; regroup; projection; remove-parameter)
  q = Uncurry.value S B (projection f X)
  source = compose-over q Flat.insertion
  target = projection (funUncurry f) X
  R = Flat.regroup
  ρ = funUncurry-restrict f (pr₂ {C = X}) ▷ R
  A = comp-assoc R Flat.projection (funUncurry f)
  χ = funUncurry f ◁ Flat.remove-parameter

  abstract
    restricted-triangle : (FunctorLift.comparison q ▷ R) =₂ (ρ ⁻¹)
    restricted-triangle = isoComp-unitˡ-at (ρ ⁻¹) ∙
      (isoComp-cong
        (preWhisker-idIso (funUncurry (f ∘ pr₂)) R ∙ (preWhisker R ◁ funUncurryIso-id (f ∘ pr₂)))
        (pre-inverse (funUncurry-restrict f pr₂) R) ∙
        preWhisker-isoComp-at (funUncurryIso (idIso (f ∘ pr₂))) ((funUncurry-restrict f pr₂) ⁻¹) R)

    triangle-normal : FunctorLift.comparison source =₂ χ
    triangle-normal = cancel-right (A ∙ ρ) χ ∙
      isoComp-cong (idIso (χ ∙ (A ∙ ρ)))
        ((inverse-composite A ρ) ⁻¹ ∙ isoComp-cong restricted-triangle (idIso (A ⁻¹)))

    comparison : FunctorOverIso source target
    comparison = record { underlying = Flat.remove-parameter
      ; compatible = triangle-normal ⁻¹ ∙ isoComp-unitˡ-at χ }
```
