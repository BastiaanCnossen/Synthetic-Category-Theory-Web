# Relative currying and universal evaluation

The beta identification for a curried family is an identification over
the base. Its triangle is the restriction of the specified universal
evaluation triangle, including the product projection comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.EvaluationRestriction as Restriction

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.CurryingBeta
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (isoInverse-unique)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Beta {X C D S : CAT} (f : MAP C S) (g : MAP D S)
  (v : MAP (X × C) D) (over : (g ∘ v) =₁ (f ∘ pr₂)) where
  module Curried = Curry f g v over
  module Local = CurriedTriangle f g v over
  module Restricted = Restriction.Restriction 𝒯 M ℱ P Curried.functor
    (pullbackCone (funPost g) (nameFun f))

  comparison : (Evaluation.evaluate f g ∘ productMap Curried.functor (id C)) =₁ v
  comparison = Local.evaluation-with-image ∙ Restricted.ℓ ⁻¹

  abstract
    inverse-image : (g ◁ Restricted.ℓ ⁻¹) =₂ ((g ◁ Restricted.ℓ) ⁻¹)
    inverse-image = (isoInverse-unique (g ◁ Restricted.ℓ) (g ◁ Restricted.ℓ ⁻¹)
      (postWhisker-idIso g _ ∙
        ((postWhisker g ◁ isoComp-inverseˡ-at Restricted.ℓ) ∙
          (postWhisker-isoComp-at g (Restricted.ℓ ⁻¹) Restricted.ℓ) ⁻¹))) ⁻¹

    over-comparison : (over ∙ (g ◁ comparison)) =₂ Restricted.target
    over-comparison = cancel-right (g ◁ Restricted.ℓ) Restricted.target ∙
      (isoComp-cong ((Restricted.comparison) ⁻¹ ∙ Local.native-beta)
        (idIso ((g ◁ Restricted.ℓ) ⁻¹)) ∙
        ((isoComp-assoc-at over (g ◁ Local.evaluation-with-image)
          ((g ◁ Restricted.ℓ) ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso over)
            (isoComp-cong (idIso (g ◁ Local.evaluation-with-image)) inverse-image ∙
              postWhisker-isoComp-at g Local.evaluation-with-image (Restricted.ℓ ⁻¹))))

  restricted-evaluation : FunctorOver (f ∘ pr₂) g
  restricted-evaluation = record
    { lift = Evaluation.evaluate f g ∘ productMap Curried.functor (id C)
    ; comparison = Restricted.target }

  original : FunctorOver (f ∘ pr₂) g
  original = record { lift = v ; comparison = over }

  beta : FunctorOverIso restricted-evaluation original
  beta = record { underlying = comparison ; compatible = over-comparison }
```
