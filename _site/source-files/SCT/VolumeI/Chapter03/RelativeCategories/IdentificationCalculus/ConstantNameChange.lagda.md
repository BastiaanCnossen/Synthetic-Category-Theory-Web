# Changing the functor in a constant named family

Choose the identification between names by its prescribed uncurried
image. Its comparison with a constant family is then natural under every
parameter substitution. This choice is useful when changing the structure
functor in a relative functor category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Change {C S : CAT} {f g : MAP C S} (α : f =₁ g) where
  βf : funUncurry (nameFun f) =₁ (f ∘ pr₂ {C = One})
  βf = funCurry-β (f ∘ pr₂)
  βg : funUncurry (nameFun g) =₁ (g ∘ pr₂ {C = One})
  βg = funCurry-β (g ∘ pr₂)
  prescribed : funUncurry (nameFun f) =₁ funUncurry (nameFun g)
  prescribed = βg ⁻¹ ∙ ((α ▷ pr₂) ∙ βf)
  named : nameFun f =₁ nameFun g
  named = funIsoReflect (nameFun f) (nameFun g) prescribed

  abstract
    image : (βg ∙ funUncurryIso named) =₂ ((α ▷ pr₂) ∙ βf)
    image = cancel-inverse βg ((α ▷ pr₂) ∙ βf) ∙
      isoComp-cong (idIso βg) (funIsoReflect-β (nameFun f) (nameFun g) prescribed)

  module At {X : CAT} (u : MAP X One) where
    R : MAP (X × C) (One × C)
    R = productMap u (id C)
    δf = parameter-over u f
    δg = parameter-over u g
    Af = funUncurry-restrict (nameFun f) u
    Ag = funUncurry-restrict (nameFun g) u
    groupedf = δf ∙ ((βf ▷ R) ∙ Af)
    groupedg = δg ∙ ((βg ▷ R) ∙ Ag)

    abstract
      normalize : (h : MAP C S) →
        (parameter-over u h ∙ ((funCurry-β (h ∘ pr₂ {C = One}) ▷ R) ∙ funUncurry-restrict (nameFun h) u)) =₂
          uncurry-constant-name h u
      normalize h = isoComp-assoc-at (h ◁ parameter-base u C) (comp-assoc R pr₂ h)
        ((funCurry-β (h ∘ pr₂ {C = One}) ▷ R) ∙ funUncurry-restrict (nameFun h) u)

      beta-square : ((βg ▷ R) ∙ (funUncurryIso named ▷ R)) =₂ (((α ▷ pr₂) ▷ R) ∙ (βf ▷ R))
      beta-square = preWhisker-isoComp-at (α ▷ pr₂) βf R ∙
        ((preWhisker R ◁ image) ∙ (preWhisker-isoComp-at βg (funUncurryIso named) R) ⁻¹)

      comparison : (uncurry-constant-name g u ∙ funUncurryIso (named ▷ u)) =₂
        ((α ▷ pr₂ {C = X}) ∙ uncurry-constant-name f u)
      comparison = isoComp-cong (idIso (α ▷ pr₂)) (normalize f) ∙
        (paste-iso-squares ((βf ▷ R) ∙ Af) ((βg ▷ R) ∙ Ag) δf δg
          (funUncurryIso (named ▷ u)) ((α ▷ pr₂) ▷ R) (α ▷ pr₂)
          (paste-iso-squares Af Ag (βf ▷ R) (βg ▷ R)
            (funUncurryIso (named ▷ u)) (funUncurryIso named ▷ R) ((α ▷ pr₂) ▷ R)
            (funUncurry-restrict-inputs named u) beta-square)
          (lift-base-outer pr₂ pr₂ R (parameter-base u C) α) ∙
          isoComp-cong ((normalize g) ⁻¹) (idIso (funUncurryIso (named ▷ u))))
```
