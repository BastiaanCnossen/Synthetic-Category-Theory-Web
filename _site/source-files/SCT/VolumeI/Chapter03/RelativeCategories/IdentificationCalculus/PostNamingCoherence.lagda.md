# Decoding the postcomposition naming comparison

The chosen comparison between postcomposition of a name and the name of
a composite has a specified uncurried image. Reducing the terminal
coordinate gives exactly the usual postcomposition comparison for
decoding. The calculation retains both curry beta identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointReductionCoherence as PointReduction

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.PostNamingCoherence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in; oneProduct-retraction)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ
  using (post-nameFun; post-nameFun-uncurried; decodeFun-post)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (reassociateFour; cancel-inverse)

module Normalization {B C D : CAT} (g : MAP C D) (h : MAP B C) where
  i : MAP B (One × B)
  i = oneProduct-in B
  module Reduce = PointReduction.Reduction 𝒯 i (pr₂ {C = One}) (oneProduct-retraction B)
  module ReducePost = Reduce.Post h g
  β : funUncurry (nameFun h) =₁ (h ∘ (pr₂ {C = One}))
  β = funCurry-β (h ∘ (pr₂ {C = One}))
  γ : funUncurry (nameFun (g ∘ h)) =₁ ((g ∘ h) ∘ (pr₂ {C = One}))
  γ = funCurry-β ((g ∘ h) ∘ (pr₂ {C = One}))
  η : funUncurry (funPost g ∘ nameFun h) =₁ (g ∘ funUncurry (nameFun h))
  η = funPost-uncurry g (nameFun h)
  assoc : ((g ∘ h) ∘ (pr₂ {C = One})) =₁ (g ∘ (h ∘ (pr₂ {C = One})))
  assoc = comp-assoc (pr₂ {C = One}) h g

  abstract
    name-normal : {E : CAT} (f : MAP B E) →
      (Reduce.reduce f ∙ (funCurry-β (f ∘ (pr₂ {C = One})) ▷ i)) =₂ decode-nameFun f
    name-normal f = isoComp-cong (idIso (comp-unitʳ f))
        (isoComp-assoc-at (f ◁ oneProduct-retraction B) (comp-assoc i (pr₂ {C = One}) f) (funCurry-β (f ∘ (pr₂ {C = One})) ▷ i)) ∙
      isoComp-assoc-at (comp-unitʳ f) ((f ◁ oneProduct-retraction B) ∙ comp-assoc i (pr₂ {C = One}) f)
        (funCurry-β (f ∘ (pr₂ {C = One})) ▷ i)

    raw-at : (post-nameFun-uncurried g h ▷ i) =₂
      ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))))
    raw-at = isoComp-cong (pre-inverse γ i)
      (isoComp-cong (pre-inverse assoc i) (preWhisker-isoComp-at (g ◁ β) η i) ∙
        preWhisker-isoComp-at (assoc ⁻¹) ((g ◁ β) ∙ η) i) ∙
      preWhisker-isoComp-at (γ ⁻¹) (assoc ⁻¹ ∙ ((g ◁ β) ∙ η)) i

    first : (decode-nameFun (g ∘ h) ∙ decodeFunIso (post-nameFun g h)) =₂
      ((Reduce.reduce (g ∘ h) ∙ (γ ▷ i)) ∙
        ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))))
    first = isoComp-cong ((name-normal (g ∘ h)) ⁻¹) (raw-at ∙ post-nameFun-decode-image g h)

    cancelled :
      ((Reduce.reduce (g ∘ h) ∙ (γ ▷ i)) ∙
        ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))))) =₂
      ((Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))
    cancelled = (isoComp-assoc-at (Reduce.reduce (g ∘ h)) ((assoc ▷ i) ⁻¹) (((g ◁ β) ▷ i) ∙ (η ▷ i))) ⁻¹ ∙
      (isoComp-cong (idIso (Reduce.reduce (g ∘ h)))
        (cancel-inverse (γ ▷ i) ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))) ∙
        isoComp-assoc-at (Reduce.reduce (g ∘ h)) (γ ▷ i)
          ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))))

    prefix : (Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) =₂
      ((g ◁ Reduce.reduce h) ∙ comp-assoc i (h ∘ (pr₂ {C = One})) g)
    prefix = ReducePost.cancel-associator ∙
      isoComp-cong (idIso (Reduce.reduce (g ∘ h))) ((pre-inverse assoc i) ⁻¹)

    middle : ((Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))) =₂
      ((g ◁ Reduce.reduce h) ∙ ((g ◁ (β ▷ i)) ∙ decodeFun-post g (nameFun h)))
    middle = isoComp-cong (idIso (g ◁ Reduce.reduce h))
        (isoComp-assoc-at (g ◁ (β ▷ i)) (comp-assoc i (funUncurry (nameFun h)) g) (η ▷ i)) ∙
      (isoComp-cong (idIso (g ◁ Reduce.reduce h))
        (isoComp-cong (whisker-mixed-at β i g) (idIso (η ▷ i))) ∙
        (reassociateFour (g ◁ Reduce.reduce h) (comp-assoc i (h ∘ (pr₂ {C = One})) g) ((g ◁ β) ▷ i) (η ▷ i) ∙
          isoComp-cong prefix (idIso (((g ◁ β) ▷ i) ∙ (η ▷ i)))))

    last : ((g ◁ Reduce.reduce h) ∙ ((g ◁ (β ▷ i)) ∙ decodeFun-post g (nameFun h))) =₂
      ((g ◁ decode-nameFun h) ∙ decodeFun-post g (nameFun h))
    last = isoComp-cong (postWhisker g ◁ name-normal h) (idIso (decodeFun-post g (nameFun h))) ∙
      (isoComp-cong ((postWhisker-isoComp-at g (Reduce.reduce h) (β ▷ i)) ⁻¹)
        (idIso (decodeFun-post g (nameFun h))) ∙
        (isoComp-assoc-at (g ◁ Reduce.reduce h) (g ◁ (β ▷ i)) (decodeFun-post g (nameFun h))) ⁻¹)

    comparison : (decode-nameFun (g ∘ h) ∙ decodeFunIso (post-nameFun g h)) =₂
      ((g ◁ decode-nameFun h) ∙ decodeFun-post g (nameFun h))
    comparison = last ∙ (middle ∙ (cancelled ∙ first))
```
