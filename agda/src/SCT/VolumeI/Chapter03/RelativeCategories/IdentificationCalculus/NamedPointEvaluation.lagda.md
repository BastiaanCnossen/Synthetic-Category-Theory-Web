# Evaluating a named relative functor

Evaluating the cone naming a relative functor recovers that functor over
the base. The underlying comparison is `decode-nameFun`; its triangle
compatibility follows from the constant-name unit law and the specified
postcomposition comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameUnit as ConstantUnit
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.PostNamingCoherence as PostNaming

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamedPointEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse; inverse-composite)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (post-nameFun; decodeFun-post)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingCoherence 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingLaws 𝒯 M ℱ using (nameFunIso-square)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P using (module Triangles)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (evalMatch)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Named {C D S : CAT} (f : MAP C S) (g : MAP D S) (u : FunctorOver f g) where
  h : MAP C D
  h = FunctorLift.lift u
  θ : (g ∘ h) =₁ f
  θ = FunctorLift.comparison u
  module K = ConstantUnit.Unit 𝒯 M ℱ P f
  i : MAP C (One × C)
  i = oneProduct-in C
  ρ : (nameFun f ∘ id One) =₁ nameFun f
  ρ = comp-unitʳ (nameFun f)
  π : (funPost g ∘ nameFun h) =₁ nameFun (g ∘ h)
  π = post-nameFun g h
  τ : (funPost g ∘ nameFun h) =₁ (nameFun f ∘ id One)
  τ = Cone.match (Over.Name.cone f g u)
  η : funUncurry (funPost g ∘ nameFun h) =₁ (g ∘ funUncurry (nameFun h))
  η = funPost-uncurry g (nameFun h)
  κ : decodeFun (funPost g ∘ nameFun h) =₁ (g ∘ decodeFun (nameFun h))
  κ = decodeFun-post g (nameFun h)
  A : ((g ∘ funUncurry (nameFun h)) ∘ i) =₁ (g ∘ decodeFun (nameFun h))
  A = comp-assoc i (funUncurry (nameFun h)) g
  δ : ((f ∘ pr₂ {C = One}) ∘ i) =₁ f
  δ = K.Reduce.reduce f
  κi : (funUncurry (nameFun f ∘ id One) ∘ i) =₁ ((f ∘ pr₂ {C = One}) ∘ i)
  κi = uncurry-constant-name f (id One) ▷ i
  τi : (funUncurry (funPost g ∘ nameFun h) ∘ i) =₁ (funUncurry (nameFun f ∘ id One) ∘ i)
  τi = funUncurryIso τ ▷ i

  abstract
    named-matching : (ρ ∙ τ) =₂ (nameFunIso θ ∙ π)
    named-matching = cancel-inverse ρ (nameFunIso θ ∙ π) ∙
      isoComp-cong (idIso ρ) (Triangles.triangleNameMap-at f g h θ)

    evaluated-matching : (evalMatch (Over.Name.cone f g u) ▷ i) =₂
      (κi ∙ (τi ∙ (η ▷ i) ⁻¹))
    evaluated-matching = isoComp-cong (idIso κi)
        (isoComp-cong (idIso τi) (pre-inverse η i) ∙
          preWhisker-isoComp-at (funUncurryIso τ) (η ⁻¹) i) ∙
      preWhisker-isoComp-at
        (uncurry-constant-name f (id One))
        (funUncurryIso τ ∙ η ⁻¹) i

    decoded-matching : FunctorLift.comparison (PointTriangle (Over.Name.cone f g u)) =₂
      ((decode-nameFun f ∙ decodeFunIso ρ) ∙ (decodeFunIso τ ∙ κ ⁻¹))
    decoded-matching =
      isoComp-cong K.decoded
        (isoComp-cong ((decodeFunIso-at τ) ⁻¹) ((inverse-composite A (η ▷ i)) ⁻¹)) ∙
      ((isoComp-assoc-at δ κi (τi ∙ ((η ▷ i) ⁻¹ ∙ A ⁻¹))) ⁻¹ ∙
        (isoComp-cong (idIso δ)
          (isoComp-cong (idIso κi) (isoComp-assoc-at τi ((η ▷ i) ⁻¹) (A ⁻¹)) ∙
            isoComp-assoc-at κi (τi ∙ (η ▷ i) ⁻¹) (A ⁻¹)) ∙
          isoComp-cong (idIso δ) (isoComp-cong evaluated-matching (idIso (A ⁻¹)))))

    decoded-name-composition : (decodeFunIso ρ ∙ decodeFunIso τ) =₂
      (decodeFunIso (nameFunIso θ) ∙ decodeFunIso π)
    decoded-name-composition = decodeFunIso-comp (nameFunIso θ) π ∙
      ((decodeFun-isoMap _ _ ◁ named-matching) ∙ (decodeFunIso-comp ρ τ) ⁻¹)

    prefix : ((decode-nameFun f ∙ decodeFunIso ρ) ∙ decodeFunIso τ) =₂
      (θ ∙ ((g ◁ decode-nameFun h) ∙ κ))
    prefix = isoComp-cong (idIso θ) (PostNaming.Normalization.comparison 𝒯 M ℱ g h) ∙
      (isoComp-assoc-at θ (decode-nameFun (g ∘ h)) (decodeFunIso π) ∙
        (isoComp-cong (nameFunIso-square θ) (idIso (decodeFunIso π)) ∙
          ((isoComp-assoc-at (decode-nameFun f) (decodeFunIso (nameFunIso θ)) (decodeFunIso π)) ⁻¹ ∙
            (isoComp-cong (idIso (decode-nameFun f)) decoded-name-composition ∙
              isoComp-assoc-at (decode-nameFun f) (decodeFunIso ρ) (decodeFunIso τ)))))

    triangle : FunctorLift.comparison (PointTriangle (Over.Name.cone f g u)) =₂
      (θ ∙ (g ◁ decode-nameFun h))
    triangle = cancel-right κ (θ ∙ (g ◁ decode-nameFun h)) ∙
      (isoComp-cong
        ((isoComp-assoc-at θ (g ◁ decode-nameFun h) κ) ⁻¹ ∙ prefix) (idIso (κ ⁻¹)) ∙
        ((isoComp-assoc-at (decode-nameFun f ∙ decodeFunIso ρ) (decodeFunIso τ) (κ ⁻¹)) ⁻¹ ∙
          decoded-matching))

    comparison : FunctorOverIso (PointTriangle (Over.Name.cone f g u)) u
    comparison = record { underlying = decode-nameFun h ; compatible = triangle ⁻¹ }
```
