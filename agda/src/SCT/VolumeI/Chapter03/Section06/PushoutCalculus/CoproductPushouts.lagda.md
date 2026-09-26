# Adjoining an unchanged summand

The square from `A → C` to `A ⊔ D → C ⊔ D` is a pushout. An extension
copairs the map from `C` with the supplied map from `D`. Lift its other
comparison with a prescribed first restriction, so compatibility with
the original matching follows by cancellation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoproductPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.IsomorphismRestriction 𝒯 M B using (module RestrictionLift)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Adjoin {A C : CAT} (f : MAP A C) (D : CAT) where
  sum-map : MAP (A ⊔ D) (C ⊔ D)
  sum-map = copair (in₁ ∘ f) in₂
  cocone : Cocone (in₁ {A} {D}) f (C ⊔ D)
  cocone = record { left = sum-map ; right = in₁ ; match = copair-β₁ (in₁ ∘ f) in₂ }
  square : Square (in₁ {A} {D}) f sum-map in₁
  square = record { commute = Cocone.match cocone }
  abstract
    second : {E : CAT} (h : MAP (C ⊔ D) E) → ((h ∘ sum-map) ∘ in₂) =₁ (h ∘ in₂)
    second h = (h ◁ copair-β₂ (in₁ ∘ f) in₂) ∙ comp-assoc in₂ sum-map h

  module Factor {E : CAT} (t : Cocone (in₁ {A} {D}) f E) where
    k = Cocone.left t
    v = Cocone.right t
    τ = Cocone.match t
    functor = copair v (k ∘ in₂)
    induced = coconePost functor cocone
    right = copair-β₁ v (k ∘ in₂)
    σ = Cocone.match induced
    desired = (right ▷ f) ∙ σ
    first = τ ⁻¹ ∙ desired
    other = copair-β₂ v (k ∘ in₂) ∙ second functor
    module Left = RestrictionLift (functor ∘ sum-map) k first other
    abstract
      compatible : (τ ∙ (Left.lift ▷ in₁)) =₂ desired
      compatible = cancel-inverse τ desired ∙ isoComp-cong (idIso τ) Left.left-image
      comparison : CoconeIso induced t
      comparison = record { leftIso = Left.lift ; rightIso = right ; compatible = compatible }

  abstract
    extensions : CoconeExtensionProperty cocone
    extensions = record
      { factor = λ E t → Factor.functor t
      ; factor-β = λ E t → Factor.comparison t
      ; reflect = λ E h k Φ → coproduct-reflect h k (CoconeIso.rightIso Φ)
          (second k ∙ ((CoconeIso.leftIso Φ ▷ in₂) ∙ (second h) ⁻¹)) }
    isPushout : IsPushout square
    isPushout = cocone-extension→pushout square extensions
```
