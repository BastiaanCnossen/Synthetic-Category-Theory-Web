# The pasting lemma for pushout squares

For `lem:Pasting_Lemma_Pushouts`, assume the left square is a pushout.
The right square is then a pushout if and only if the specified outer
rectangle is a pushout.

We prove extension and comparison of cocones at every target. Flattening
passes between the right and outer spans, and the left pushout supplies
the inverse passage. The recognition theorem then gives the mapping-anima
universal properties. All comparisons include their matching data.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.PushoutExtensions as Extensions
import SCT.VolumeI.Chapter01.Section08.UniversalCoconePasting as Universal
import SCT.VolumeI.Chapter01.Section08.CoconePastingPostcomposition as Postcomposition

module SCT.VolumeI.Chapter01.Section08.PushoutPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePasting 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeUniversality 𝒯
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P

module Pasting {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂)
  (left-isPushout : IsPushout left) where

  outer : Square (g₂ ∘ g₁) f₁ f₃ (h₂ ∘ h₁)
  outer = PastedSquare.outer left right
  module Paste = PasteCocones g₁ g₂ left

  postcomparison : {E : CAT} (F : MAP B₃ E) →
    CoconeIso (Paste.flatten (coconePost F (squareCocone right))) (coconePost F (squareCocone outer))
  postcomparison = Postcomposition.PastedPostcomposition.comparison 𝒯 M left right

  module PastePushouts (right-isPushout : IsPushout right) where
    module At (E : CAT) where
      module Left = Universal.UniversalPasting 𝒯 M P g₁ g₂ left left-isPushout E
      module Right = Extensions.Extensions 𝒯 M P right right-isPushout E

      module Lift (t : Cocone (g₂ ∘ g₁) f₁ E) where
        module Intermediate = Left.LiftOuter t
        module Extension = Right.Lift Intermediate.value
        value : MAP B₃ E
        value = Extension.value
        comparison : CoconeIso (coconePost value (squareCocone outer)) t
        comparison = coconeIso-compose Intermediate.comparison
          (coconeIso-compose (Paste.flatten-iso Extension.comparison)
            (coconeIso-inverse (postcomparison value)))

      reflect : (F G : MAP B₃ E) →
        CoconeIso (coconePost F (squareCocone outer)) (coconePost G (squareCocone outer)) → =₁ F G
      reflect F G Φ = Right.Compare.comparison F G
        (Left.ReflectFlattened.comparison
          (coconeIso-compose (coconeIso-inverse (postcomparison G))
            (coconeIso-compose Φ (postcomparison F))))

    extensions : CoconeExtensionProperty (squareCocone outer)
    extensions = record { factor = At.Lift.value ; factor-β = At.Lift.comparison ; reflect = At.reflect }

    isPushout : IsPushout outer
    isPushout = cocone-extension→pushout outer extensions

  module CancelPushout (outer-isPushout : IsPushout outer) where
    module At (E : CAT) where
      module Left = Universal.UniversalPasting 𝒯 M P g₁ g₂ left left-isPushout E
      module Outer = Extensions.Extensions 𝒯 M P outer outer-isPushout E

      module Lift (t : Cocone g₂ f₂ E) where
        module Extension = Outer.Lift (Paste.flatten t)
        value : MAP B₃ E
        value = Extension.value
        comparison : CoconeIso (coconePost value (squareCocone right)) t
        comparison = Left.ReflectFlattened.comparison
          (coconeIso-compose Extension.comparison (postcomparison value))

      reflect : (F G : MAP B₃ E) →
        CoconeIso (coconePost F (squareCocone right)) (coconePost G (squareCocone right)) → =₁ F G
      reflect F G Φ = Outer.Compare.comparison F G
        (coconeIso-compose (postcomparison G)
          (coconeIso-compose (Paste.flatten-iso Φ) (coconeIso-inverse (postcomparison F))))

    extensions : CoconeExtensionProperty (squareCocone right)
    extensions = record { factor = At.Lift.value ; factor-β = At.Lift.comparison ; reflect = At.reflect }

    isPushout : IsPushout right
    isPushout = cocone-extension→pushout right extensions

  paste-isPushout : IsPushout right → IsPushout outer
  paste-isPushout = PastePushouts.isPushout

  cancel-isPushout : IsPushout outer → IsPushout right
  cancel-isPushout = CancelPushout.isPushout
```
