# Currying from the mapping-anima universal property

Fix any category with evaluation satisfying `def:Functor_Category`.
Specialization of the inverse gives currying. The beta comparison of the
evaluation-induced functor converts its lifting rule into the familiar
evaluation formula. The same comparison gives reflection of natural
isomorphisms. These arguments require no anima hypothesis on the domain.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section06.Representation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Specialization 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Evaluation 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.FunctorCategories 𝒯 M

module Representing {F C D : CAT} (e : MAP (F × C) D) (universal : IsFunctorCategory e) where
  open Evaluation e public

  abstract
    curry : {T : CAT} → MAP (T × C) D → MAP T F
    curry {T} f = SpecializationLift.functor (specializeMap-lift (At.forward T) (universal T) f)

    curry-β : {T : CAT} (f : MAP (T × C) D) → =₁ (uncurry (curry f)) f
    curry-β {T} f = SpecializationLift.comparison (specializeMap-lift (At.forward T) (universal T) f) ∙
      invIso (At.specialize-β T (curry f))

  reflect : {T : CAT} (f g : MAP T F) → =₁ (uncurry f) (uncurry g) → =₁ f g
  reflect {T} f g α = specializeMap-reflect (At.forward T) (universal T) f g
    (invIso (At.specialize-β T g) ∙ (α ∙ At.specialize-β T f))

  curry-η : {T : CAT} (f : MAP T F) → =₁ (curry (uncurry f)) f
  curry-η f = reflect _ f (curry-β (uncurry f))

  curry-cong : {T : CAT} {f g : MAP (T × C) D} → =₁ f g → =₁ (curry f) (curry g)
  curry-cong {f = f} {g} α = reflect _ _ (invIso (curry-β g) ∙ (α ∙ curry-β f))

  curry-pre : {S T : CAT} (f : MAP (T × C) D) (r : MAP S T) →
    =₁ (curry (f ∘ productMap r (id C))) (curry f ∘ r)
  curry-pre f r = reflect _ _
    (invIso (uncurry-pre (curry f) r) ∙
      (invIso (curry-β f ▷ productMap r (id C)) ∙ curry-β (f ∘ productMap r (id C))))
```
