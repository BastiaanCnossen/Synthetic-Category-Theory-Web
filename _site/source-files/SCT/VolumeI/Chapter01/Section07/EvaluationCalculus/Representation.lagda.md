# Currying from the mapping-anima universal property

Fix any category with evaluation satisfying `def:Functor_Category`.
Specialization of the inverse gives currying. The beta comparison of the
evaluation-induced functor converts its lifting rule into the familiar
evaluation formula. The same comparison gives reflection of natural
isomorphisms. These arguments require no anima hypothesis on the domain.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.Representation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Specialization 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Evaluation 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories 𝒯 M

module Representing {F C D : CAT} (e : MAP (F × C) D) (universal : IsFunctorCategory e) where
  open Evaluation e public

  abstract
    curry : {T : CAT} → MAP (T × C) D → MAP T F
    curry {T} f = SpecializationLift.functor (specializeMap-lift (At.forward T) (universal T) f)

    curry-β : {T : CAT} (f : MAP (T × C) D) → (uncurry (curry f)) =₁ f
    curry-β {T} f = SpecializationLift.comparison (specializeMap-lift (At.forward T) (universal T) f) ∙
      (At.specialize-β T (curry f)) ⁻¹

  reflect : {T : CAT} (f g : MAP T F) → (uncurry f) =₁ (uncurry g) → f =₁ g
  reflect {T} f g α = specializeMap-reflect (At.forward T) (universal T) f g
    ((At.specialize-β T g) ⁻¹ ∙ (α ∙ At.specialize-β T f))

  curry-η : {T : CAT} (f : MAP T F) → (curry (uncurry f)) =₁ f
  curry-η f = reflect _ f (curry-β (uncurry f))

  curry-cong : {T : CAT} {f g : MAP (T × C) D} → f =₁ g → (curry f) =₁ (curry g)
  curry-cong {f = f} {g} α = reflect _ _ ((curry-β g) ⁻¹ ∙ (α ∙ curry-β f))

  curry-restrict : {S T : CAT} (f : MAP (T × C) D) (r : MAP S T) →
    (curry (f ∘ productMap r (id C))) =₁ (curry f ∘ r)
  curry-restrict f r = reflect _ _
    ((uncurry-restrict (curry f) r) ⁻¹ ∙
      ((curry-β f ▷ productMap r (id C)) ⁻¹ ∙ curry-β (f ∘ productMap r (id C))))
```
