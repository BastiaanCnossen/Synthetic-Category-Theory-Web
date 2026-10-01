# Postcomposition laws for relative functor categories

Compare the universal families to prove that postcomposition respects
identifications, identity, and composition. The resulting equalities
are equalities of the functors themselves, not just their values on
absolute points.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)

abstract
  postcompose-identification : {B C D S : CAT} (f : MAP B S) {g : MAP C S} {h : MAP D S}
    {u v : FunctorOver g h} → FunctorOverIso u v →
    Postcompose.functor f u =₁ Postcompose.functor f v
  postcompose-identification f {g} {h} {u} {v} Φ = reflect-family f h _ _
    (compose-iso-over (inverse-iso-over (Postcompose.family-comparison f v))
      (compose-iso-over (prewhisker-over (universal f g) Φ) (Postcompose.family-comparison f u)))

  postcompose-identity : {B C S : CAT} (f : MAP B S) (g : MAP C S) →
    Postcompose.functor f (identity-over g) =₁ id (FunOver f g)
  postcompose-identity f g = reflect-family f g _ _
    (compose-iso-over (inverse-iso-over (family-identity f g))
      (compose-iso-over (left-unit-over (universal f g))
        (Postcompose.family-comparison f (identity-over g))))

  postcompose-composite : {A B C D S : CAT} (f : MAP A S) {g : MAP B S} {h : MAP C S} {k : MAP D S}
    (u : FunctorOver g h) (v : FunctorOver h k) →
    (Postcompose.functor f v ∘ Postcompose.functor f u) =₁ Postcompose.functor f (compose-over v u)
  postcompose-composite f {g} u v = reflect-family f _ _ _
    (compose-iso-over (inverse-iso-over (Postcompose.family-comparison f (compose-over v u)))
      (compose-iso-over (inverse-iso-over (associator-over (universal f g) u v))
        (compose-iso-over (postwhisker-over v (Postcompose.family-comparison f u))
          (postcompose-family f v (Postcompose.functor f u)))))

  postcompose-maps-composite : {A B C D S : CAT} (f : MAP A S) {g : MAP B S} {h : MAP C S} {k : MAP D S}
    (u : FunctorOver g h) (v : FunctorOver h k) →
    (Postcompose.maps f v ∘ Postcompose.maps f u) =₁ Postcompose.maps f (compose-over v u)
  postcompose-maps-composite f u v = (Postcompose.maps-as-core f (compose-over v u)) ⁻¹ ∙
    (mapPost-cong (postcompose-composite f u v) ∙
      (mapPost-comp (Postcompose.functor f u) (Postcompose.functor f v) ∙
        ((mapPost (Postcompose.functor f v) ◁ Postcompose.maps-as-core f u) ∙
          (Postcompose.maps-as-core f v ▷ Postcompose.maps f u))))
```
