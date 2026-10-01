# Cartesian and cocartesian morphisms

A morphism is cocartesian when every square formed by precomposition and
its image under the given functor is a pullback. Postcomposition gives
the dual definition of cartesian morphisms. These definitions apply to
any functor; no fibration hypothesis or functoriality of universals is used.
They represent the absolute statement `def:cocartesian-morphism`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section05.CocartesianMorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomCompositionNaturality as Naturality

module Along {C D : CAT} (F : MAP C D) {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Original = At {C = C} {x = x} {y = y} e using (precompose; postcompose)
    module Image = Naturality.Image 𝒯 M ℱ P I E S {C = C} {D = D} F {x = x} {y = y} e using (point; precompose; postcompose)
    module Mapped = At {C = D} {x = F ∘ x} {y = F ∘ y} Image.point using (precompose; postcompose)

  cocartesian-square : (z : Obj-abs C) →
    Cone (hom-post F x z) (Mapped.precompose (F ∘ z)) (Hom C y z)
  cocartesian-square z = record { left = Original.precompose z
    ; right = hom-post F y z ; match = Image.precompose z }

  cartesian-square : (z : Obj-abs C) →
    Cone (hom-post F z y) (Mapped.postcompose (F ∘ z)) (Hom C z x)
  cartesian-square z = record { left = Original.postcompose z
    ; right = hom-post F z x ; match = Image.postcompose z }

  IsCocartesian : Set m
  IsCocartesian = (z : Obj-abs C) → IsPullback (cocartesian-square z)

  IsCartesian : Set m
  IsCartesian = (z : Obj-abs C) → IsPullback (cartesian-square z)
```
