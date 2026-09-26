# Factoring through a full subcategory

A functor whose entire family of objects lands in a full subcategory
factors through it. Name the functor and the object lift, apply the
defining pullback square, and decode its factorization. The comparison
with the original functor is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryFactorization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction-name)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P

module Factor {A C D : CAT} (i : MAP A C) (full : IsFullSubcategory i)
  (f : MAP D C) (objects : FunctorLift (mapPost {C = One} i) (mapPost {C = One} f)) where
  j = FunctorLift.lift objects
  module U = UniversalCone (fullSubcategorySquare i D)
    (IsFullSubcategory.mapping-square-isPullback full D)

  cone : Cone (restrictionToCores D C) (mapPost (mapPost i)) One
  cone = record
    { left = nameMap f ; right = nameMap j
    ; match = (mapPost-name (mapPost i) j) ⁻¹ ∙
        (nameMapIso (FunctorLift.comparison objects ⁻¹) ∙ mappingAction-name One f) }
  point = U.factor cone

  functor : MAP D A
  functor = decodeMap point

  comparison : (i ∘ functor) =₁ f
  comparison = unnamedIso
    (ConeIso.leftIso (U.factor-β cone) ∙
      ((mapPost i ◁ name-decode point) ∙ (mapPost-name i functor) ⁻¹))

  factorization : FunctorLift i f
  factorization = record { lift = functor ; comparison = comparison }

  unique : (g h : FunctorLift i f) → FunctorLift.lift g =₁ FunctorLift.lift h
  unique g h = embedding-reflect i (full-subcategory-isEmbedding i full) _ _
    (FunctorLift.comparison h ⁻¹ ∙ FunctorLift.comparison g)
```
