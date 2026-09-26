# Lifting an inverting functor using the mapping universal property

Name the functor as a point of the inverting mapping anima, lift that
point through the given equivalence, and decode it. The named
comparisons give the required identification after restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.MappingLocalizationLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingPoints 𝒯 M ℱ P I E S Q using (module Point)

module Lift {C T D : CAT} (W : MorphismCollection C) (l : MAP C T)
  (restriction : FunctorLift (Inverting.inclusion W D) (mapPre l))
  (universal : IsEquiv (FunctorLift.lift restriction))
  (f : MAP C D) (inverts : Inverts f W) where
  chosen = equiv-lift universal (Point.point W f inverts)
  point = FunctorLift.lift chosen
  q = FunctorLift.lift restriction
  inclusion = Inverting.inclusion W D

  factor : MAP T D
  factor = decodeMap point

  comparison : (factor ∘ l) =₁ f
  comparison = unnamedIso
    (Point.comparison W f inverts ∙
      ((inclusion ◁ FunctorLift.comparison chosen) ∙
        (comp-assoc point q inclusion ∙
          (((FunctorLift.comparison restriction) ⁻¹ ▷ point) ∙
            ((mapPre l ◁ name-decode point) ∙ (mapPre-name l factor) ⁻¹)))))
```
