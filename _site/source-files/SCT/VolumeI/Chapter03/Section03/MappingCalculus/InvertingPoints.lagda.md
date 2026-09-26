# Naming a functor that inverts the collection

The given factorization on arrows names a point of the inverting
mapping anima. Its projection is the original named functor.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingPoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction; mappingAction-name)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphismInclusion)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)

module Point {C D : CAT} (W : MorphismCollection C) (f : MAP C D) (inverts : Inverts f W) where
  w = MorphismCollection.inclusion W
  k = FunctorLift.lift inverts
  π = isomorphismInclusion D
  cone : Cone (Inverting.restriction W D) (mapPost π) One
  cone = record { left = nameMap f ; right = nameMap k
    ; match = (mapPost-name π k) ⁻¹ ∙
        (nameMapIso ((FunctorLift.comparison inverts) ⁻¹) ∙
          (mapPre-name w (mapPost f) ∙
            ((mapPre w ◁ mappingAction-name [1] f) ∙
              comp-assoc (nameMap f) (mappingAction [1] C D) (mapPre w)))) }

  point : Obj-abs (Inverting.maps W D)
  point = pullbackLift cone

  comparison : (Inverting.inclusion W D ∘ point) =₁ nameMap f
  comparison = pullbackLift-β₁ cone
```
