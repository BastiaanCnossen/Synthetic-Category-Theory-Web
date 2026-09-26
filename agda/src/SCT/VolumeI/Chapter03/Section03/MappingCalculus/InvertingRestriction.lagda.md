# Restricting functors that invert a collection

This is `rmk:Functors_Inverting_W_Natural_In_W`. A functor preserving
the two collections induces restriction on their inverting mapping
animae. Compatibility with the core comparison then induces restriction
on the full functor subcategories. Both ambient squares are retained.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingPrecomposition 𝒯 M using (mappingAction-precompose)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection; PreservesMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphismInclusion)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.SpannedFunctoriality 𝒯 M ℱ P I E S
  using (PreservesObjects; module Induced)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.FunctorCoreRestriction 𝒯 M ℱ using () renaming (module Restrict to CoreRestriction)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

module Restrict {A B : CAT} (V : MorphismCollection A) (W : MorphismCollection B)
  (f : MAP A B) (preserves : PreservesMorphisms f V W) (D : CAT) where
  module Source = Inverting W D
  module Target = Inverting V D
  v = MorphismCollection.inclusion V
  w = MorphismCollection.inclusion W
  k = FunctorLift.lift preserves
  π = isomorphismInclusion D

  abstract
    action : (Target.restriction ∘ mapPre f) =₁ (mapPre k ∘ Source.restriction)
    action = comp-assoc (mappingAction [1] B D) (mapPre w) (mapPre k) ∙
      (((mapPre-comp k w) ⁻¹ ▷ mappingAction [1] B D) ∙
        ((mapPre-cong ((FunctorLift.comparison preserves) ⁻¹) ▷ mappingAction [1] B D) ∙
          ((mapPre-comp v (mapPost f) ▷ mappingAction [1] B D) ∙
            ((comp-assoc (mappingAction [1] B D) (mapPre (mapPost f)) (mapPre v)) ⁻¹ ∙
              ((mapPre v ◁ mappingAction-precompose f [1] D) ∙
                comp-assoc (mapPre f) (mappingAction [1] A D) (mapPre v))))))

  cone : Cone Target.restriction (mapPost π) Source.maps
  cone = record { left = mapPre f ∘ Source.inclusion ; right = mapPre k ∘ pullback₂
    ; match = comp-assoc pullback₂ (mapPre k) (mapPost π) ∙
        ((mapPre-mapPost k π ▷ pullback₂) ∙
          ((comp-assoc pullback₂ (mapPost π) (mapPre k)) ⁻¹ ∙
            ((mapPre k ◁ pullbackMatch) ∙
              (comp-assoc Source.inclusion Source.restriction (mapPre k) ∙
                ((action ▷ Source.inclusion) ∙ (comp-assoc Source.inclusion (mapPre f) Target.restriction) ⁻¹))))) }

  maps : MAP Source.maps Target.maps
  maps = pullbackLift cone

  maps-comparison : (Target.inclusion ∘ maps) =₁ (mapPre f ∘ Source.inclusion)
  maps-comparison = pullbackLift-β₁ cone

  abstract
    preserves-objects : PreservesObjects (funPre {D = D} f) Source.objects Target.objects
    preserves-objects = record { lift = maps
      ; comparison = comp-assoc Source.inclusion (CoreOfFun.comparison B D) (mapPost (funPre f)) ∙
          (((CoreRestriction.comparison-natural f D) ⁻¹ ▷ Source.inclusion) ∙
            ((comp-assoc Source.inclusion (mapPre f) (CoreOfFun.comparison A D)) ⁻¹ ∙
              ((CoreOfFun.comparison A D ◁ maps-comparison) ∙
                comp-assoc maps Target.inclusion (CoreOfFun.comparison A D)))) }

  module OnFunctors (L : SubcategoryAxiom) where
    factorization : FunctorLift (Target.Category.functorInclusion L)
      (funPre f ∘ Source.Category.functorInclusion L)
    factorization = Induced.factorization {V = Source.objects} {W = Target.objects}
      (Source.Category.Full.presentation L) (Target.Category.Full.presentation L)
      (funPre f) preserves-objects

    functor : MAP (Source.Category.functors L) (Target.Category.functors L)
    functor = FunctorLift.lift factorization

    comparison : (Target.Category.functorInclusion L ∘ functor) =₁
      (funPre f ∘ Source.Category.functorInclusion L)
    comparison = FunctorLift.comparison factorization
```
