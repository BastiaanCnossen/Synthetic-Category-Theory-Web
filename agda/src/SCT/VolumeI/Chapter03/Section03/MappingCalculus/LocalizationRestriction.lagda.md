# Restriction along an inverting functor

This is `con:Restriction_Along_An_Inverting_Functor`. Every functor from
the target inverts its isomorphisms. Inverting restriction therefore
factors the ordinary restriction functor through the selected full
subcategory, with its specified ambient comparison.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingRestriction 𝒯 M ℱ P I E S Q using (module Restrict)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphisms 𝒯 M ℱ P I E S Q R using (module Preservation)

module RestrictionAlong (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
  (l : MAP C T) (inverts : Inverts l W) (D : CAT) where
  module Source = Inverting.Category (isomorphisms T) D L
  module Target = Inverting.Category W D L
  module Restriction = Restrict.OnFunctors W (isomorphisms T) l inverts D L
  source-equivalence = Preservation.functors-isEquiv T D L
  inverse = IsEquiv.inverse source-equivalence

  abstract
    functor : MAP (Fun T D) Target.functors
    functor = Restriction.functor ∘ inverse
  
    comparison : (Target.functorInclusion ∘ functor) =₁ (funPre l)
    comparison = comp-unitʳ (funPre l) ∙
      ((funPre l ◁ (IsEquiv.retractionIso source-equivalence) ⁻¹) ∙
        (comp-assoc inverse Source.functorInclusion (funPre l) ∙
          ((Restriction.comparison ▷ inverse) ∙
            (comp-assoc inverse Restriction.functor Target.functorInclusion) ⁻¹)))

  factorization : FunctorLift {C = Target.functors} {D = Fun C D} {X = Fun T D}
    Target.functorInclusion (funPre {D = D} l)
  factorization = record { lift = functor ; comparison = comparison }
```
