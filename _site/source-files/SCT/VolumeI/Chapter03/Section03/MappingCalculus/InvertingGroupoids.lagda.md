# Every functor into a groupoid inverts the collection

For `lem:Functor_Into_Groupoid_Inverts_Everything`, the core of the
isomorphism inclusion is an equivalence. Its base change therefore
selects the whole mapping anima, and the corresponding full subcategory
is the whole functor category.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open Rezk 𝒯 M ℱ P I E using (identityIso; identityIso-arrow; isoArrow)
open Rezk.RezkAxiom R
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphismInclusion)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization 𝒯 M ℱ P I E S
  using (full-subcategory-on-equivalent-objects)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

isomorphisms-of-groupoid : (D : CAT) → IsGroupoid D → IsEquiv (isomorphismInclusion D)
isomorphisms-of-groupoid D groupoid = equiv-compose (mapPost isoArrow) (CoreOfFun.uncurrying [1] D)
  (mapPost-isEquiv isoArrow (equiv-cancel-right identityIso isoArrow (rezk-isEquiv D)
    (equiv-transport (identityIso-arrow ⁻¹) groupoid)))
  (CoreOfFun.uncurrying-isEquiv [1] D)

inverting-maps-into-groupoid : {C : CAT} (W : MorphismCollection C) (D : CAT) →
  IsGroupoid D → IsEquiv (Inverting.inclusion W D)
inverting-maps-into-groupoid W D groupoid = pullback-equivalence
  (Inverting.restriction W D) (mapPost (isomorphismInclusion D))
  (mapPost-isEquiv (isomorphismInclusion D) (isomorphisms-of-groupoid D groupoid))

inverting-functors-into-groupoid : (L : SubcategoryAxiom) {C : CAT}
  (W : MorphismCollection C) (D : CAT) → IsGroupoid D →
  IsEquiv (Inverting.Category.functorInclusion W D L)
inverting-functors-into-groupoid L {C = C} W D groupoid =
  full-subcategory-on-equivalent-objects (Inverting.objects W D)
    (Inverting.Category.Full.presentation W D L)
    (equiv-compose (Inverting.inclusion W D) (CoreOfFun.comparison C D)
      (inverting-maps-into-groupoid W D groupoid) (CoreOfFun.comparison-isEquiv C D))
```
