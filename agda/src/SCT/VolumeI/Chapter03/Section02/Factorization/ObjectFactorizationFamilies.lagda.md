# Families of factorizations through a full subcategory

An anima-parametrized family of functors lifts if its induced family on
cores lands in the chosen objects. Restricting the mapping action at
each endpoint shows that all its arrows belong to the defining morphism
collection. The subcategory universal property then gives the lift.

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

module SCT.VolumeI.Chapter03.Section02.Factorization.ObjectFactorizationFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; module UniversalCone)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingRestriction 𝒯 M using (mappingAction-restrict)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation; presentationSquare)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.Factorization.ObjectCollectionClosure 𝒯 M ℱ P I E S using (module Closure)

curry-lift : {Γ T X Y : CAT} → isAn Γ → (f : MAP X Y) (h : MAP Γ (Map T Y)) →
  FunctorLift f (mapUncurry h) → FunctorLift (mapPost f) h
curry-lift Γ-an f h l = record { lift = mapCurry Γ-an (FunctorLift.lift l)
  ; comparison = mapReflect Γ-an _ _
      (FunctorLift.comparison l ∙
        ((f ◁ mapCurry-β Γ-an (FunctorLift.lift l)) ∙
          mapPost-uncurry f (mapCurry Γ-an (FunctorLift.lift l)))) }

module Factor {C : CAT} (V : ObjectCollection C)
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V))
  {Γ D : CAT} (Γ-an : isAn Γ)
  (h : MAP Γ (Map D C)) (objects : MAP Γ (Map (Core D) (ObjectCollection.collection V)))
  (over-core : (mappingAction One D C ∘ h) =₁ (mapPost (ObjectCollection.inclusion V) ∘ objects)) where
  j = ObjectCollection.inclusion V
  action = mappingAction [1] D C ∘ h

  endpoint : (x : Obj-abs [1]) →
    (mapPost (mapPre {D = C} x) ∘ action) =₁
      (mapPost j ∘ (mapPre (mapPre {D = D} x) ∘ objects))
  endpoint x = comp-assoc objects (mapPre (mapPre x)) (mapPost j) ∙
    ((mapPre-mapPost (mapPre x) j ▷ objects) ∙
      ((comp-assoc objects (mapPost j) (mapPre (mapPre x))) ⁻¹ ∙
        ((mapPre (mapPre x) ◁ over-core) ∙
          (comp-assoc h (mappingAction One D C) (mapPre (mapPre x)) ∙
            ((mappingAction-restrict x D C ▷ h) ∙
              (comp-assoc h (mappingAction [1] D C) (mapPost (mapPre x))) ⁻¹)))))

  raw-endpoint : (x : Obj-abs [1]) →
    (mapPre x ∘ mapUncurry action) =₁
      (j ∘ mapUncurry (mapPre (mapPre {D = D} x) ∘ objects))
  raw-endpoint x = mapPost-uncurry j (mapPre (mapPre x) ∘ objects) ∙
    (mapUncurryIso (endpoint x) ∙ (mapPost-uncurry (mapPre x) action) ⁻¹)

  raw-arrows = Closure.lift-endpoints V (mapUncurry action)
    (mapUncurry (mapPre (mapPre zero) ∘ objects))
    (mapUncurry (mapPre (mapPre one) ∘ objects)) (raw-endpoint zero) (raw-endpoint one)
  arrows = curry-lift Γ-an (SpannedMorphisms.morphisms-inclusion V) action raw-arrows
  module U = UniversalCone
    (presentationSquare (SpannedMorphisms.collectionOfMorphisms V)
      (SubcategoryPresentation.inclusion A) (SubcategoryPresentation.arrows A) D)
    (SubcategoryPresentation.universal A D)

  cone : Cone (mappingAction [1] D C) (mapPost (SpannedMorphisms.morphisms-inclusion V)) Γ
  cone = record { left = h ; right = FunctorLift.lift arrows
    ; match = (FunctorLift.comparison arrows) ⁻¹ }

  factorization : FunctorLift (mapPost (SubcategoryPresentation.inclusion A)) h
  factorization = record { lift = U.factor cone ; comparison = ConeIso.leftIso (U.factor-β cone) }
```
