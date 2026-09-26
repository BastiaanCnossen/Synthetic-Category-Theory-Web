# Detecting groupoids from their mapping anima of arrows

These are `(3) ⇔ (4)` and `(3) ⇒ (5)` of
`prop:Equivalent_Conditions_Geometric_Realization`. Rezk transports
fullness between the identity-arrow functor and the inclusion of
isomorphisms. A full subcategory is an equivalence if its map on cores
is an equivalence; the core comparison identifies that map with
`constantMap`.

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

module SCT.VolumeI.Chapter03.Section04.GroupoidCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open Rezk 𝒯 M ℱ P I E using (Iso; identityIso; isoArrow; identityIso-arrow)
open Rezk.RezkAxiom R
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (constantMap; core-constant)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P
  using (IsFullSubcategory; full-subcategory-core-detects-equivalence)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences 𝒯 M P
  using (full-subcategory-precompose-equivalence)

constant-full-from-isomorphism-full : (C : CAT) →
  IsFullSubcategory (isoArrow {C}) → IsFullSubcategory (identityArrow {C})
constant-full-from-isomorphism-full C = full-subcategory-precompose-equivalence
  identityArrow isoArrow identityIso (rezk-isEquiv C) identityIso-arrow

isomorphism-full-from-constant-full : (C : CAT) →
  IsFullSubcategory (identityArrow {C}) → IsFullSubcategory (isoArrow {C})
isomorphism-full-from-constant-full C = full-subcategory-precompose-equivalence
  isoArrow identityArrow inverse (equiv-inverse (rezk-isEquiv C)) comparison
  where
  inverse = IsEquiv.inverse (rezk-isEquiv C)
  comparison : (identityArrow ∘ inverse) =₁ isoArrow
  comparison = comp-unitʳ isoArrow ∙
    ((isoArrow ◁ (IsEquiv.retractionIso (rezk-isEquiv C)) ⁻¹) ∙
      (comp-assoc inverse identityIso isoArrow ∙ (identityIso-arrow ⁻¹ ▷ inverse)))

morphismwise-groupoid-criterion : (C : CAT) →
  IsFullSubcategory (identityArrow {C}) → IsEquiv (constantMap C) → IsGroupoid C
morphismwise-groupoid-criterion C full e = full-subcategory-core-detects-equivalence identityArrow full
  (equiv-cancel-left (mapPost identityArrow) (CoreOfFun.uncurrying [1] C)
    (CoreOfFun.uncurrying-isEquiv [1] C) (equiv-transport (core-constant C ⁻¹) e))
```
