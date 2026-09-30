# Isomorphisms in a functor category

The equivalence used in `prop:Objectwise_Criterion_Natural_Isomorphisms`
is compatible with the two functors to the category of arrow diagrams.
Rezk reduces the comparison to interchange of constant diagrams.
```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.IsomorphismDiagrams
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
  using (Ar; NatTrans; identityArrow; Fun; nameFun; decodeFun; name-decodeFun; funPost)
open Rezk 𝒯 M ℱ P I E using (Iso; IsoLift; identityIso; isoArrow; identityIso-arrow)
open Rezk.RezkAxiom R
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryFactorization 𝒯 M P using (module Factor)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ
  using (module Interchange; nameFun-cong; post-nameFun; decodeFun-cong; decodeFun-post)

open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ
  using (funPost-isEquiv; funPost-comp; funPost-cong)

module IsomorphismDiagrams (C D : CAT) where
  module Swap = Interchange [1] C D using (exchange; exchange-constant)
  q = IsEquiv.inverse (rezk-isEquiv (Fun C D))

  functor : MAP (Iso (Fun C D)) (Fun C (Iso D))
  functor = funPost identityIso ∘ q

  abstract
    isEquiv : IsEquiv functor
    isEquiv = equiv-compose q (funPost identityIso)
      (equiv-inverse (rezk-isEquiv (Fun C D)))
      (funPost-isEquiv identityIso (rezk-isEquiv D))

    constant-arrow : (identityArrow ∘ q) =₁ isoArrow
    constant-arrow = comp-unitʳ isoArrow ∙
      ((isoArrow ◁ (IsEquiv.retractionIso (rezk-isEquiv (Fun C D))) ⁻¹) ∙
        (comp-assoc q identityIso isoArrow ∙ (identityIso-arrow ⁻¹ ▷ q)))

    arrow-comparison : (funPost (isoArrow {D}) ∘ functor) =₁
      (Swap.exchange ∘ isoArrow {Fun C D})
    arrow-comparison = (Swap.exchange ◁ constant-arrow) ∙
      (comp-assoc q identityArrow Swap.exchange ∙
        ((Swap.exchange-constant ⁻¹ ▷ q) ∙
          ((funPost-cong identityIso-arrow ▷ q) ∙
            ((funPost-comp identityIso isoArrow ▷ q) ∙
              (comp-assoc q (funPost identityIso) (funPost isoArrow)) ⁻¹))))
```