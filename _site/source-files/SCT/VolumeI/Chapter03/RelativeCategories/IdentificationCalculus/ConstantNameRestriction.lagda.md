# Restricting the constant-name comparison

The chosen normalization of a constant named family is compatible with
successive parameter changes. The proof uses the specified second
projection of product substitution and iterated uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.SubstitutionCoherence 𝒯 M ℱ using (funUncurry-restrict-iterated)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over; compositor-over)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)

module Restriction {X Y C S : CAT} (f : MAP C S) (u : MAP X One) (r : MAP Y X) where
  F : MAP One (Fun C S)
  F = nameFun f
  A : MAP (One × C) S
  A = funUncurry F
  q : MAP (One × C) S
  q = f ∘ pr₂
  U : MAP (X × C) (One × C)
  U = productMap u (id C)
  R : MAP (Y × C) (X × C)
  R = productMap r (id C)
  Q : MAP (Y × C) (One × C)
  Q = productMap (u ∘ r) (id C)
  κ : (U ∘ R) =₁ Q
  κ = slice-comparison {C = C} u r
  β : A =₁ q
  β = funCurry-β q
  δu : (q ∘ U) =₁ (f ∘ pr₂)
  δu = parameter-over u f
  δr : ((f ∘ pr₂) ∘ R) =₁ (f ∘ pr₂)
  δr = parameter-over r f
  δq : (q ∘ Q) =₁ (f ∘ pr₂)
  δq = parameter-over (u ∘ r) f
  βu : (A ∘ U) =₁ (q ∘ U)
  βu = β ▷ U
  βq : (A ∘ Q) =₁ (q ∘ Q)
  βq = β ▷ Q
  Au : funUncurry (F ∘ u) =₁ (A ∘ U)
  Au = funUncurry-restrict F u
  Aq : funUncurry (F ∘ (u ∘ r)) =₁ (A ∘ Q)
  Aq = funUncurry-restrict F (u ∘ r)
  Ar : funUncurry ((F ∘ u) ∘ r) =₁ (funUncurry (F ∘ u) ∘ R)
  Ar = funUncurry-restrict (F ∘ u) r
  assocA : ((A ∘ U) ∘ R) =₁ (A ∘ (U ∘ R))
  assocA = comp-assoc R U A
  assocq : ((q ∘ U) ∘ R) =₁ (q ∘ (U ∘ R))
  assocq = comp-assoc R U q
  Nu : (A ∘ U) =₁ (f ∘ pr₂)
  Nu = δu ∙ βu
  Nq : (A ∘ Q) =₁ (f ∘ pr₂)
  Nq = δq ∙ βq
  Ku : funUncurry (F ∘ u) =₁ (f ∘ pr₂)
  Ku = Nu ∙ Au
  Kq : funUncurry (F ∘ (u ∘ r)) =₁ (f ∘ pr₂)
  Kq = Nq ∙ Aq

  projection-step : (δq ∙ ((q ◁ κ) ∙ assocq)) =₂ (δr ∙ (δu ▷ R))
  projection-step = isoComp-cong (idIso δr) (isoComp-unitʳ-at (δu ▷ R) ∙
      (isoComp-cong (idIso (δu ▷ R)) (isoComp-inverseˡ-at assocq) ∙
        isoComp-assoc-at (δu ▷ R) (assocq ⁻¹) assocq)) ∙
    (isoComp-assoc-at δr ((δu ▷ R) ∙ assocq ⁻¹) assocq ∙
      (isoComp-cong (compositor-over r u f) (idIso assocq) ∙
        (isoComp-assoc-at δq (q ◁ κ) assocq) ⁻¹))

  evaluation-step : (Nq ∙ ((A ◁ κ) ∙ assocA)) =₂ (δr ∙ (Nu ▷ R))
  evaluation-step = isoComp-cong (idIso δr)
      ((preWhisker-isoComp-at δu βu R) ⁻¹) ∙
    (isoComp-assoc-at δr (δu ▷ R) (βu ▷ R) ∙
      (isoComp-cong projection-step (idIso (βu ▷ R)) ∙
        ((isoComp-assoc-at δq ((q ◁ κ) ∙ assocq) (βu ▷ R)) ⁻¹ ∙
          (isoComp-cong (idIso δq)
            ((isoComp-assoc-at (q ◁ κ) assocq (βu ▷ R)) ⁻¹ ∙
              (isoComp-cong (idIso (q ◁ κ)) ((preWhisker-comp-at β U R) ⁻¹) ∙
                (isoComp-assoc-at (q ◁ κ) (β ▷ (U ∘ R)) assocA ∙
                  (isoComp-cong (interchange-at β κ) (idIso assocA) ∙
                    (isoComp-assoc-at βq (A ◁ κ) assocA) ⁻¹)))) ∙
            isoComp-assoc-at δq βq ((A ◁ κ) ∙ assocA)))))

  normalize : {Z : CAT} (s : MAP Z One) →
    ((parameter-over s f ∙ (β ▷ productMap s (id C))) ∙ funUncurry-restrict F s) =₂
      uncurry-constant-name f s
  normalize s = isoComp-assoc-at (f ◁ parameter-base s C)
      (comp-assoc (productMap s (id C)) pr₂ f)
      ((β ▷ productMap s (id C)) ∙ funUncurry-restrict F s) ∙
    isoComp-assoc-at (parameter-over s f) (β ▷ productMap s (id C)) (funUncurry-restrict F s)

  grouped-restriction : (Kq ∙ funUncurryIso (comp-assoc r u F)) =₂
    (δr ∙ ((Ku ▷ R) ∙ Ar))
  grouped-restriction = isoComp-cong (idIso δr)
      (isoComp-cong ((preWhisker-isoComp-at Nu Au R) ⁻¹) (idIso Ar)) ∙
    (isoComp-cong (idIso δr) ((isoComp-assoc-at (Nu ▷ R) (Au ▷ R) Ar) ⁻¹) ∙
      (isoComp-assoc-at δr (Nu ▷ R) ((Au ▷ R) ∙ Ar) ∙
        (isoComp-cong evaluation-step (idIso ((Au ▷ R) ∙ Ar)) ∙
          ((isoComp-assoc-at Nq ((A ◁ κ) ∙ assocA) ((Au ▷ R) ∙ Ar)) ⁻¹ ∙
            (isoComp-cong (idIso Nq)
              ((isoComp-assoc-at (A ◁ κ) assocA ((Au ▷ R) ∙ Ar)) ⁻¹ ∙
                funUncurry-restrict-iterated F u r) ∙
              isoComp-assoc-at Nq Aq (funUncurryIso (comp-assoc r u F)))))))

  comparison :
    (uncurry-constant-name f (u ∘ r) ∙ funUncurryIso (comp-assoc r u F)) =₂
    (δr ∙ ((uncurry-constant-name f u ▷ R) ∙ Ar))
  comparison = isoComp-cong (idIso δr)
      (isoComp-cong (preWhisker R ◁ normalize u) (idIso Ar)) ∙
    (grouped-restriction ∙ isoComp-cong ((normalize (u ∘ r)) ⁻¹)
      (idIso (funUncurryIso (comp-assoc r u F))))
```
