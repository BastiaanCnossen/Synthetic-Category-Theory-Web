# Comparing universal cocones

Extend each cocone through the other. Their two beta comparisons,
postcomposition associativity, and reflection identify both composites
with the identity. The resulting equivalence retains its computation
on the entire defining cocone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.PushoutUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconePostAssociativity 𝒯 M using (coconePost-assoc)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as PU
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)

module Identity {A B C D : CAT} {u : MAP A B} {v : MAP A C} (s : Cocone u v D) where
  p = Cocone.left s
  q = Cocone.right s
  τ = Cocone.match s
  input = comp-assoc u p (id D)
  output = comp-assoc v q (id D)
  σ = id D ◁ τ
  abstract
    output-normal : ((comp-unitˡ q ▷ v) ∙ output ⁻¹) =₂ comp-unitˡ (q ∘ v)
    output-normal = cancel-right output (comp-unitˡ (q ∘ v)) ∙
      isoComp-cong ((left-unitor-comp v q) ⁻¹) (idIso (output ⁻¹))
    matching : (τ ∙ (comp-unitˡ p ▷ u)) =₂
      ((comp-unitˡ q ▷ v) ∙ Cocone.match (coconePost (id D) s))
    matching = (isoComp-cong (idIso τ) (left-unitor-comp u p) ∙
      (isoComp-assoc-at τ (comp-unitˡ (p ∘ u)) input ∙
        (isoComp-cong (postWhisker-id-at τ) (idIso input) ∙
          ((isoComp-assoc-at (comp-unitˡ (q ∘ v)) σ input) ⁻¹ ∙
            (isoComp-cong output-normal (idIso (σ ∙ input)) ∙
              (isoComp-assoc-at (comp-unitˡ q ▷ v) (output ⁻¹) (σ ∙ input)) ⁻¹))))) ⁻¹
    comparison : CoconeIso (coconePost (id D) s) s
    comparison = record { leftIso = comp-unitˡ p ; rightIso = comp-unitˡ q ; compatible = matching }

module Uniqueness {A B C D E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) (t : Cocone u v E)
  (source : CoconeExtensionProperty s) (target : CoconeExtensionProperty t) where
  module Source = CoconeExtensionProperty source
  module Target = CoconeExtensionProperty target
  forward = Source.factor E t
  backward = Target.factor D s
  computation = Source.factor-β E t
  abstract
    section : (backward ∘ forward) =₁ id D
    section = Source.reflect D (backward ∘ forward) (id D)
      (coconeIso-compose (coconeIso-inverse (Identity.comparison s))
        (coconeIso-compose (Target.factor-β D s)
          (coconeIso-compose (coconeIso-post backward computation)
            (coconePost-assoc s forward backward))))
    retraction : (forward ∘ backward) =₁ id E
    retraction = Target.reflect E (forward ∘ backward) (id E)
      (coconeIso-compose (coconeIso-inverse (Identity.comparison t))
        (coconeIso-compose computation
          (coconeIso-compose (coconeIso-post forward (Target.factor-β D s))
            (coconePost-assoc t backward forward))))
    isEquiv : IsEquiv forward
    isEquiv = record { inverse = backward ; sectionIso = section ⁻¹ ; retractionIso = retraction ⁻¹ }
```
