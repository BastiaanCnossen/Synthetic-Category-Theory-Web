# Restricting a whole relative comparison

A relative triangle can be restricted along a functor and then pasted
with a fixed matching identification. Perform this operation on the
entire cospan of relative identifications. The resulting map retains
the triangle witness, so full computation rules can be transported
before taking a lift into a pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyPairing as Pairing

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints-map)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (change-map-evaluate)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding as Relative
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as ConeAction
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanRestriction as ConeRestriction
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonAlgebra 𝒯 using (left-boundary)
open Param vocabulary terminal products productLaws composition vertical
  using (const-comp; const-cong; unitˡ)
open Param.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (whisker-mixed-general)
open Naturality vocabulary terminal products productLaws composition vertical whiskering
  using (pre-composition)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pre-constant; post-constant)

module Restriction {B C D S T : CAT} {f : MAP C T} {g : MAP D T}
  (p : MAP S T) (r : MAP B C) (q : MAP B S) (τ : (f ∘ r) =₁ (p ∘ q))
  (u v : FunctorOver f g) where
  h = FunctorLift.lift u
  k = FunctorLift.lift v
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  a₀ = comp-assoc r h g
  a₁ = comp-assoc r k g
  cone : FunctorOver f g → Cone g p B
  cone w = record { left = FunctorLift.lift w ∘ r ; right = q
    ; match = τ ∙ ((FunctorLift.comparison w ▷ r) ∙
        (comp-assoc r (FunctorLift.lift w) g) ⁻¹) }
  module Source = Relative.Encoding 𝒯 M ℱ P u v
  module Target = Encoding (cone u) (cone v)
  left : MAP Source.Left Target.Left
  left = preWhisker r
  right : MAP One Target.Right
  right = const (idIso q)
  base : MAP Source.Middle Target.Middle
  base = changeEndpoints-map a₀ τ ∘ preWhisker r

  opaque
    base-at : {A : CAT} (γ : MAP A Source.Middle) →
      (base ∘ γ) =₁ (const τ ∙ ((γ ▷ r) ∙ const (a₀ ⁻¹)))
    base-at γ = change-map-evaluate a₀ τ (γ ▷ r) ∙
      comp-assoc γ (preWhisker r) (changeEndpoints-map a₀ τ)

    mixed : (const a₁ ∙ (postWhisker g ▷ r)) =₁ ((g ◁ left) ∙ const a₀)
    mixed = isoComp-cong (postWhisker g ◁ comp-unitʳ (preWhisker r)) (idIso (const a₀)) ∙
      (whisker-mixed-general (id Source.Left) r g ∙
        isoComp-cong (idIso (const a₁))
          (preWhisker r ◁ (comp-unitʳ (postWhisker g)) ⁻¹))

    left-normalization : (Target.leftMap ∘ left) =₁
      (const (Cone.match (cone v)) ∙ (g ◁ left))
    left-normalization = isoComp-cong (const-pre (Cone.match (cone v)) left) (idIso _) ∙
      isoComp-pre (const (Cone.match (cone v))) (postWhisker g) left

    leftSquare : (Target.leftMap ∘ left) =₁ (base ∘ Source.leftMap)
    leftSquare = (base-at Source.leftMap) ⁻¹ ∙
      ((isoComp-cong (idIso (const τ))
        (isoComp-cong
          (isoComp-cong (pre-constant θv r) (idIso _) ∙
            pre-composition (const θv) (postWhisker g) r)
          (idIso (const (a₀ ⁻¹))))) ⁻¹ ∙
      ((left-boundary a₀ a₁ (θv ▷ r) τ (postWhisker g ▷ r) (g ◁ left) mixed) ⁻¹ ∙
        left-normalization))

    right-normalization : (Target.rightMap ∘ right) =₁ const (Cone.match (cone u))
    right-normalization = unitˡ (const (Cone.match (cone u))) ∙
      (isoComp-cong
        (const-cong (postWhisker-idIso p q) ∙ post-constant p (idIso q))
        (const-pre (Cone.match (cone u)) right) ∙
        isoComp-pre (postWhisker p) (const (Cone.match (cone u))) right)

    rightSquare : (Target.rightMap ∘ right) =₁ (base ∘ Source.rightMap)
    rightSquare = (base-at Source.rightMap) ⁻¹ ∙
      ((const-comp τ ((θu ▷ r) ∙ a₀ ⁻¹) ∙
        isoComp-cong (idIso (const τ))
          (const-comp (θu ▷ r) (a₀ ⁻¹) ∙
            isoComp-cong (pre-constant θu r) (idIso (const (a₀ ⁻¹))))) ⁻¹ ∙
        right-normalization)

  cospan : CospanMap Source.leftMap Source.rightMap Target.leftMap Target.rightMap
  cospan = record { left = left ; right = right ; base = base
    ; leftSquare = leftSquare ; rightSquare = rightSquare }
```

Transport a computation rule through this cospan before decoding. The
result compares the entire restricted cone identification, including
its matching witness one dimension higher.

```agda
  opaque
    map-computation : {A : CAT}
      (familyCone : Cone Source.leftMap Source.rightMap A)
      (α : Obj-abs A) (Φ : FunctorOverIso u v) →
      ConeIso (conePre α familyCone) (Source.encode Φ) →
      ConeIso (conePre α (CospanMap.mapCone cospan familyCone))
        (CospanMap.mapCone cospan (Source.encode Φ))
    map-computation familyCone α Φ image = coneIso-compose
      (ConeAction.Action.Identification.comparison 𝒯 P cospan image)
      (ConeRestriction.Restriction.comparison 𝒯 P cospan α familyCone)

    decoded-computation : {A : CAT}
      (familyCone : Cone Source.leftMap Source.rightMap A)
      (α : Obj-abs A) (Φ : FunctorOverIso u v) →
      ConeIso (conePre α familyCone) (Source.encode Φ) →
      ConeIso₂
        (Target.decode (conePre α (CospanMap.mapCone cospan familyCone)))
        (Target.decode (CospanMap.mapCone cospan (Source.encode Φ)))
    decoded-computation familyCone α Φ image = Target.decode-comparison
      (map-computation familyCone α Φ image)
```
