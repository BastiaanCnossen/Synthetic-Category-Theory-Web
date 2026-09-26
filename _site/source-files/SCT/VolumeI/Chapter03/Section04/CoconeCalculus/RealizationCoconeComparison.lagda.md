# The realized square retains the original cocone

Restrict the realized cocone along the localization maps. The specified
image of its commutativity identification gives a comparison with the
original cocone postcomposed by localization. Both leg comparisons are
the already chosen naturality identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.RealizationCoconeComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (Square)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section04.GeometricRealization 𝒯 M ℱ P I E S Q R using (module Realization)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.RealizationComparisons 𝒯 M ℱ P I E S Q R using (module RealizationAction)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSquareRestriction 𝒯 using (module Cube)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeBridgeReversal 𝒯 using (module Reversal)

module Diagram (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L)
  {A B C D : CAT} {u : MAP A B} {v : MAP A C} {r : MAP B D} {s : MAP C D}
  (square : Square u v r s) where
  module Geom = Realization L Z using (category; localization)
  module Action = RealizationAction L Z using (action; naturality; composite-naturality; module SquareImage)
  module Image = Action.SquareImage square
  module CubeProof = Cube u v (Action.action u) (Action.action v)
    (Geom.localization A) (Geom.localization B) (Geom.localization C) (Action.naturality u) (Action.naturality v)
    (squareCocone square) (squareCocone Image.value) (Geom.localization D) (Action.naturality r) (Action.naturality s)
  module Left = Reversal u (Action.action u) (Geom.localization A) (Geom.localization B) (Action.naturality u) (Action.action r)
  module Right = Reversal v (Action.action v) (Geom.localization A) (Geom.localization C) (Action.naturality v) (Action.action s)

  abstract
    left-normal : CubeProof.left =₂ Action.composite-naturality u r
    left-normal = isoComp-cong (idIso (comp-assoc u r (Geom.localization D)))
      (isoComp-cong (idIso (Action.naturality r ▷ u)) Left.comparison)
    right-normal : CubeProof.right =₂ Action.composite-naturality v s
    right-normal = isoComp-cong (idIso (comp-assoc v s (Geom.localization D)))
      (isoComp-cong (idIso (Action.naturality s ▷ v)) Right.comparison)

    matching : CubeProof.τ =₂ (CubeProof.right ⁻¹ ∙ (CubeProof.σ ∙ CubeProof.left))
    matching = isoComp-cong (＝-inv ◁ (right-normal ⁻¹))
      (isoComp-cong (idIso CubeProof.σ) (left-normal ⁻¹)) ∙ Image.matching-image

    comparison : CoconeIso (CubeProof.Restrict.value (squareCocone Image.value))
      (coconePost (Geom.localization D) (squareCocone square))
    comparison = CubeProof.Compatible.comparison matching
```
