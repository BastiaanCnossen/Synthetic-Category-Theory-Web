# The mapping-anima restriction of a localization

Taking cores of a restriction into the full inverting subcategory gives
the corresponding restriction on mapping animae. The comparison below
retains its map to the ambient mapping anima. In particular an equivalence
on the functor categories gives an equivalence on these mapping animae.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMapping
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.FunctorCoreRestriction 𝒯 M ℱ using (module Restrict)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

module OnMaps (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
  (l : MAP C T) (D : CAT)
  (r : FunctorLift {C = Inverting.Category.functors W D L} {D = Fun C D} {X = Fun T D}
    (Inverting.Category.functorInclusion W D L) (funPre {D = D} l)) where
  module Target = Inverting W D
  module Category = Target.Category L
  module Core = CoreComparison Target.objects Category.Full.presentation
    using (comparison; over-core; comparison-isEquiv)
  inclusion = Category.functorInclusion
  chosen : MAP (Fun T D) Category.functors
  chosen = FunctorLift.lift r
  q = CoreOfFun.comparison C D
  qT = CoreOfFun.comparison T D

  abstract
    maps : MAP (Map T D) Target.maps
    maps = Core.comparison ∘ (mapPost chosen ∘ qT)

    comparison : (Target.inclusion ∘ maps) =₁ mapPre l
    comparison = equiv-reflect (CoreOfFun.comparison-isEquiv C D) _ _
      (Restrict.comparison-natural l D ∙
        ((mapPost-cong (FunctorLift.comparison r) ▷ qT) ∙
          ((mapPost-comp chosen inclusion ▷ qT) ∙
            ((comp-assoc qT (mapPost chosen) (mapPost inclusion)) ⁻¹ ∙
              ((Core.over-core ▷ (mapPost chosen ∘ qT)) ∙
                ((comp-assoc (mapPost chosen ∘ qT) Core.comparison (q ∘ Target.inclusion)) ⁻¹ ∙
                  (comp-assoc maps Target.inclusion q) ⁻¹))))))

    isEquiv : IsEquiv chosen → IsEquiv maps
    isEquiv e = equiv-compose (mapPost chosen ∘ qT) Core.comparison
      (equiv-compose qT (mapPost chosen) (CoreOfFun.comparison-isEquiv T D) (mapPost-isEquiv chosen e))
      Core.comparison-isEquiv

  factorization : FunctorLift Target.inclusion (mapPre l)
  factorization = record { lift = maps ; comparison = comparison }

```
