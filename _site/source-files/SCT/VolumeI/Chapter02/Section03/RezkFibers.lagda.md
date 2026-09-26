# Identifications and invertible arrows with specified endpoints

For `cor:Invertible_Morphisms_Induce_Isomorphisms`, representability
identifies the identification anima with the fiber of the diagonal.
The Rezk equivalence replaces the diagonal by the endpoint functor of
`Iso C`. The comparison below is an equivalence of the actual pullbacks,
including their specified matchings.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.Representability as Representability
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section03.RezkFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (Rep : Representability.Representability 𝒯 P) where

open Rezk 𝒯 M ℱ P I E public
open RezkAxiom R
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P
  using (module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section06.RepresentabilityDiagonal 𝒯 P
  using (module Diagonal)

isoEndpoints : {C : CAT} → MAP (Iso C) (C × C)
isoEndpoints = pair ev₀ ev₁ ∘ isoArrow

identityIso-endpoints : {C : CAT} →
  (isoEndpoints ∘ identityIso) =₁ (pair (id C) (id C))
identityIso-endpoints = pair-cong identity-source identity-target ∙
  (pair-pre ev₀ ev₁ identityArrow ∙
    ((pair ev₀ ev₁ ◁ identityIso-arrow) ∙
      comp-assoc identityIso isoArrow (pair ev₀ ev₁)))

IsoBetween : {C : CAT} → Obj-abs C → Obj-abs C → CAT
IsoBetween x y = Pullback (pair x y) isoEndpoints

module IdentificationFiber {C : CAT} (x y : Obj-abs C) where
  private
    module D = Diagonal Rep x y

    change : CospanMap (pair x y) (pair (id C) (id C))
      (pair x y) isoEndpoints
    change = record
      { left = id One ; right = identityIso ; base = id (C × C)
      ; leftSquare = (comp-unitˡ (pair x y)) ⁻¹ ∙ comp-unitʳ (pair x y)
      ; rightSquare = (comp-unitˡ (pair (id C) (id C))) ⁻¹ ∙ identityIso-endpoints }

    module Change = CospanMap change
    module CospanProof = CospanEquivalence change
      (id-isEquiv One) (rezk-isEquiv C) (id-isEquiv (C × C))
      using (pullbackMap-isEquiv)

  identification-to-iso : MAP (x ＝ y) (IsoBetween x y)
  identification-to-iso = Change.pullbackMap ∘ pullbackLift D.reversed-square

  identification-to-iso-isEquiv : IsEquiv identification-to-iso
  identification-to-iso-isEquiv = equiv-compose
    (pullbackLift D.reversed-square) Change.pullbackMap
    D.reversed-isPullback CospanProof.pullbackMap-isEquiv
```
