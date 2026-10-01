# Ordinary pullbacks and invertible arrows

The first square in the unlabelled remark after `cons:Directed_Pullback`
is a pullback: replace the diagonal by the endpoint functor on `Iso C`
using the Rezk equivalence. The bottom leg below is the actual pair of
the ordinary pullback projections. Its matching is transported with a
full cone comparison.

This proves the square independently of the later assertion that the
ordinary pullback is a full subcategory of the directed pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section01.InvertiblePullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open Rezk 𝒯 M ℱ P I E public
open Rezk.RezkAxiom R
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullbackCone-isPullback;
    pullback-restrict-equivalence; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalPullbacks as Diagonal
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Cospans

iso-endpoints : {C : CAT} → MAP (Iso C) (C × C)
iso-endpoints = pair ev₀ ev₁ ∘ isoArrow

identity-endpoints : {C : CAT} →
  (iso-endpoints ∘ identityIso) =₁ pair (id C) (id C)
identity-endpoints = pair-cong identity-source identity-target ∙
  (pair-pre ev₀ ev₁ identityArrow ∙
    ((pair ev₀ ev₁ ◁ identityIso-arrow) ∙ comp-assoc identityIso isoArrow (pair ev₀ ev₁)))

module At {A B C : CAT} (f : MAP A C) (g : MAP B C) where
  F = productMap f g
  Δ = pair (id C) (id C)
  module D = Diagonal.DiagonalPullback 𝒯 P f g
    using (forward; forward-isEquiv; forward-left)

  change : CospanMap F Δ F iso-endpoints
  change = record
    { left = id (A × B) ; right = identityIso ; base = id (C × C)
    ; leftSquare = (comp-unitˡ F) ⁻¹ ∙ comp-unitʳ F
    ; rightSquare = (comp-unitˡ Δ) ⁻¹ ∙ identity-endpoints }
  module Change = CospanMap change using (pullbackMap; pullbackMap-β)
  module Equivalence = Cospans.CospanEquivalence 𝒯 P change
    (id-isEquiv (A × B)) (rezk-isEquiv C) (id-isEquiv (C × C))
    using (pullbackMap-isEquiv)

  comparison : MAP (Pullback f g) (Pullback F iso-endpoints)
  comparison = Change.pullbackMap ∘ D.forward

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-compose D.forward Change.pullbackMap
    D.forward-isEquiv Equivalence.pullbackMap-isEquiv

  projections = pair (pullback₁ {f = f} {g}) pullback₂
  raw = conePre comparison (pullbackCone F iso-endpoints)

  projection-comparison : Cone.left raw =₁ projections
  projection-comparison = comp-unitˡ projections ∙
    ((id (A × B) ◁ D.forward-left) ∙
    (comp-assoc D.forward pullback₁ (id (A × B)) ∙
    ((ConeIso.leftIso Change.pullbackMap-β ▷ D.forward) ∙
      (comp-assoc D.forward Change.pullbackMap pullback₁) ⁻¹)))

  normalized = coneRetarget raw projections (Cone.right raw)
    projection-comparison (idIso (Cone.right raw))

  normalization : ConeIso raw normalized
  normalization = coneRetarget-β raw projections (Cone.right raw)
    projection-comparison (idIso (Cone.right raw))

  square : Cone iso-endpoints F (Pullback f g)
  square = coneSwap normalized

  square-isPullback : IsPullback square
  square-isPullback = pullback-swap normalized
    (pullback-cone-invariant normalization
      (pullback-restrict-equivalence (pullbackCone F iso-endpoints) comparison
        (pullbackCone-isPullback F iso-endpoints) comparison-isEquiv))
```
