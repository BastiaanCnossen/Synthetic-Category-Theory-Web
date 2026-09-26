# Unitality of joins

For `lem:Unitality_Of_Joins`, strictness of the initial category makes
the upper edge of either join pushout an equivalence. Mapping out then
shows that the lower edge is an equivalence. Composing with the
coproduct unit gives the actual inclusion of the remaining summand.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinUnits
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I)
  (Z : Initial.InitialStructure 𝒯 M) (strict : Initial.StrictInitial 𝒯 M Z) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Initial.InitialStructure Z
open Initial.StrictInitial strict
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-all)
open import SCT.VolumeI.Chapter01.Section05.CoproductEquivalences 𝒯 M Z B
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback-converse)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_; join-in₁; join-in₂)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J

pushout-equivalence : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  (s : Square u l r v) → IsPushout s → IsEquiv u → IsEquiv v
pushout-equivalence {u = u} {v = v} s es eu = pre-tests-all v (λ E →
  degenerate-pullback-converse (mapPre-isEquiv u eu)
    (coneSwap (mappingOut s E)) (pullback-swap (mappingOut s E) (es E)))

module LeftUnit (C : CAT) where
  module Diagram = Span (terminate Zero) (terminate C)
  module Pushout = JoinPushout (mapping-out (terminate Zero) (terminate C) one-isAn)

  top-isEquiv : IsEquiv Diagram.top
  top-isEquiv = equiv-cancel-left Diagram.top (pullback₁ ∘ pr₁)
    (into-zero-isEquiv (pullback₁ ∘ pr₁)) (into-zero-isEquiv ((pullback₁ ∘ pr₁) ∘ Diagram.top))

  inclusion-isEquiv : IsEquiv (join-in₂ {Zero} {C})
  inclusion-isEquiv = equiv-compose in₂ (inclusion (terminate Zero) (terminate C))
    (equiv-inverse (coproduct-unitˡ-isEquiv C))
    (pushout-equivalence Pushout.square Pushout.universal top-isEquiv)

module RightUnit (C : CAT) where
  module Diagram = Span (terminate C) (terminate Zero)
  module Pushout = JoinPushout (mapping-out (terminate C) (terminate Zero) one-isAn)

  top-isEquiv : IsEquiv Diagram.top
  top-isEquiv = equiv-cancel-left Diagram.top (pullback₂ ∘ pr₁)
    (into-zero-isEquiv (pullback₂ ∘ pr₁)) (into-zero-isEquiv ((pullback₂ ∘ pr₁) ∘ Diagram.top))

  inclusion-isEquiv : IsEquiv (join-in₁ {C} {Zero})
  inclusion-isEquiv = equiv-compose in₁ (inclusion (terminate C) (terminate Zero))
    (equiv-inverse (coproduct-unitʳ-isEquiv C))
    (pushout-equivalence Pushout.square Pushout.universal top-isEquiv)
```
