# Fibration structures under equivalences

A square whose horizontal functors are equivalences is a pullback.
Base change therefore transports cartesian and cocartesian fibration
structures across such a square, with its specified matching.
Isomorphic functors are a special case.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.EquivalenceInvariance
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter04.Section05.BaseChange as BaseChange

module Along {C D B X : CAT} {f : MAP C B} {v : MAP D B}
  (s : Cone f v X) (ev : IsEquiv v) (eu : IsEquiv (Cone.left s)) where
  private
    es : IsPullback s
    es = degenerate-pullback ev s eu
  module Changed = BaseChange.At 𝒯 M ℱ P I E S Q R s es using (cocartesian; cartesian)
  open Changed public using (cocartesian; cartesian)

module Isomorphic {A B : CAT} {f g : MAP A B} (α : f =₁ g) where
  square : Cone f (id B) A
  square = record { left = id A ; right = g
    ; match = (comp-unitˡ g) ⁻¹ ∙ (α ∙ comp-unitʳ f) }
  module Changed = Along square (id-isEquiv B) (id-isEquiv A)
  open Changed public using (cocartesian; cartesian)
```
