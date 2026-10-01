# Universal objects of slices and coslices

Target evaluation has the identity-arrow functor as a right adjoint
section; source evaluation has it as a left adjoint section. Pulling back
along an object gives a terminal object of its slice and an initial object
of its coslice. The projection comparison identifies the underlying arrow
with the identity arrow at the given object. This proves
`lem:Slice_Category_Admits_Terminal_Object` and its dual.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.SliceUniversalObjects
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I
  using (module SliceEndpoint; module CosliceEndpoint)
open import SCT.VolumeI.Chapter04.Section04.EvaluationAdjunctions 𝒯 M ℱ P I E S Q R
  using (target-evaluation-right-adjoint-section; source-evaluation-left-adjoint-section)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as Change
import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.AdjunctionCharacterization as Universal

module SliceAt {C : CAT} (x : Obj-abs C) where
  module Endpoint = SliceEndpoint x using (square; square-isPullback)
  module Changed = Change.Right 𝒯 M ℱ P I E S Q R
    (target-evaluation-right-adjoint-section C) x Endpoint.square Endpoint.square-isPullback
    using (section; value; original-section)
  object : Obj-abs (Slice C x)
  object = Changed.section
  isTerminal : IsTerminal object
  isTerminal = Universal.right-adjoint-section-is-terminal 𝒯 M ℱ P I E S Q object Changed.value
  identity-arrow : (EndpointFiber.arrow (id C) (const x) ∘ object) =₁ (identityArrow ∘ x)
  identity-arrow = Changed.original-section

module CosliceAt {C : CAT} (x : Obj-abs C) where
  module Endpoint = CosliceEndpoint x using (square; square-isPullback)
  module Changed = Change.Left 𝒯 M ℱ P I E S Q R
    (source-evaluation-left-adjoint-section C) x Endpoint.square Endpoint.square-isPullback
    using (section; value; original-section)
  object : Obj-abs (Coslice C x)
  object = Changed.section
  isInitial : IsInitial object
  isInitial = Universal.left-adjoint-section-is-initial 𝒯 M ℱ P I E S Q object Changed.value
  identity-arrow : (EndpointFiber.arrow (const x) (id C) ∘ object) =₁ (identityArrow ∘ x)
  identity-arrow = Changed.original-section
```
