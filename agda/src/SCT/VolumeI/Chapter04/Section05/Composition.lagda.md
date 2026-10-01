# Composition of cartesian and cocartesian fibrations

Directed evaluation of a composite factors as directed evaluation of
the first functor followed by a base change of directed evaluation of
the second. Base change and composition of adjoint sections therefore
give the desired section. The full upper triangle then transports this
structure to the chosen directed evaluation of the composite.
This proves `prop:Cartesian_Fibrations_Closed_Under_Composition` in
both variances.

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

module SCT.VolumeI.Chapter04.Section05.Composition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section01.DirectedEvaluationComposition as EvaluationComposition
import SCT.VolumeI.Chapter04.Section04.CompositeBaseChange as Compose

module At {A B C : CAT} (f : MAP A B) (g : MAP B C) where
  module Source = EvaluationComposition.At.Source 𝒯 M ℱ P I f g
    using (right-map; square; square-isPullback; triangle)
  module Target = EvaluationComposition.At.Target 𝒯 M ℱ P I f g
    using (right-map; square; square-isPullback; triangle)

  module Covariant (wf : Fibration.CocartesianFibration f) (wg : Fibration.CocartesianFibration g) where
    private
      module WF = Fibration.CocartesianFibration wf using (lift; left-adjoint-section)
      module WG = Fibration.CocartesianFibration wg using (lift; left-adjoint-section)
      module Result = Compose.Along.Right 𝒯 M ℱ P I E S Q R
        Source.square Source.square-isPullback Source.triangle
        (record { section = WF.lift ; left-adjoint-section = WF.left-adjoint-section })
        (record { section = WG.lift ; left-adjoint-section = WG.left-adjoint-section })
        using (value; section-comparison; intermediate-section)
    intermediate-section = Result.intermediate-section
    value : Fibration.CocartesianFibration (g ∘ f)
    value = record { lift = RightBousfieldLocalization.section Result.value
      ; left-adjoint-section = RightBousfieldLocalization.left-adjoint-section Result.value }
    lift-comparison : Fibration.CocartesianFibration.lift value =₁ (WF.lift ∘ intermediate-section)
    lift-comparison = Result.section-comparison

  module Contravariant (wf : Fibration.CartesianFibration f) (wg : Fibration.CartesianFibration g) where
    private
      module WF = Fibration.CartesianFibration wf using (lift; right-adjoint-section)
      module WG = Fibration.CartesianFibration wg using (lift; right-adjoint-section)
      module Result = Compose.Along.Left 𝒯 M ℱ P I E S Q R
        Target.square Target.square-isPullback Target.triangle
        (record { section = WF.lift ; right-adjoint-section = WF.right-adjoint-section })
        (record { section = WG.lift ; right-adjoint-section = WG.right-adjoint-section })
        using (value; section-comparison; intermediate-section)
    intermediate-section = Result.intermediate-section
    value : Fibration.CartesianFibration (g ∘ f)
    value = record { lift = LeftBousfieldLocalization.section Result.value
      ; right-adjoint-section = LeftBousfieldLocalization.right-adjoint-section Result.value }
    lift-comparison : Fibration.CartesianFibration.lift value =₁ (WF.lift ∘ intermediate-section)
    lift-comparison = Result.section-comparison
```
