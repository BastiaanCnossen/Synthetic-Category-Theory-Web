# Cartesian and cocartesian fibrations under base change

The directed-evaluation square of a pullback is itself a pullback. Pulling
back its left or right adjoint section gives the fibration structure on
the base-changed functor. This proves
`prop:Cartesian_Fibrations_Closed_Under_Base_Change` in both variances,
without functoriality of universals.

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

module SCT.VolumeI.Chapter04.Section05.BaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
import SCT.VolumeI.Chapter04.Section01.DirectedEvaluationBaseChange as EvaluationChange
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as SectionChange

module At {C D B X : CAT} {f : MAP C B} {v : MAP D B}
  (s : Cone f v X) (es : IsPullback s) where
  module Change = EvaluationChange.At 𝒯 M ℱ P I s es using (module Source; module Target)
  module Original = Fibration f using (CocartesianFibration; CartesianFibration)
  module Changed = Fibration (Cone.right s) using (CocartesianFibration; CartesianFibration)

  cocartesian : Original.CocartesianFibration → Changed.CocartesianFibration
  cocartesian w = record { lift = Result.section ; left-adjoint-section = Result.value }
    where
    module W = Original.CocartesianFibration w
    module Result = SectionChange.Left 𝒯 M ℱ P I E S Q R W.left-adjoint-section
      Change.Source.map Change.Source.square Change.Source.square-isPullback using (section; value)

  cartesian : Original.CartesianFibration → Changed.CartesianFibration
  cartesian w = record { lift = Result.section ; right-adjoint-section = Result.value }
    where
    module W = Original.CartesianFibration w
    module Result = SectionChange.Right 𝒯 M ℱ P I E S Q R W.right-adjoint-section
      Change.Target.map Change.Target.square Change.Target.square-isPullback using (section; value)
```
