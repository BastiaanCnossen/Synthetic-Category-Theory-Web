# Universal lifts

For an arbitrary parameter category, the category of lifts projects
back to its parameters with an adjoint section. Its underlying arrow
is identified with the chosen lift restricted to the parameter functor.
For an absolute parameter this gives an initial covariant lift or a
terminal contravariant lift. The parameterized assertion is expressed
entirely through absolute pullbacks and adjoint sections.

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

module SCT.VolumeI.Chapter04.Section05.UniversalLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (pullbackCone-isPullback)
open Laws.PullbackStructure P using (Pullback; pullback₁; pullback₂; pullbackCone)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as Change
import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.LocalizationFibers as Fibers

module Covariant {A B : CAT} (f : MAP A B) (w : Fibration.CocartesianFibration f) where
  module Eval = Evaluation f using (directed-ev₀; module Left)
  module W = Fibration.CocartesianFibration w using (lift; left-adjoint-section)

  module Parameterized {Γ : CAT} (q : MAP Γ Eval.Left.category) where
    category = Pullback Eval.directed-ev₀ q
    projection : MAP category Γ
    projection = pullback₂
    module Result = Change.Left 𝒯 M ℱ P I E S Q R W.left-adjoint-section q
      (pullbackCone Eval.directed-ev₀ q) (pullbackCone-isPullback Eval.directed-ev₀ q)
      using (section; value; original-section)
    section : MAP Γ category
    section = Result.section
    adjoint-section : LeftAdjointSection projection section
    adjoint-section = Result.value
    image : (pullback₁ ∘ section) =₁ (W.lift ∘ q)
    image = Result.original-section

  module Absolute (q : Obj-abs Eval.Left.category) where
    module Result = Fibers.At.Initial 𝒯 M ℱ P I E S Q R Eval.directed-ev₀ q W.left-adjoint-section
      using (object; image; isInitial)
    open Result public

module Contravariant {A B : CAT} (f : MAP A B) (w : Fibration.CartesianFibration f) where
  module Eval = Evaluation f using (directed-ev₁; module Right)
  module W = Fibration.CartesianFibration w using (lift; right-adjoint-section)

  module Parameterized {Γ : CAT} (q : MAP Γ Eval.Right.category) where
    category = Pullback Eval.directed-ev₁ q
    projection : MAP category Γ
    projection = pullback₂
    module Result = Change.Right 𝒯 M ℱ P I E S Q R W.right-adjoint-section q
      (pullbackCone Eval.directed-ev₁ q) (pullbackCone-isPullback Eval.directed-ev₁ q)
      using (section; value; original-section)
    section : MAP Γ category
    section = Result.section
    adjoint-section : RightAdjointSection projection section
    adjoint-section = Result.value
    image : (pullback₁ ∘ section) =₁ (W.lift ∘ q)
    image = Result.original-section

  module Absolute (q : Obj-abs Eval.Right.category) where
    module Result = Fibers.At.Terminal 𝒯 M ℱ P I E S Q R Eval.directed-ev₁ q W.right-adjoint-section
      using (object; image; isTerminal)
    open Result public
```
