# Fibrations over groupoids and product projections

For a category C, directed source and target evaluation over the
terminal category are obtained from ordinary evaluation by pulling
back along the endpoint equivalences. Their adjoint sections thus
supply both fibration structures on C → One. Base change then gives
both structures on each product projection. This completes the
absolute examples in `lem:Projection_Is_Cocartesian_Fibration`.

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

module SCT.VolumeI.Chapter04.Section05.Projections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section04.EvaluationAdjunctions 𝒯 M ℱ P I E S Q R
  using (source-evaluation-left-adjoint-section; target-evaluation-right-adjoint-section)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
import SCT.VolumeI.Chapter01.Section06.PullbackProducts as Products
import SCT.VolumeI.Chapter04.Section01.TerminalBase as TerminalBase
import SCT.VolumeI.Chapter04.Section02.GroupoidBase as GroupoidBase
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as SectionChange
import SCT.VolumeI.Chapter04.Section05.BaseChange as BaseChange

module OverTerminal (C : CAT) where
  module Eval = Evaluation (terminate C) using (directed-ev₀; directed-ev₁; module Left; module Right)
  module Terminal = TerminalBase.OverTerminal 𝒯 M ℱ P I C
    using (left-equivalence; right-equivalence; source-comparison; target-comparison)

  source-square : Cone (ev₀ {C}) Eval.Left.left (Ar C)
  source-square = record { left = id (Ar C) ; right = Eval.directed-ev₀
    ; match = Terminal.source-comparison ⁻¹ ∙ comp-unitʳ ev₀ }
  target-square : Cone (ev₁ {C}) Eval.Right.right (Ar C)
  target-square = record { left = id (Ar C) ; right = Eval.directed-ev₁
    ; match = Terminal.target-comparison ⁻¹ ∙ comp-unitʳ ev₁ }

  private
    module Source = SectionChange.Left 𝒯 M ℱ P I E S Q R
      (source-evaluation-left-adjoint-section C) Eval.Left.left source-square
      (degenerate-pullback Terminal.left-equivalence source-square (id-isEquiv (Ar C)))
      using (section; value)
    module Target = SectionChange.Right 𝒯 M ℱ P I E S Q R
      (target-evaluation-right-adjoint-section C) Eval.Right.right target-square
      (degenerate-pullback Terminal.right-equivalence target-square (id-isEquiv (Ar C)))
      using (section; value)

  cocartesian : Fibration.CocartesianFibration (terminate C)
  cocartesian = record { lift = Source.section ; left-adjoint-section = Source.value }
  cartesian : Fibration.CartesianFibration (terminate C)
  cartesian = record { lift = Target.section ; right-adjoint-section = Target.value }

module Product (C D : CAT) where
  module Square = Products.TerminalBase 𝒯 P (terminate C) (terminate D) using (productCone; productCone-isPullback)
  module Second = BaseChange.At 𝒯 M ℱ P I E S Q R Square.productCone Square.productCone-isPullback
    using (cocartesian; cartesian)
  module First = BaseChange.At 𝒯 M ℱ P I E S Q R (coneSwap Square.productCone)
    (pullback-swap Square.productCone Square.productCone-isPullback) using (cocartesian; cartesian)

  first-cocartesian : Fibration.CocartesianFibration (pr₁ {C = C} {D = D})
  first-cocartesian = First.cocartesian (OverTerminal.cocartesian D)
  first-cartesian : Fibration.CartesianFibration (pr₁ {C = C} {D = D})
  first-cartesian = First.cartesian (OverTerminal.cartesian D)
  second-cocartesian : Fibration.CocartesianFibration (pr₂ {C = C} {D = D})
  second-cocartesian = Second.cocartesian (OverTerminal.cocartesian C)
  second-cartesian : Fibration.CartesianFibration (pr₂ {C = C} {D = D})
  second-cartesian = Second.cartesian (OverTerminal.cartesian C)
```

The same argument applies over any groupoid. The directed-pullback
projections are equivalences, so the ordinary evaluation adjoint sections
pull back to sections of directed evaluation. No replacement of the given
functor is required. This proves the absolute assertion of
`prop:Isofibrations_Over_Groupoids_Are_Cocartesian`.

```agda
module OverGroupoid {C D : CAT} (f : MAP C D) (w : IsGroupoid D) where
  private
    module Eval = Evaluation f using (directed-ev₀; directed-ev₁; module Left; module Right)
    module Groupoid = GroupoidBase.OverGroupoid 𝒯 M ℱ P I E R f w
      using (left-projection-equivalence; right-projection-equivalence; source-comparison; target-comparison)

  source-square : Cone (ev₀ {C}) Eval.Left.left (Ar C)
  source-square = record { left = id (Ar C) ; right = Eval.directed-ev₀
    ; match = Groupoid.source-comparison ⁻¹ ∙ comp-unitʳ ev₀ }
  target-square : Cone (ev₁ {C}) Eval.Right.right (Ar C)
  target-square = record { left = id (Ar C) ; right = Eval.directed-ev₁
    ; match = Groupoid.target-comparison ⁻¹ ∙ comp-unitʳ ev₁ }

  private
    module Source = SectionChange.Left 𝒯 M ℱ P I E S Q R
      (source-evaluation-left-adjoint-section C) Eval.Left.left source-square
      (degenerate-pullback Groupoid.left-projection-equivalence source-square (id-isEquiv (Ar C)))
      using (section; value)
    module Target = SectionChange.Right 𝒯 M ℱ P I E S Q R
      (target-evaluation-right-adjoint-section C) Eval.Right.right target-square
      (degenerate-pullback Groupoid.right-projection-equivalence target-square (id-isEquiv (Ar C)))
      using (section; value)

  cocartesian : Fibration.CocartesianFibration f
  cocartesian = record { lift = Source.section ; left-adjoint-section = Source.value }
  cartesian : Fibration.CartesianFibration f
  cartesian = record { lift = Target.section ; right-adjoint-section = Target.value }
```
