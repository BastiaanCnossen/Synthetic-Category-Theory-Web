# The categories of one-sided inverse data

Over an invertible family, either inverse triangle has a unique choice.
The long-edge composition equivalence is pulled back at identity arrows;
reordering the pullbacks identifies this with the actual category of
one-sided inverse triangles. Neither assertion uses Rezk.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.OneSidedInverseFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UniversalInverseExpressions 𝒯 M ℱ P I E S public
open Laws.PullbackStructure P
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.RightTriangleAction as Right
import SCT.VolumeI.Chapter02.Section03.CompositionCalculus.LeftTriangleAction as Left
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantLongEdgeFiber as Constant
import SCT.VolumeI.Chapter02.Section03.PullbackCalculus.TwoStageFibers as Reorder

InverseTriangle : CAT → CAT
InverseTriangle C = Pullback (edge₁ {C}) identityArrow

rightInverseArrow leftInverseArrow : {C : CAT} → MAP (InverseTriangle C) (Ar C)
rightInverseArrow = edge₀ ∘ pullback₁
leftInverseArrow = edge₂ ∘ pullback₁

module At {B C : CAT} (f : MAP B (Ar C)) where
  private
    module RightAction = Right.At 𝒯 M ℱ P I E S Q f
      using (arrow; long-cone; long-isPullback)
    module LeftAction = Left.At 𝒯 M ℱ P I E S Q f
      using (arrow; long-cone; long-isPullback)
    module RightOrder = Reorder.At 𝒯 P f edge₀ edge₁ identityArrow
      using (projection-isEquiv)
    module LeftOrder = Reorder.At 𝒯 P f edge₂ edge₁ identityArrow
      using (projection-isEquiv)

  right-inverse-projection-isEquiv : IsInvertibleExpression RightAction.arrow →
    IsEquiv (pullback₂ {f = rightInverseArrow} {f})
  right-inverse-projection-isEquiv witness = RightOrder.projection-isEquiv
    (Constant.At.projection-isEquiv 𝒯 P ev₁ identityArrow identity-target
      RightAction.long-cone (RightAction.long-isPullback witness))

  left-inverse-projection-isEquiv : IsInvertibleExpression LeftAction.arrow →
    IsEquiv (pullback₂ {f = leftInverseArrow} {f})
  left-inverse-projection-isEquiv witness = LeftOrder.projection-isEquiv
    (Constant.At.projection-isEquiv 𝒯 P ev₀ identityArrow identity-source
      LeftAction.long-cone (LeftAction.long-isPullback witness))

module UniversalFibers (C : CAT) where
  private
    module U = Universal C
      using (inverse-data)
    module Fibers = At (isoArrow {C})
      using (left-inverse-projection-isEquiv; right-inverse-projection-isEquiv)

  right-inverse-projection-isEquiv :
    IsEquiv (pullback₂ {f = rightInverseArrow} {isoArrow {C}})
  right-inverse-projection-isEquiv = Fibers.right-inverse-projection-isEquiv U.inverse-data

  left-inverse-projection-isEquiv :
    IsEquiv (pullback₂ {f = leftInverseArrow} {isoArrow {C}})
  left-inverse-projection-isEquiv = Fibers.left-inverse-projection-isEquiv U.inverse-data
```
