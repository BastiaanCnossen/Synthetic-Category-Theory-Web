# The two boundary composites of a framed square

Uncurry the vertical arrow to a square family and retain the comparison
with that arrow in its endpoint frames. The four corner equations then
transfer the two triangle presentations to the original boundary.

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

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareCommutativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ArrowCategorySquares 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.UncurryFramedSquare as Recovery
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareBoundaryTransfer as Transfer

module At {Γ C : CAT} {x y z w : MAP Γ C}
  {top : MorphismExpression x y} {right : MorphismExpression y z}
  {left : MorphismExpression x w} {bottom : MorphismExpression w z}
  (square : FramedSquare top right left bottom) where
  module F = FramedSquare square
  module N = MorphismExpression F.vertical
  module T = MorphismExpression top
  module R = MorphismExpression right
  module L = MorphismExpression left
  module B = MorphismExpression bottom
  module Recover = Recovery.At 𝒯 M ℱ N.arrow
  W = Recover.square
  module Curried = Recover.Curried
  ε = Recover.comparison
  left-frame = N.source-frame ∙ (ev₀ ◁ ε)
  right-frame = N.target-frame ∙ (ev₁ ◁ ε)
  left-side = left-frame ∙ (Curried.Vertical.boundary zero) ⁻¹
  right-side = right-frame ∙ (Curried.Vertical.boundary one) ⁻¹

  recovered-vertical : MorphismExpression L.arrow R.arrow
  recovered-vertical = record { arrow = Curried.nested
    ; source-frame = left-side ∙ Curried.Vertical.boundary zero
    ; target-frame = right-side ∙ Curried.Vertical.boundary one }
  vertical-comparison : ExpressionIso recovered-vertical F.vertical
  vertical-comparison = record { comparison = ε
    ; source-compatible = (cancel-inverse-tail left-frame (Curried.Vertical.boundary zero)) ⁻¹
    ; target-compatible = (cancel-inverse-tail right-frame (Curried.Vertical.boundary one)) ⁻¹ }

  top-edge : ExpressionIso
    (retarget-expression (post-expression ev₀ recovered-vertical) L.source-frame R.source-frame) top
  top-edge = expressionIso-compose F.top-edge
    (retarget-expressionIso (post-expressionIso ev₀ vertical-comparison) L.source-frame R.source-frame)
  bottom-edge : ExpressionIso
    (retarget-expression (post-expression ev₁ recovered-vertical) L.target-frame R.target-frame) bottom
  bottom-edge = expressionIso-compose F.bottom-edge
    (retarget-expressionIso (post-expressionIso ev₁ vertical-comparison) L.target-frame R.target-frame)
  top-side = ExpressionIso.comparison top-edge ∙ (Curried.Horizontal.comparison zero) ⁻¹
  bottom-side = ExpressionIso.comparison bottom-edge ∙ (Curried.Horizontal.comparison one) ⁻¹

  module E₀₀ = Endpoints.At 𝒯 M ℱ P I E S W zero zero T.source-frame L.source-frame
  module E₀₁ = Endpoints.At 𝒯 M ℱ P I E S W zero one T.target-frame R.source-frame
  module E₁₀ = Endpoints.At 𝒯 M ℱ P I E S W one zero B.source-frame L.target-frame
  module E₁₁ = Endpoints.At 𝒯 M ℱ P I E S W one one B.target-frame R.target-frame

  abstract
    top-image : (top-side ∙ Curried.Horizontal.comparison zero) =₂ ExpressionIso.comparison top-edge
    top-image = cancel-inverse-tail (ExpressionIso.comparison top-edge) (Curried.Horizontal.comparison zero)
    bottom-image : (bottom-side ∙ Curried.Horizontal.comparison one) =₂ ExpressionIso.comparison bottom-edge
    bottom-image = cancel-inverse-tail (ExpressionIso.comparison bottom-edge) (Curried.Horizontal.comparison one)

  module Boundary = Transfer.At 𝒯 M ℱ P I E S W top right left bottom
  module Compared = Boundary.Identified top-side right-side left-side bottom-side
    (E₀₀.from-endpoint top-side left-side
      (ExpressionIso.source-compatible top-edge ∙ isoComp-cong (idIso T.source-frame) (postWhisker ev₀ ◁ top-image)))
    (E₀₁.from-endpoint top-side right-side
      (ExpressionIso.target-compatible top-edge ∙ isoComp-cong (idIso T.target-frame) (postWhisker ev₁ ◁ top-image)))
    (E₁₀.from-endpoint bottom-side left-side
      (ExpressionIso.source-compatible bottom-edge ∙ isoComp-cong (idIso B.source-frame) (postWhisker ev₀ ◁ bottom-image)))
    (E₁₁.from-endpoint bottom-side right-side
      (ExpressionIso.target-compatible bottom-edge ∙ isoComp-cong (idIso B.target-frame) (postWhisker ev₁ ◁ bottom-image)))

  comparison : ExpressionIso (compose-expression top right) (compose-expression left bottom)
  comparison = Compared.comparison
```
