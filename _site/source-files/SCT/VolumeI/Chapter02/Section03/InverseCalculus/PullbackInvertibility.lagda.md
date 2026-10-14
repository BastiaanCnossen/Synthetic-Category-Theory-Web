# Pullback projections jointly reflect invertibility

A family of morphisms in a pullback is invertible when both projected
families are invertible. Rezk identifies the projected arrows with
constant diagrams. The embedding of constant arrows lifts their actual
matching, and the arrow-category pullback then recovers a constant
presentation of the original family. This is an argument for the whole
parameterized family, without pointwise detection of equivalences.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.PullbackInvertibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.LiftedInverseExpressions 𝒯 M ℱ P I E S public
  using (IsInvertibleExpression)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
  using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.LiftedInverseExpressions 𝒯 M ℱ P I E S
  using (lift-invertible-expression; IsoLift)
open Rezk 𝒯 M ℱ P I E using (identityIso; identityIso-arrow; isoArrow)
import SCT.VolumeI.Chapter02.Section03.RezkIdentification as Identification
import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding as Embedding
import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.ConeLifting as Lifting
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramNaturality as Constants
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeNaturality as ConstantCones

module At {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (et : IsPullback t) {x y : MAP Γ T}
  (α : MorphismExpression x y)
  (left-invertible : IsInvertibleExpression (post-expression (Cone.left t) α))
  (right-invertible : IsInvertibleExpression (post-expression (Cone.right t) α)) where
  module Left = Identification.Identify 𝒯 M ℱ P I E R
    (post-expression (Cone.left t) α)
    (invertible-expression-lift (post-expression (Cone.left t) α) left-invertible)
    using (center; constant-comparison)
  module Right = Identification.Identify 𝒯 M ℱ P I E R
    (post-expression (Cone.right t) α)
    (invertible-expression-lift (post-expression (Cone.right t) α) right-invertible)
    using (center; constant-comparison)
  module Constant = Constants.At 𝒯 M ℱ [1] using (module Post)
  module BaseEmbedding = Embedding.WithRezk 𝒯 M ℱ P I E S Q R
    using (identityArrow-isEmbedding)
  module Pullback = Lifting.PullbackComparison 𝒯 P f g (funPost f) (funPost g)
    identityArrow identityArrow identityArrow (Constant.Post.value f) (Constant.Post.value g)
    (BaseEmbedding.identityArrow-isEmbedding B)
    t et (mappedCone [1] t) (fun-preserves-pullback [1] t et) identityArrow
    using (module WithComparison)
  module Found = Pullback.WithComparison (ConstantCones.At.value 𝒯 M ℱ P [1] t)
    (MorphismExpression.arrow α) Left.center Right.center Left.constant-comparison Right.constant-comparison
    using (value; comparison)

  constant-presentation : (identityArrow ∘ Found.value) =₁ MorphismExpression.arrow α
  constant-presentation = Found.comparison

  lift : IsoLift (MorphismExpression.arrow α)
  lift = record { lift = identityIso ∘ Found.value
    ; comparison = constant-presentation ∙
        ((identityIso-arrow ▷ Found.value) ∙ (comp-assoc Found.value identityIso isoArrow) ⁻¹) }

  value : IsInvertibleExpression α
  value = lift-invertible-expression α lift

pullback-reflects-invertible : {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) → IsPullback t → {x y : MAP Γ T} (α : MorphismExpression x y) →
  IsInvertibleExpression (post-expression (Cone.left t) α) →
  IsInvertibleExpression (post-expression (Cone.right t) α) → IsInvertibleExpression α
pullback-reflects-invertible = At.value
```
