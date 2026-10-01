# Recognizing an adjoint section through pullback projections

For a section of the right projection of a pullback, a relative
deformation is enough when its restriction to the section has invertible
left projection. The right projection is already the identity by the
relative normalization. Joint reflection of invertibility and the
relaxation criterion then produce the adjoint section.

This is the recognition step of base change. The construction of the
lifted deformation and the proof of its left-projection hypothesis are
separate obligations.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PullbackSectionCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (post-retarget)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (identified-invertible; identity-invertible; retarget-invertible)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.PullbackInvertibility 𝒯 M ℱ P I E S Q R
  using (pullback-reflects-invertible)
import SCT.VolumeI.Chapter04.Section04.RelaxedAdjointSections as Relaxed
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalization as Transfer

module At {C D B T : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (et : IsPullback t) (j : MAP D T)
  (ρ : (Cone.right t ∘ j) =₁ id D) where
  u = Cone.left t
  q = Cone.right t
  module Criterion = Relaxed.WithSection 𝒯 M ℱ P I E S q j ρ
    using (u; v; α; β; module Left; module Right)

  module Left (ε : MorphismExpression (j ∘ q) (id T))
    (over-base : ExpressionIso
      (retarget-expression (post-expression q ε) Criterion.u Criterion.v) (identity-expression q))
    (left-invertible : IsInvertibleExpression (post-expression u (restrict-expression ε j))) where
    module Normal = Transfer.WithSection.Left 𝒯 M ℱ P I E q j ρ ε using (on-section; identity)

    left : IsInvertibleExpression (post-expression u Normal.on-section)
    left = identified-invertible
      (expressionIso-inverse (post-retarget u (restrict-expression ε j) Criterion.α Criterion.β))
      (retarget-invertible (post-expression u (restrict-expression ε j))
        (u ◁ Criterion.α) (u ◁ Criterion.β) left-invertible)
    right : IsInvertibleExpression (post-expression q Normal.on-section)
    right = identified-invertible (expressionIso-inverse (Normal.identity over-base))
      (identity-invertible (q ∘ j))
    on-section : IsInvertibleExpression Normal.on-section
    on-section = pullback-reflects-invertible t et Normal.on-section left right
    value : LeftAdjointSection q j
    value = Criterion.Left.Invertible.value ε over-base on-section

  module Right (η : MorphismExpression (id T) (j ∘ q))
    (over-base : ExpressionIso
      (retarget-expression (post-expression q η) Criterion.v Criterion.u) (identity-expression q))
    (left-invertible : IsInvertibleExpression (post-expression u (restrict-expression η j))) where
    module Normal = Transfer.WithSection.Right 𝒯 M ℱ P I E q j ρ η using (on-section; identity)

    left : IsInvertibleExpression (post-expression u Normal.on-section)
    left = identified-invertible
      (expressionIso-inverse (post-retarget u (restrict-expression η j) Criterion.β Criterion.α))
      (retarget-invertible (post-expression u (restrict-expression η j))
        (u ◁ Criterion.β) (u ◁ Criterion.α) left-invertible)
    right : IsInvertibleExpression (post-expression q Normal.on-section)
    right = identified-invertible (expressionIso-inverse (Normal.identity over-base))
      (identity-invertible (q ∘ j))
    on-section : IsInvertibleExpression Normal.on-section
    on-section = pullback-reflects-invertible t et Normal.on-section left right
    value : RightAdjointSection q j
    value = Criterion.Right.Invertible.value η over-base on-section
```
