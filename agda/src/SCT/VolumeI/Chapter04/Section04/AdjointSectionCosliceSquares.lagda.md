# The coslice square of a left adjoint section

For an adjunction with invertible unit, the usual functor on coslices
induced by the right adjoint forms a pullback over that right adjoint.
Its source comparison is the inverse of the specified unit component.
This follows by normalizing transposition and retaining the complete
cone comparison with the usual coslice functor.

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

module SCT.VolumeI.Chapter04.Section04.AdjointSectionCosliceSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TranspositionWithInvertibleUnit as Unit
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CosliceTranspositionExpressions as Normalization
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CoslicePullbackRecognition as Recognition

module WithUnit {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (κ : id C =₁ (r ∘ l))
  (unit-comparison : ExpressionIso (Adjunction.unit adj) (isomorphism-expression κ))
  (b : Obj-abs C) where
  private
    module U = Unit.WithUnit 𝒯 M ℱ P I E S adj κ unit-comparison using (unit-frame)
    module Normal = Normalization.WithUnit.Realized 𝒯 M ℱ P I E S adj κ unit-comparison b Q
      using (normalized; normalized-isEquiv)
    module Recognize = Recognition.At 𝒯 M ℱ P I r (l ∘ b) b ((U.unit-frame b) ⁻¹)
      using (functor; square; comparison; introduction; module Recognized)

  source-comparison : (r ∘ (l ∘ b)) =₁ b
  source-comparison = (U.unit-frame b) ⁻¹

  open Recognize public using (functor; square; comparison; introduction)

  abstract
    square-isPullback : IsPullback square
    square-isPullback = Recognize.Recognized.square-isPullback Normal.normalized-isEquiv
```

Rezk recovery supplies the specified unit identification for any left
adjoint section. The displayed source frame continues to use this
recovered identification, without replacing it by an unrelated section
comparison.

```agda
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section03.RezkRecovery as Recovery
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S
  using (LeftAdjointSection)

module FromSection (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  {C D : CAT} {p : MAP C D} {s : MAP D C} (w : LeftAdjointSection p s)
  (b : Obj-abs D) where
  private
    module W = LeftAdjointSection w using (adjunction; unit-invertible)
    module A = Adjunction W.adjunction using (unit)
    module Recovered = Recovery.Recover 𝒯 M ℱ P I E R A.unit
      (invertible-expression-lift A.unit W.unit-invertible)
      using (identification; isomorphism-recovery)
  open WithUnit W.adjunction Recovered.identification
    (expressionIso-inverse Recovered.isomorphism-recovery) b public
    using (source-comparison; functor; square; comparison; introduction; square-isPullback)
```
