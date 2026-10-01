# Adjoint sections are preserved by base change

A pullback of a left or right adjoint section is again an adjoint section.
We lift its deformation over the base and transport invertibility of the
restriction along the section square. Joint reflection of invertibility
by the pullback projections and the relaxation theorem finish the proof.
No functoriality of universals or pointwise recognition principle is used.

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

module SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S using (module Over)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (retarget-reflects-invertible; identified-invertible; identity-invertible)
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ProjectedRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.BaseChangeDeformations as Deformations
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PullbackSectionCriterion as Criterion
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalizationConverse as Recovery

module WithSection {C D D′ T : CAT} (p : MAP C D) (s : MAP D C)
  (ρ : (p ∘ s) =₁ id D) (v : MAP D′ D) (t : Cone p v T) (et : IsPullback t) where
  module Lift = Deformations.At 𝒯 M ℱ P I E S p s ρ v t et
    using (u; q; j; κ; ρ′; module Left; module Right)
  open Lift using (u; q; j; κ; ρ′)
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ
    using (section-frame; base-frame; module Left; module Right)
  section : MAP D′ T
  section = j
  original-section : (u ∘ section) =₁ (s ∘ v)
  original-section = κ
  section-identification : (q ∘ section) =₁ id D′
  section-identification = ρ′

  module Left (ε : MorphismExpression (s ∘ p) (id C))
    (on-section : ExpressionIso
      (retarget-expression (N.Left.left-counit ε) N.section-frame (idIso s)) (identity-expression s))
    (over-base : ExpressionIso
      (retarget-expression (N.Left.right-counit ε) N.base-frame (idIso p)) (identity-expression p)) where
    module Changed = Lift.Left ε over-base using (value; underlying; source-frame; target-frame; left-image)
    abstract
      original-invertible : IsInvertibleExpression (restrict-expression ε s)
      original-invertible = retarget-reflects-invertible (restrict-expression ε s)
        (idIso ((s ∘ p) ∘ s)) (comp-unitˡ s)
        (retarget-reflects-invertible (N.Left.left-counit ε) N.section-frame (idIso s)
          (identified-invertible (expressionIso-inverse on-section) (identity-invertible s)))
      left-invertible : IsInvertibleExpression (post-expression u (restrict-expression Changed.underlying j))
      left-invertible = Restriction.At.value 𝒯 M ℱ P I E S ε s v u j κ Changed.underlying
        Changed.source-frame Changed.target-frame Changed.left-image original-invertible
      value : LeftAdjointSection q section
      value = Criterion.At.Left.value 𝒯 M ℱ P I E S Q R t et j ρ′ Changed.underlying
        (Over.MorphismOver.over-base Changed.value) left-invertible

  module Right (η : MorphismExpression (id C) (s ∘ p))
    (over-base : ExpressionIso
      (retarget-expression (N.Right.left-unit η) (idIso p) N.base-frame) (identity-expression p))
    (on-section : ExpressionIso
      (retarget-expression (N.Right.right-unit η) (idIso s) N.section-frame) (identity-expression s)) where
    module Changed = Lift.Right η over-base using (value; underlying; source-frame; target-frame; left-image)
    abstract
      original-invertible : IsInvertibleExpression (restrict-expression η s)
      original-invertible = retarget-reflects-invertible (restrict-expression η s)
        (comp-unitˡ s) (idIso ((s ∘ p) ∘ s))
        (retarget-reflects-invertible (N.Right.right-unit η) (idIso s) N.section-frame
          (identified-invertible (expressionIso-inverse on-section) (identity-invertible s)))
      left-invertible : IsInvertibleExpression (post-expression u (restrict-expression Changed.underlying j))
      left-invertible = Restriction.At.value 𝒯 M ℱ P I E S η s v u j κ Changed.underlying
        Changed.source-frame Changed.target-frame Changed.left-image original-invertible
      value : RightAdjointSection q section
      value = Criterion.At.Right.value 𝒯 M ℱ P I E S Q R t et j ρ′ Changed.underlying
        (Over.MorphismOver.over-base Changed.value) left-invertible

module Left {C D D′ T : CAT} {p : MAP C D} {s : MAP D C}
  (w : LeftAdjointSection p s) (v : MAP D′ D) (t : Cone p v T) (et : IsPullback t) where
  module Recovered = Recovery.Left 𝒯 M ℱ P I E S Q R w
    using (section-identification; on-section; over-base; module A)
  module Changed = WithSection p s Recovered.section-identification v t et
    using (section; section-identification; original-section; module Left)
  open Changed public using (section; section-identification; original-section)
  value : LeftAdjointSection (Cone.right t) section
  value = Changed.Left.value Recovered.A.counit Recovered.on-section Recovered.over-base

module Right {C D D′ T : CAT} {p : MAP C D} {s : MAP D C}
  (w : RightAdjointSection p s) (v : MAP D′ D) (t : Cone p v T) (et : IsPullback t) where
  module Recovered = Recovery.Right 𝒯 M ℱ P I E S Q R w
    using (section-identification; on-section; over-base; module A)
  module Changed = WithSection p s Recovered.section-identification v t et
    using (section; section-identification; original-section; module Right)
  open Changed public using (section; section-identification; original-section)
  value : RightAdjointSection (Cone.right t) section
  value = Changed.Right.value Recovered.A.unit Recovered.over-base Recovered.on-section

right-localization-base-change : {C D D′ T : CAT} {p : MAP C D} →
  RightBousfieldLocalization p → (v : MAP D′ D) →
  (t : Cone p v T) → IsPullback t → RightBousfieldLocalization (Cone.right t)
right-localization-base-change w v t et = record
  { section = Changed.section ; left-adjoint-section = Changed.value }
  where
  module W = RightBousfieldLocalization w
  module Changed = Left W.left-adjoint-section v t et using (section; value)

left-localization-base-change : {C D D′ T : CAT} {p : MAP C D} →
  LeftBousfieldLocalization p → (v : MAP D′ D) →
  (t : Cone p v T) → IsPullback t → LeftBousfieldLocalization (Cone.right t)
left-localization-base-change w v t et = record
  { section = Changed.section ; right-adjoint-section = Changed.value }
  where
  module W = LeftBousfieldLocalization w
  module Changed = Right W.right-adjoint-section v t et using (section; value)
```
