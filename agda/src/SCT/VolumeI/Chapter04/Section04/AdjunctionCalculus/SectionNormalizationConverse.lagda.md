# Recovering normalized data from adjoint sections

The invertible unit or counit determines the section identification by
Rezk recovery. Its full expression comparison and the two triangles then
force both normalization equations. This is the converse to the
construction in `NormalizedSections`, with the original counit or unit.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalizationConverse
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-cong)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S
  using (invertible-expression-lift)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
import SCT.VolumeI.Chapter02.Section03.RezkRecovery as Recovery
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.NormalizedTriangles as Triangles
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized

module Left {C D : CAT} {p : MAP C D} {s : MAP D C} (w : LeftAdjointSection p s) where
  module W = LeftAdjointSection w
  module A = W.A
  module Recovered = Recovery.Recover 𝒯 M ℱ P I E R A.unit
    (invertible-expression-lift A.unit W.unit-invertible)
  section-identification : (p ∘ s) =₁ id D
  section-identification = Recovered.identification ⁻¹
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s section-identification
  module Data = N.Left A.counit

  abstract
    unit-comparison : ExpressionIso A.unit Data.unit
    unit-comparison = expressionIso-compose
      (isomorphism-cong ((inverse-inverse Recovered.identification) ⁻¹))
      (expressionIso-inverse Recovered.isomorphism-recovery)

    left-unit-comparison : ExpressionIso A.left-unit (isomorphism-expression (N.section-frame ⁻¹))
    left-unit-comparison = expressionIso-compose Data.left-unit-identified
      (retarget-expressionIso (post-expressionIso s unit-comparison)
        (comp-unitʳ s) ((comp-assoc s p s) ⁻¹))

    right-unit-comparison : ExpressionIso A.right-unit (isomorphism-expression (N.base-frame ⁻¹))
    right-unit-comparison = expressionIso-compose Data.right-unit-identified
      (retarget-expressionIso (restrict-expressionIso unit-comparison p)
        (comp-unitˡ p) (idIso ((p ∘ s) ∘ p)))

    on-section : ExpressionIso
      (retarget-expression Data.left-counit N.section-frame (idIso s)) (identity-expression s)
    on-section = Triangles.At.normalize-counit 𝒯 M ℱ P I E S Q N.section-frame
      A.left-unit A.left-counit A.left-triangle left-unit-comparison

    over-base : ExpressionIso
      (retarget-expression Data.right-counit N.base-frame (idIso p)) (identity-expression p)
    over-base = Triangles.At.normalize-counit 𝒯 M ℱ P I E S Q N.base-frame
      A.right-unit A.right-counit A.right-triangle right-unit-comparison

  module Result = Data.Normalized on-section over-base

module Right {C D : CAT} {p : MAP C D} {s : MAP D C} (w : RightAdjointSection p s) where
  module W = RightAdjointSection w
  module A = W.A
  module Recovered = Recovery.Recover 𝒯 M ℱ P I E R A.counit
    (invertible-expression-lift A.counit W.counit-invertible)
  section-identification : (p ∘ s) =₁ id D
  section-identification = Recovered.identification
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s section-identification
  module Data = N.Right A.unit

  abstract
    counit-comparison : ExpressionIso A.counit Data.counit
    counit-comparison = expressionIso-inverse Recovered.isomorphism-recovery

    left-counit-comparison : ExpressionIso A.left-counit (isomorphism-expression N.base-frame)
    left-counit-comparison = expressionIso-compose Data.left-counit-identified
      (retarget-expressionIso (restrict-expressionIso counit-comparison p)
        (idIso ((p ∘ s) ∘ p)) (comp-unitˡ p))

    right-counit-comparison : ExpressionIso A.right-counit (isomorphism-expression N.section-frame)
    right-counit-comparison = expressionIso-compose Data.right-counit-identified
      (retarget-expressionIso (post-expressionIso s counit-comparison)
        ((comp-assoc s p s) ⁻¹) (comp-unitʳ s))

    over-base : ExpressionIso
      (retarget-expression Data.left-unit (idIso p) N.base-frame) (identity-expression p)
    over-base = Triangles.At.normalize-unit 𝒯 M ℱ P I E S Q N.base-frame
      A.left-unit A.left-counit A.left-triangle left-counit-comparison

    on-section : ExpressionIso
      (retarget-expression Data.right-unit (idIso s) N.section-frame) (identity-expression s)
    on-section = Triangles.At.normalize-unit 𝒯 M ℱ P I E S Q N.section-frame
      A.right-unit A.right-counit A.right-triangle right-counit-comparison

  module Result = Data.Normalized over-base on-section
```
