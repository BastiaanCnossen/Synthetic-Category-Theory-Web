# The unit and counit of a composite adjunction

The usual global formulas are compared with their expanded components.
The comparisons retain the external associators at their endpoints.
Triangle equations are established separately.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; restrict-retarget-outer)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (restrict-composition; retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeComponentFrames as Frames
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData as Data
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeTriangleAlgebra as Algebra

private
  abstract
    restrict-composite-frames : {Γ Δ C : CAT} {x y z : MAP Γ C}
      (f : MorphismExpression x y) (g : MorphismExpression y z) (r : MAP Δ Γ)
      {x′ y′ z′ : MAP Δ C} (p : (x ∘ r) =₁ x′) (q : (y ∘ r) =₁ y′) (t : (z ∘ r) =₁ z′) →
      ExpressionIso (retarget-expression (restrict-expression (compose-expression f g) r) p t)
        (compose-expression (retarget-expression (restrict-expression f r) p q)
          (retarget-expression (restrict-expression g r) q t))
    restrict-composite-frames f g r p q t = expressionIso-compose
      (expressionIso-inverse (retarget-composition (restrict-expression f r) (restrict-expression g r) p q t))
      (retarget-expressionIso (expressionIso-inverse (restrict-composition f g r)) p t)

    unit-frame : {Γ C : CAT} (x : MAP Γ C) →
      (((idIso x ∙ comp-unitˡ x) ∙ (idIso (id C) ▷ x))) =₂ comp-unitˡ x
    unit-frame x = isoComp-unitʳ-at (comp-unitˡ x) ∙
      isoComp-cong (isoComp-unitˡ-at (comp-unitˡ x)) (preWhisker-idIso (id _) x)

    post-identity-frame : {Γ C D : CAT} (F : MAP C D) (x : MAP Γ C)
      {z : MAP Γ D} (α : z =₁ (F ∘ x)) → ((F ◁ idIso x) ∙ α) =₂ α
    post-identity-frame F x α = isoComp-unitˡ-at α ∙
      isoComp-cong (postWhisker-idIso F x) (idIso α)

module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
  module A = Adjunction adjA using (unit; counit; unit-at; counit-at)
  module B = Adjunction adjB using (unit; counit; unit-at; counit-at)
  module AR = Restriction.Components 𝒯 M ℱ P I E S adjA using (counit-restrict)
  module BR = Restriction.Components 𝒯 M ℱ P I E S adjB using (unit-restrict)
  L = k ∘ l
  R = r ∘ s
  raw-unit = compose-expression A.unit (post-expression r (B.unit-at l))
  raw-counit = compose-expression (post-expression k (A.counit-at s)) B.counit
  unit = retarget-expression raw-unit (idIso (id C)) ((comp-assoc L s r) ⁻¹)
  counit = retarget-expression raw-counit ((comp-assoc R l k) ⁻¹) (idIso (id T))
  module Result = Data.Data 𝒯 M ℱ P I E S L R unit counit

  module Unit {Γ : CAT} (x : MAP Γ C) where
    module F = Frames.At 𝒯 x l k s r
    module K = Algebra.At.X.K 𝒯 M ℱ P I E S Q Γ
    module Expanded = Algebra.At.Composite 𝒯 M ℱ P I E S Q Γ adjA adjB
    finish = (r ◁ F.inner) ∙ comp-assoc x (s ∘ L) r

    abstract
      second : ExpressionIso
        (retarget-expression (restrict-expression (post-expression r (B.unit-at l)) x)
          (comp-assoc x l r) finish)
        (post-expression r (B.unit-at (l ∘ x)))
      second = expressionIso-compose (post-expressionIso r (BR.unit-restrict l x))
        (expressionIso-compose
          (restrict-post-frames r (B.unit-at l) x (idIso (l ∘ x)) F.inner)
          (retarget-cong (restrict-expression (post-expression r (B.unit-at l)) x)
            ((post-identity-frame r (l ∘ x) (comp-assoc x l r)) ⁻¹) (idIso finish)))

      raw-comparison : ExpressionIso (retarget-expression (Result.unit-at x) (idIso x) F.output)
        (compose-expression (A.unit-at x) (post-expression r (B.unit-at (l ∘ x))))
      raw-comparison = expressionIso-compose (compose-expression-cong (expressionIso-id (A.unit-at x)) second)
        (expressionIso-compose
          (restrict-composite-frames A.unit (post-expression r (B.unit-at l)) x (comp-unitˡ x) (comp-assoc x l r) finish)
          (expressionIso-compose
            (retarget-cong (restrict-expression raw-unit x) (unit-frame x)
              (F.comparison ∙ isoComp-assoc-at F.output F.outer (F.global ▷ x)))
            (expressionIso-compose
              (restrict-retarget-outer raw-unit (idIso (id C)) F.global x
                (idIso x ∙ comp-unitˡ x) (F.output ∙ F.outer))
              (retarget-assoc (restrict-expression unit x) (comp-unitˡ x) F.outer (idIso x) F.output))))

      comparison : ExpressionIso (retarget-expression (Result.unit-at x) (idIso x) F.output) (Expanded.expanded-unit x)
      comparison = expressionIso-compose
        (expressionIso-inverse (expressionIso-compose
          (compose-expression-cong (expressionIso-id (A.unit-at x)) (K.post-comparison r (B.unit-at (l ∘ x))))
          (K.composite-comparison (A.unit-at x) (K.post r (B.unit-at (l ∘ x)))))) raw-comparison

  module Counit {Γ : CAT} (y : MAP Γ T) where
    module F = Frames.At 𝒯 y s r l k
    module K = Algebra.At.X.K 𝒯 M ℱ P I E S Q Γ
    module Expanded = Algebra.At.Composite 𝒯 M ℱ P I E S Q Γ adjA adjB
    start = (k ◁ F.inner) ∙ comp-assoc y (l ∘ R) k

    abstract
      first : ExpressionIso
        (retarget-expression (restrict-expression (post-expression k (A.counit-at s)) y)
          start (comp-assoc y s k))
        (post-expression k (A.counit-at (s ∘ y)))
      first = expressionIso-compose (post-expressionIso k (AR.counit-restrict s y))
        (expressionIso-compose
          (restrict-post-frames k (A.counit-at s) y F.inner (idIso (s ∘ y)))
          (retarget-cong (restrict-expression (post-expression k (A.counit-at s)) y)
            (idIso start) ((post-identity-frame k (s ∘ y) (comp-assoc y s k)) ⁻¹)))

      raw-comparison : ExpressionIso (retarget-expression (Result.counit-at y) F.output (idIso y))
        (compose-expression (post-expression k (A.counit-at (s ∘ y))) (B.counit-at y))
      raw-comparison = expressionIso-compose (compose-expression-cong first (expressionIso-id (B.counit-at y)))
        (expressionIso-compose
          (restrict-composite-frames (post-expression k (A.counit-at s)) B.counit y start (comp-assoc y s k) (comp-unitˡ y))
          (expressionIso-compose
            (retarget-cong (restrict-expression raw-counit y)
              (F.comparison ∙ isoComp-assoc-at F.output F.outer (F.global ▷ y)) (unit-frame y))
            (expressionIso-compose
              (restrict-retarget-outer raw-counit F.global (idIso (id T)) y
                (F.output ∙ F.outer) (idIso y ∙ comp-unitˡ y))
              (retarget-assoc (restrict-expression counit y) F.outer (comp-unitˡ y) F.output (idIso y)))))

      comparison : ExpressionIso (retarget-expression (Result.counit-at y) F.output (idIso y)) (Expanded.expanded-counit y)
      comparison = expressionIso-compose
        (expressionIso-inverse (expressionIso-compose
          (compose-expression-cong (K.post-comparison k (A.counit-at (s ∘ y))) (expressionIso-id (B.counit-at y)))
          (K.composite-comparison (K.post k (A.counit-at (s ∘ y))) (B.counit-at y)))) raw-comparison
```
