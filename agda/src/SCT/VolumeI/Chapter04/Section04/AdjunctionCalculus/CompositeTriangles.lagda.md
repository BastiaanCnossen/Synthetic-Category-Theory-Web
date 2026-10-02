# Triangle identities for the composite adjunction

The expanded triangle identities descend through the explicit endpoint
associators of the composite unit and counit.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DoublePostcompositionFrames 𝒯 M ℱ P I E
  using (post-composite-frames; double-post-id; double-post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.NormalizedIdentityExpressions 𝒯 M ℱ P I E
  using (identity-reflect)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeComponents as Components
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeExpandedComponents as Expanded

private
  abstract
    double-id-frame : {Γ B C D : CAT} (F : MAP B C) (G : MAP C D) (x : MAP Γ B)
      {z : MAP Γ D} (a : z =₁ (G ∘ (F ∘ x))) →
      ((G ◁ (F ◁ idIso x)) ∙ a) =₂ a
    double-id-frame F G x a = isoComp-unitˡ-at a ∙
      isoComp-cong (double-post-id F G x) (idIso a)

module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
  {k : MAP D T} {s : MAP T D} (adjA : Adjunction l r) (adjB : Adjunction k s) where
  module Data = Components.Composite 𝒯 M ℱ P I E S Q adjA adjB
  module A = Data.Result
  L = k ∘ l
  R = r ∘ s

  module Left {Γ : CAT} (x : MAP Γ C) where
    module U = Data.Unit x
    module V = Data.Counit (L ∘ x)
    module X = Expanded.At 𝒯 M ℱ P I E S Q {Γ = Γ} adjA adjB
    α = comp-assoc x l k
    n = k ◁ (l ◁ (r ◁ (s ◁ α)))
    middle = (k ◁ (l ◁ U.F.output)) ∙ comp-assoc (R ∘ (L ∘ x)) l k
    first = post-expression L (A.unit-at x)
    second = A.counit-at (L ∘ x)

    abstract
      middle-comparison : middle =₂ (n ∙ V.F.output)
      middle-comparison = isoComp-assoc-at n (k ◁ (l ◁ comp-assoc (L ∘ x) s r))
          (comp-assoc (R ∘ (L ∘ x)) l k) ∙
        isoComp-cong (double-post-composition l k (r ◁ (s ◁ α)) (comp-assoc (L ∘ x) s r))
          (idIso (comp-assoc (R ∘ (L ∘ x)) l k))

      first-comparison : ExpressionIso (retarget-expression first α middle)
        (post-expression k (post-expression l (X.expanded-unit x)))
      first-comparison = expressionIso-compose (post-expressionIso k (post-expressionIso l U.raw-comparison))
        (expressionIso-compose (post-composite-frames l k (A.unit-at x) (idIso x) U.F.output)
          (retarget-cong first ((double-id-frame l k x α) ⁻¹) (idIso middle)))

      second-comparison : ExpressionIso (retarget-expression second middle α)
        (X.expanded-counit (k ∘ (l ∘ x)))
      second-comparison = expressionIso-compose (X.counit-parameter α)
        (expressionIso-compose (retarget-expressionIso V.raw-comparison n α)
          (expressionIso-compose (expressionIso-inverse (retarget-assoc second V.F.output (idIso (L ∘ x)) n α))
            (retarget-cong second middle-comparison ((isoComp-unitʳ-at α) ⁻¹))))

      triangle : ExpressionIso (compose-expression first second) (identity-expression (L ∘ x))
      triangle = identity-reflect (compose-expression first second) α
        (expressionIso-compose (X.left-triangle x)
          (expressionIso-compose (compose-expression-cong first-comparison second-comparison)
            (expressionIso-inverse (retarget-composition first second α middle α))))

  module Right {Γ : CAT} (y : MAP Γ T) where
    module U = Data.Unit (R ∘ y)
    module V = Data.Counit y
    module X = Expanded.At 𝒯 M ℱ P I E S Q {Γ = Γ} adjA adjB
    b = comp-assoc y s r
    n = r ◁ (s ◁ (k ◁ (l ◁ b)))
    middle = (r ◁ (s ◁ V.F.output)) ∙ comp-assoc (L ∘ (R ∘ y)) s r
    first = A.unit-at (R ∘ y)
    second = post-expression R (A.counit-at y)

    abstract
      middle-comparison : middle =₂ (n ∙ U.F.output)
      middle-comparison = isoComp-assoc-at n (r ◁ (s ◁ comp-assoc (R ∘ y) l k))
          (comp-assoc (L ∘ (R ∘ y)) s r) ∙
        isoComp-cong (double-post-composition s r (k ◁ (l ◁ b)) (comp-assoc (R ∘ y) l k))
          (idIso (comp-assoc (L ∘ (R ∘ y)) s r))

      first-comparison : ExpressionIso (retarget-expression first b middle)
        (X.expanded-unit (r ∘ (s ∘ y)))
      first-comparison = expressionIso-compose (X.unit-parameter b)
        (expressionIso-compose (retarget-expressionIso U.raw-comparison b n)
          (expressionIso-compose (expressionIso-inverse (retarget-assoc first (idIso (R ∘ y)) U.F.output b n))
            (retarget-cong first ((isoComp-unitʳ-at b) ⁻¹) middle-comparison)))

      second-comparison : ExpressionIso (retarget-expression second middle b)
        (post-expression r (post-expression s (X.expanded-counit y)))
      second-comparison = expressionIso-compose (post-expressionIso r (post-expressionIso s V.raw-comparison))
        (expressionIso-compose (post-composite-frames s r (A.counit-at y) V.F.output (idIso y))
          (retarget-cong second (idIso middle) ((double-id-frame s r y b) ⁻¹)))

      triangle : ExpressionIso (compose-expression first second) (identity-expression (R ∘ y))
      triangle = identity-reflect (compose-expression first second) b
        (expressionIso-compose (X.right-triangle y)
          (expressionIso-compose (compose-expression-cong first-comparison second-comparison)
            (expressionIso-inverse (retarget-composition first second b middle b))))
```
