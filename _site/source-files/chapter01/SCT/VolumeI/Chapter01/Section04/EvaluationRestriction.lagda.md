# Restriction of relative evaluation

Relative evaluation commutes with change of the term source through its
specified coordinates and their compatibility over the base. Equality of
complete evaluated images after this change reflects equality of mapping
identifications at an anima source.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.EvaluationRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; postWhisker-id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼; pair-pre; project-pair₁)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; cancel-left)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase using (change-parameter; reflect-second)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase
open import SCT.VolumeI.Chapter01.Section04.EvaluationCoherence using (evaluation⁼-reflect)
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
```
Changing the term source compares two evaluations through their common
coordinates. The first coordinate keeps the chosen projection comparison;
the second uses the actual uncurrying restriction. The following square is
natural in an arbitrary independent identification-family parameter.
The supplied compatibility over the base is reconstructed from the first
projection of those same routes. Composition and unit restriction remain
separate obligations for the default-choice comparison.

```agda
private
  module FixedSquares {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
      {l₁ : x =₁ x′} {r₁ : y =₁ y′} {l₂ : x′ =₁ x″} {r₂ : y′ =₁ y″}
      → SquareCell₌ t m (const l₁) (const r₁)
      → SquareCell₌ m b (const l₂) (const r₂)
      → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
    paste-fixed {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂} first second =
      replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁) (paste-square₌ first second)

    inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
    inverse-fixed {l = l} {r = r} square =
      replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ square)

module _ {Γ : Context} {P Q C D : CAT Γ} where
  open Terms.InContext P using (Term)
  private
    module ParameterChange (r : MAP Q P) where
      module Raw = EvaluationChange {C = C} {D = D} r
        using (source-change; target-change; common; input-normalization;
          output-normalization; input-route; output-route)
      open Raw public

      input-over : (x : Term (Map C D))
        → IdentificationOver {A = One {Γ}}
            (comp-over-map r (change-parameter r) (evaluation-over (x ∘ r)))
            (functor-over (common x) (pair-β₁ (r ∘ pr₁) (uncurry x ∘ source-change)))
      input-over x = identification-over (input-route x) (compatible-to-over compatibility)
        where
        R = FunctorOverBase.functor (evaluation-over (x ∘ r))
        v = uncurry (x ∘ r)
        first = post-triangle r pr₁ R (pair-β₁ pr₁ v)
        second = post-triangle (id D) pr₂ R (pair-β₂ pr₁ v)
        finish = uncurry-restrict x r ∙ comp-unitˡ v
        projection = project-pair₁ (r ∘ pr₁) (id D ∘ pr₂) R
        normalized = pair⁼ (id₌ (r ∘ pr₁) ∙ first) (finish ∙ second) ∙
          pair-pre (r ∘ pr₁) (id D ∘ pr₂) R
        normalization : input-route x =₂ normalized
        normalization = comp₌-cong ((pair⁼-comp (id₌ (r ∘ pr₁)) first finish second) ⁻¹) (id₌ _) ∙
          (comp₌-assoc (input-normalization x)
            (pair⁼ first second) (pair-pre (r ∘ pr₁) (id D ∘ pr₂) R)) ⁻¹
        compatibility : CompatibleOver pr₁
          (FunctorOverBase.cell (comp-over-map r (change-parameter r) (evaluation-over (x ∘ r))))
          (pair-β₁ (r ∘ pr₁) (uncurry x ∘ source-change)) (input-route x)
        compatibility = comp₌-assoc (r ◁ pair-β₁ pr₁ v) (comp-assoc R pr₁ r) projection ∙
          (comp₌-cong (comp₌-unitˡ-One first) (id₌ projection) ∙
            (pair-evaluation-over₁-One (r ∘ pr₁) (id D ∘ pr₂) R
              (id₌ (r ∘ pr₁) ∙ first) (finish ∙ second) ∙
              comp₌-cong (id₌ (pair-β₁ (r ∘ pr₁) (uncurry x ∘ source-change)))
                (postWhisker pr₁ ◁ normalization)))

      output-over : (x : Term (Map C D))
        → IdentificationOver {A = One {Γ}}
            (comp-over (evaluation-over x) (change-parameter r))
            (functor-over (common x) (pair-β₁ (r ∘ pr₁) (uncurry x ∘ source-change)))
      output-over x = identification-over (output-route x) (compatible-to-over
        (pair-evaluation-over₁-One pr₁ (uncurry x) source-change
          (pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)) (id₌ (uncurry x ∘ source-change))))

      module _ {X : CAT Γ} where
        open Terms.Equalities X using (_＝_)

        common⁼ : {x y : Term (Map C D)} → x ＝ y → common x ＝ common y
        common⁼ α = pair⁼ (const (id₌ (r ∘ pr₁))) (uncurry⁼ α ▷ source-change)

        input-route-natural : {x y : Term (Map C D)} (α : x ＝ y)
          → SquareCell₌ (target-change ◁ evaluation⁼ (α ▷ r)) (common⁼ α)
              (const (input-route x)) (const (input-route y))
        input-route-natural {x = x} {y = y} α =
          let uα = uncurry⁼ (α ▷ r)
              first-normalize = const-cong (postWhisker-id₌ r pr₁) ∙ post-constant r (id₌ pr₁)
              first = replace-edges₌ (first-normalize ⁻¹) (id₌ _)
                (identity-square₌ (const {P = X} (id₌ (r ∘ pr₁))))
              second = FixedSquares.paste-fixed (postWhisker-id uα) (uncurry-restrict-inputs α r)
              normalize = replace-sides₌
                (pair⁼-constant (id₌ (r ∘ pr₁)) (uncurry-restrict x r ∙ comp-unitˡ (uncurry (x ∘ r))))
                (pair⁼-constant (id₌ (r ∘ pr₁)) (uncurry-restrict y r ∙ comp-unitˡ (uncurry (y ∘ r))))
                (pair⁼-square first second)
          in FixedSquares.paste-fixed (productMap-pair-inner r (id D) (const (id₌ pr₁)) uα) normalize

        output-route-natural : {x y : Term (Map C D)} (α : x ＝ y)
          → SquareCell₌ (evaluation⁼ α ▷ source-change) (common⁼ α)
              (const (output-route x)) (const (output-route y))
        output-route-natural {x = x} {y = y} α =
          let b = pair-β₁ (r ∘ pr₁) (id C ∘ pr₂)
              uα = uncurry⁼ α ▷ source-change
              first-normalize = const-cong (preWhisker-id₌ pr₁ source-change) ∙ pre-constant (id₌ pr₁) source-change
              first = replace-edges₌ (first-normalize ⁻¹) (id₌ _)
                (transpose-square₌ (identity-square₌ (const {P = X} b)))
              normalize = replace-sides₌
                (pair⁼-constant b (id₌ (uncurry x ∘ source-change)))
                (pair⁼-constant b (id₌ (uncurry y ∘ source-change)))
                (pair⁼-square first (identity-square₌ uα))
          in FixedSquares.paste-fixed (pair-pre-natural-inputs (const (id₌ pr₁)) (uncurry⁼ α) source-change) normalize

  evaluation-restrict : (x : Term (Map C D)) (r : MAP Q P)
    → (productMap r (id D) ∘ FunctorOverBase.functor (evaluation-over (x ∘ r))) =₁
        (FunctorOverBase.functor (evaluation-over x) ∘ productMap r (id C))
  evaluation-restrict x r = (ParameterChange.output-route r x) ⁻¹ ∙ ParameterChange.input-route r x

  evaluation-restrict-over : (x : Term (Map C D)) (r : MAP Q P)
    → IdentificationOver {A = One {Γ}}
        (comp-over-map r (change-parameter r) (evaluation-over (x ∘ r)))
        (comp-over (evaluation-over x) (change-parameter r))
  evaluation-restrict-over x r = comp-identification-over
    (inverse-identification-over (ParameterChange.output-over r x)) (ParameterChange.input-over r x)

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    evaluation-restrict-natural : {x y : Term (Map C D)} (α : x ＝ y) (r : MAP Q P)
      → SquareCell₌ (productMap r (id D) ◁ evaluation⁼ (α ▷ r))
          (evaluation⁼ α ▷ productMap r (id C))
          (const (evaluation-restrict x r)) (const (evaluation-restrict y r))
    evaluation-restrict-natural α r = FixedSquares.paste-fixed (ParameterChange.input-route-natural r α)
      (FixedSquares.inverse-fixed (ParameterChange.output-route-natural r α))
```

A change of the base parameter reflects equality of evaluated
identifications that already preserve that parameter. Their first
projections agree by the supplied over-base squares; their second
projections are reflected by the unchanged second coordinate. Recovery
then gives a criterion for identifying a selected law with a recovered
one. The equality of the complete chosen route images is an explicit
premise of this criterion, still to be proved for the default laws.

```agda
module _ {Γ : Context} {X : CAT Γ} {P Q C D : CAT Γ} where
  open Terms.InContext Q using (Term)
  open Terms.Equalities X using (_＝_)

  evaluation⁼-reflect-change : (qAn : isAn Q) (r : MAP Q P)
    {x y : Term (Map C D)} (α β : x ＝ y)
    → (productMap r (id D) ◁ evaluation⁼ α) =₁ (productMap r (id D) ◁ evaluation⁼ β)
    → α =₁ β
  evaluation⁼-reflect-change qAn r {y = y} α β image = evaluation⁼-reflect qAn α β
    (pair₌-extensionality
      (cancel-left (const (FunctorOverBase.cell (evaluation-over y)))
        ((evaluation⁼-over β) ⁻¹ ∙ evaluation⁼-over α))
      (reflect-second r image))

  evaluation-recover-after-change : (qAn : isAn Q) (r : MAP Q P)
    {x y : Term (Map C D)} (α : x ＝ y)
    (given : IdentificationOver {A = X} (evaluation-over x) (evaluation-over y))
    → (productMap r (id D) ◁ evaluation⁼ α) =₁
        (productMap r (id D) ◁ IdentificationOver.identification given)
    → α =₁ evaluation-recover qAn given
  evaluation-recover-after-change qAn r α given image =
    evaluation⁼-reflect-change qAn r α (evaluation-recover qAn given)
      ((postWhisker (productMap r (id D)) ◁ (evaluation-recover-β qAn given) ⁻¹) ∙ image)
```
