# Evaluation over a parameter

A mapping term with source P evaluates to a functor over P between the
product-over objects. Its unit and composition comparisons are full
identifications over the base. Recovering a supplied relative identification
uses both its evaluation component and its compatibility with the parameter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.EvaluationOverBase where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-edges₌)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (FunctorOverBase; comp-over; id-over)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (IdentificationOver; identification-over; IsIdentificationOver;
    comp-identification-over; inverse-identification-over)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-triangle₂; pair₌-unique)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase
  using (product-over; second-projection; module OverFirstFactor)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Composition
open import SCT.VolumeI.Chapter01.Section04.CompositionEvaluation using (composition-evaluation)

module _ {Γ : Context} where
  -- The derived identity comparison restricts the representing beta directly.
  -- Its relative lift is the chosen evaluation-identity below.
  evaluation-over : {P C D : CAT Γ} → MAP P (Map C D)
    → FunctorOverBase (product-over P C) (product-over P D)
  evaluation-over {P} f = OverFirstFactor.pair-pr₁-over P (uncurry f)

  uncurry-compose : {P C D E : CAT Γ}
    (g : MAP P (Map D E)) (f : MAP P (Map C D))
    → uncurry (compose g f) =₁
        (uncurry g ∘ FunctorOverBase.functor (evaluation-over f))
  uncurry-compose g f = composition-evaluation g f

  uncurry-identity : (P C : CAT Γ) → uncurry (identity-map {P = P} C) =₁ pr₂
  uncurry-identity P C = second-projection (terminate P) ∙
    ((mapId-β C ▷ productMap (terminate P) (id C)) ∙ uncurry-restrict (mapId C) (terminate P))

  evaluation-compose : {P C D E : CAT Γ}
    (g : MAP P (Map D E)) (f : MAP P (Map C D))
    → IdentificationOver {A = One} (evaluation-over (compose g f))
        (comp-over (evaluation-over g) (evaluation-over f))
  evaluation-compose {P} g f =
    let open OverFirstFactor P
        middle = pair-pr₁-over (uncurry g ∘ pair-pr₁ (uncurry f))
        first : IdentificationOver {A = One} (evaluation-over (compose g f)) middle
        first = identification-over (pair-pr₁-cong-One (uncurry-compose g f))
          (pair-pr₁-cong-over-One (uncurry-compose g f))
        second : IdentificationOver {A = One}
          (comp-over (evaluation-over g) (evaluation-over f)) middle
        second = identification-over (pair-pr₁-compose (uncurry g) (uncurry f))
          (pair-pr₁-compose-over (uncurry g) (uncurry f))
    in comp-identification-over (inverse-identification-over second) first

  evaluation-identity : (P C : CAT Γ)
    → IdentificationOver {A = One} (evaluation-over (identity-map {P = P} C))
        (id-over (product-over P C))
  evaluation-identity P C =
    let open OverFirstFactor P
        first : IdentificationOver {A = One}
          (evaluation-over (identity-map {P = P} C)) (pair-pr₁-over pr₂)
        first = identification-over (pair-pr₁-cong-One (uncurry-identity P C))
          (pair-pr₁-cong-over-One (uncurry-identity P C))
        second : IdentificationOver {A = One} (pair-pr₁-over pr₂) (id-over (product-over P C))
        second = identification-over (pair-pr₁-id C) (pair-pr₁-id-over C)
    in comp-identification-over second first
```

The action below retains the literal constant identity in the parameter
coordinate and the accepted uncurry⁼ action in the evaluation coordinate.
Its family parameter X is independent of the source P of the mapping term.

```agda
module _ {Γ : Context} {P C D : CAT Γ} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    evaluation⁼ : {f g : MAP P (Map C D)}
      → f ＝ g
      → FunctorOverBase.functor (evaluation-over f) ＝
        FunctorOverBase.functor (evaluation-over g)
    evaluation⁼ α = OverFirstFactor.pair-pr₁-cong P (uncurry⁼ α)

    evaluation⁼-over : {f g : MAP P (Map C D)} (α : f ＝ g)
      → IsIdentificationOver (evaluation-over f) (evaluation-over g) (evaluation⁼ α)
    evaluation⁼-over α = OverFirstFactor.pair-pr₁-cong-over P (uncurry⁼ α)

    evaluation-identification : {f g : MAP P (Map C D)} (α : f ＝ g)
      → IdentificationOver {A = X} (evaluation-over f) (evaluation-over g)
    evaluation-identification α = identification-over (evaluation⁼ α) (evaluation⁼-over α)

    forget-evaluation : {f g : MAP P (Map C D)}
      → FunctorOverBase.functor (evaluation-over f) ＝
        FunctorOverBase.functor (evaluation-over g)
      → uncurry f ＝ uncurry g
    forget-evaluation {f} {g} α =
      (const (OverFirstFactor.pair-pr₁-β₂ P (uncurry g)) ∙ (pr₂ ◁ α)) ∙
        (const (OverFirstFactor.pair-pr₁-β₂ P (uncurry f))) ⁻¹

    forget-evaluation⁼ : {f g : MAP P (Map C D)} (α : f ＝ g)
      → forget-evaluation (evaluation⁼ α) =₁ uncurry⁼ α
    forget-evaluation⁼ {f} α =
      comp-inv-right (uncurry⁼ α) (const (OverFirstFactor.pair-pr₁-β₂ P (uncurry f))) ∙
        comp₌-cong (pair⁼-triangle₂ (const (id₌ pr₁)) (uncurry⁼ α))
          (id₌ ((const (OverFirstFactor.pair-pr₁-β₂ P (uncurry f))) ⁻¹))

    evaluation-recover : (pAn : isAn P) {f g : MAP P (Map C D)}
      → IdentificationOver {A = X} (evaluation-over f) (evaluation-over g)
      → f ＝ g
    evaluation-recover pAn {f} {g} α =
      uncurry-reflect pAn f g (forget-evaluation (IdentificationOver.identification α))

    evaluation-recover-β : (pAn : isAn P) {f g : MAP P (Map C D)}
      (α : IdentificationOver {A = X} (evaluation-over f) (evaluation-over g))
      → evaluation⁼ (evaluation-recover pAn α) =₁ IdentificationOver.identification α
    evaluation-recover-β pAn {f} {g} α =
      let given = IdentificationOver.identification α
          recovered = evaluation-recover pAn α
          image = evaluation⁼ recovered
          input = const (OverFirstFactor.pair-pr₁-β₂ P (uncurry f))
          output = const (OverFirstFactor.pair-pr₁-β₂ P (uncurry g))
          evaluated = forget-evaluation given
          image-second = replace-edges₌ (id₌ (pr₂ ◁ image))
            (uncurry-reflect-β pAn f g evaluated)
            (pair⁼-triangle₂ (const (id₌ pr₁)) (uncurry⁼ recovered))
          given-second = (inv-comp-right (output ∙ (pr₂ ◁ given)) input) ⁻¹
      in pair₌-unique {ε = image} {ε′ = given}
          (evaluation⁼-over recovered) image-second (IdentificationOver.over α) given-second
```

The recovery image law is an equality of the supplied underlying
identification families. It does not identify the proof fields of two
IdentificationOver records. Its first projection uses the supplied over-base
square; a second-projection calculation alone would not establish this law.
