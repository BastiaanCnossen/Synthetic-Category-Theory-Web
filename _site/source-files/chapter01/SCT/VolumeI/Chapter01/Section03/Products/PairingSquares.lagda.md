# Paired evaluations along restriction diagrams

An equation between two identifications into a product follows from the
corresponding equations between their coordinates, once both sides are
recognized as lying over those coordinates (`pair₌-unique`). This module
records the two applications used by later calculations.

1. Pairing evaluations along a restriction diagram
   (Identifications.RestrictionDiagrams). Two evaluations of `b` and `c`
   along the same diagram pair to an evaluation of `pair b c`, whose steps
   are the paired evaluations of the coordinate steps. Its direct and staged
   routes lie over the coordinate routes, so the paired evaluation is
   compatible when the coordinate evaluations are (`pair-compatible`). The
   individual instance pairs with the restrictions `pair-pre` themselves.
2. Restricting a paired evaluation along a further functor, a direct
   computation from the naturality of `pair-pre` (`PairingBaseChange`).

A change of coordinate frames, formerly an assembly of its own, is the
naturality of paired evaluation in its inputs
(`PairingRestriction.pair-evaluation-natural-inputs`).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.PairingSquares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
```

## Combining paired composites

```agda
module _ {Γ : Context} where
  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    combine-pair : {A B : CAT Γ} {a₀ a₁ a₂ : Term A} {b₀ b₁ b₂ : Term B}
      {source : Term (A × B)}
      (α : a₁ ＝ a₂) (β : b₁ ＝ b₂)
      (γ : a₀ ＝ a₁) (δ : b₀ ＝ b₁)
      (base : (source ＝ (pair a₀ b₀)))
      → (pair⁼ α β ∙ (pair⁼ γ δ ∙ base)) =₁ (pair⁼ (α ∙ γ) (β ∙ δ) ∙ base)
    combine-pair α β γ δ base =
      comp₌-cong ((pair⁼-comp α γ β δ) ⁻¹) (id₌ base) ∙
        (comp₌-assoc (pair⁼ α β) (pair⁼ γ δ) base) ⁻¹
```

## Pairing evaluations

For a restriction diagram `ρ` with `δ : r ∘ t = s` and evaluations `e₁` of
`b` and `e₂` of `c` along it, the paired evaluation of `pair b c` evaluates
directly by `pair⁼ a d ∙ pair-pre b c s`, in stages by the paired
evaluations along `r` and `t`, and finishes by `pair⁼ η θ`. Its direct route
lies over the two coordinate direct routes along the restricted projection
laws, and likewise its staged route; this is the calculus of Triangles
applied to the projection triangles of PairingRestriction.

```agda
module _ {Γ : Context} {E Q : CAT Γ} where
  open Terms.InContext Q using (Term)
  open Terms.Equalities E using (_＝_)

  module _ {R X : CAT Γ} (ρ : RestrictionDiagram {E = E} {Q = Q} R X) where
    open RestrictionDiagram ρ
    open Evaluation

    pair-evaluations : {A B : CAT Γ} {b : MAP X A} {c : MAP X B}
      {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : Term A} {c₂ c₃ : Term B}
      → Evaluation ρ b b₁ b₂ b₃ → Evaluation ρ c c₁ c₂ c₃
      → Evaluation ρ (pair b c) (pair b₁ c₁) (pair b₂ c₂) (pair b₃ c₃)
    pair-evaluations {b = b} {c} {b₁} {c₁} e₁ e₂ = evaluation
      (pair⁼ (direct e₁) (direct e₂) ∙ const (pair-pre b c composite))
      (pair⁼ (first-stage e₁) (first-stage e₂) ∙ const (pair-pre b c outer))
      (pair⁼ (second-stage e₁) (second-stage e₂) ∙ const (pair-pre b₁ c₁ inner))
      (pair⁼ (finish e₁) (finish e₂))

    module _ {A B : CAT Γ} {b : MAP X A} {c : MAP X B}
      {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : Term A} {c₂ c₃ : Term B}
      (e₁ : Evaluation ρ b b₁ b₂ b₃) (e₂ : Evaluation ρ c c₁ c₂ c₃) where

      direct-route-over₁ : SquareCell₌ (pr₁ ◁ direct-route (pair-evaluations e₁ e₂))
        (direct-route e₁)
        (const (restrict-triangle pr₁ (pair b c ∘ outer) (project-pair₁ b c outer) inner))
        (const (pair-β₁ b₃ c₃))
      direct-route-over₁ = lies-over-comp pr₁
        (lies-over-comp pr₁
          (replace-edges₌ ((post-constant pr₁ (comp-assoc inner outer (pair b c))) ⁻¹) (id₌ _)
            (constant-square₌ (restrict-triangle-assoc pr₁ (pair b c) (pair-β₁ b c) outer inner)))
          (restrict-change-square pr₁ (pair b c) b (pair-β₁ b c) commutes))
        (pair-evaluation-over₁ b c composite (direct e₁) (direct e₂))

      direct-route-over₂ : SquareCell₌ (pr₂ ◁ direct-route (pair-evaluations e₁ e₂))
        (direct-route e₂)
        (const (restrict-triangle pr₂ (pair b c ∘ outer) (project-pair₂ b c outer) inner))
        (const (pair-β₂ b₃ c₃))
      direct-route-over₂ = lies-over-comp pr₂
        (lies-over-comp pr₂
          (replace-edges₌ ((post-constant pr₂ (comp-assoc inner outer (pair b c))) ⁻¹) (id₌ _)
            (constant-square₌ (restrict-triangle-assoc pr₂ (pair b c) (pair-β₂ b c) outer inner)))
          (restrict-change-square pr₂ (pair b c) c (pair-β₂ b c) commutes))
        (pair-evaluation-over₂ b c composite (direct e₁) (direct e₂))

      staged-route-over₁ : SquareCell₌ (pr₁ ◁ staged-route (pair-evaluations e₁ e₂))
        (staged-route e₁)
        (const (restrict-triangle pr₁ (pair b c ∘ outer) (project-pair₁ b c outer) inner))
        (const (pair-β₁ b₃ c₃))
      staged-route-over₁ = lies-over-comp pr₁
        (lies-over-comp pr₁
          (restrict-square pr₁ (first-stage (pair-evaluations e₁ e₂)) (first-stage e₁)
            (project-pair₁ b c outer) (pair-β₁ b₁ c₁) inner
            (pair-evaluation-over₁ b c outer (first-stage e₁) (first-stage e₂)))
          (pair-evaluation-over₁ b₁ c₁ inner (second-stage e₁) (second-stage e₂)))
        (pair⁼-triangle₁ (finish e₁) (finish e₂))

      staged-route-over₂ : SquareCell₌ (pr₂ ◁ staged-route (pair-evaluations e₁ e₂))
        (staged-route e₂)
        (const (restrict-triangle pr₂ (pair b c ∘ outer) (project-pair₂ b c outer) inner))
        (const (pair-β₂ b₃ c₃))
      staged-route-over₂ = lies-over-comp pr₂
        (lies-over-comp pr₂
          (restrict-square pr₂ (first-stage (pair-evaluations e₁ e₂)) (first-stage e₂)
            (project-pair₂ b c outer) (pair-β₂ b₁ c₁) inner
            (pair-evaluation-over₂ b c outer (first-stage e₁) (first-stage e₂)))
          (pair-evaluation-over₂ b₁ c₁ inner (second-stage e₁) (second-stage e₂)))
        (pair⁼-triangle₂ (finish e₁) (finish e₂))

      pair-compatible : Compatible ρ e₁ → Compatible ρ e₂
        → Compatible ρ (pair-evaluations e₁ e₂)
      pair-compatible first-compatible second-compatible = pair₌-unique
        direct-route-over₁ direct-route-over₂
        (replace-edges₌ (id₌ _) (first-compatible ⁻¹) staged-route-over₁)
        (replace-edges₌ (id₌ _) (second-compatible ⁻¹) staged-route-over₂)
```

At `E = One` the paired evaluation can use `pair-pre` itself. Its steps are
those of the family construction up to `const-One`, so its compatibility is
transported from `pair-compatible`.

```agda
module _ {Γ : Context} {Q R X : CAT Γ} (ρ : RestrictionDiagram {E = One} {Q = Q} R X) where
  open Terms.InContext Q using (Term)
  open RestrictionDiagram ρ
  open Evaluation

  pair-evaluations-One : {A B : CAT Γ} {b : MAP X A} {c : MAP X B}
    {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : Term A} {c₂ c₃ : Term B}
    → Evaluation ρ b b₁ b₂ b₃ → Evaluation ρ c c₁ c₂ c₃
    → Evaluation ρ (pair b c) (pair b₁ c₁) (pair b₂ c₂) (pair b₃ c₃)
  pair-evaluations-One {b = b} {c} {b₁} {c₁} e₁ e₂ = evaluation
    (pair⁼ (direct e₁) (direct e₂) ∙ pair-pre b c composite)
    (pair⁼ (first-stage e₁) (first-stage e₂) ∙ pair-pre b c outer)
    (pair⁼ (second-stage e₁) (second-stage e₂) ∙ pair-pre b₁ c₁ inner)
    (pair⁼ (finish e₁) (finish e₂))

  pair-compatible-One : {A B : CAT Γ} {b : MAP X A} {c : MAP X B}
    {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : Term A} {c₂ c₃ : Term B}
    (e₁ : Evaluation ρ b b₁ b₂ b₃) (e₂ : Evaluation ρ c c₁ c₂ c₃)
    → Compatible-One ρ e₁ → Compatible-One ρ e₂
    → Compatible-One ρ (pair-evaluations-One e₁ e₂)
  pair-compatible-One {b = b} {c} {b₁} {c₁} e₁ e₂ first-compatible second-compatible =
    compatible-One ρ {e = pair-evaluations-One e₁ e₂}
      (compatible-replace ρ {e = pair-evaluations ρ e₁ e₂} {e′ = pair-evaluations-One e₁ e₂}
        (comp₌-cong (id₌ (pair⁼ (direct e₁) (direct e₂))) (const-One (pair-pre b c composite)))
        (comp₌-cong (id₌ (pair⁼ (first-stage e₁) (first-stage e₂)))
          (const-One (pair-pre b c outer)))
        (comp₌-cong (id₌ (pair⁼ (second-stage e₁) (second-stage e₂)))
          (const-One (pair-pre b₁ c₁ inner)))
        (id₌ (pair⁼ (finish e₁) (finish e₂)))
        (pair-compatible ρ e₁ e₂ (compatible-from-One ρ first-compatible)
          (compatible-from-One ρ second-compatible)))
```

## Restricting a paired evaluation

Restricting the paired evaluation `pair⁼ α β ∙ pair-pre u v p` along `q`,
and reassociating, agrees with the paired evaluation along `p ∘ q` of the
given coordinate restrictions `δ₀`, `δ₁`.

```agda
module _ {Γ : Context} where
  module _ {E : CAT Γ} where
    open Terms.Equalities E using (_＝_)

    module PairingBaseChange {B C D X Y : CAT Γ} (u : MAP D X) (v : MAP D Y)
      (p : MAP C D) (q : MAP B C) {u′ : MAP C X} {v′ : MAP C Y}
      (α : (u ∘ p) ＝ u′) (β : (v ∘ p) ＝ v′)
      (δ₀ : (u ∘ (p ∘ q)) ＝ (u′ ∘ q))
      (δ₁ : (v ∘ (p ∘ q)) ＝ (v′ ∘ q))
      (source-square : (δ₀ ∙ const {P = E} (comp-assoc q p u)) =₁ (α ▷ q))
      (target-square : (δ₁ ∙ const {P = E} (comp-assoc q p v)) =₁ (β ▷ q)) where

      pair⁼-identification : (pair u v ∘ p) ＝ pair u′ v′
      pair⁼-identification = pair⁼ α β ∙ const {P = E} (pair-pre u v p)

      restricted-identification : (pair u v ∘ (p ∘ q)) ＝ (pair u′ v′ ∘ q)
      restricted-identification =
        (pair⁼-identification ▷ q) ∙ (const {P = E} (comp-assoc q p (pair u v))) ⁻¹

      private
        A = const {P = E} (comp-assoc q p (pair u v))
        A₀ = const {P = E} (comp-assoc q p u)
        A₁ = const {P = E} (comp-assoc q p v)
        P₀ = const {P = E} (pair-pre u v p) ▷ q
        P₁ = const {P = E} (pair-pre (u ∘ p) (v ∘ p) q)
        P₂ = const {P = E} (pair-pre u v (p ∘ q))
        P′ = const {P = E} (pair-pre u′ v′ q)
        Δ = pair⁼ δ₀ δ₁
        Γ′ = pair⁼ (α ▷ q) (β ▷ q)
        restricted = pair⁼-identification ▷ q

        abstract
          constant-iteration : (P₂ ∙ A) =₁ (pair⁼ A₀ A₁ ∙ (P₁ ∙ P₀))
          constant-iteration =
            (const-comp (pair⁼ (comp-assoc q p u) (comp-assoc q p v))
              (pair-pre (u ∘ p) (v ∘ p) q ∙ (pair-pre u v p ▷ q)) ∙
            comp₌-cong (pair⁼-constant (comp-assoc q p u) (comp-assoc q p v))
              (const-comp (pair-pre (u ∘ p) (v ∘ p) q) (pair-pre u v p ▷ q) ∙
                comp₌-cong (id₌ P₁) (pre-constant (pair-pre u v p) q))) ⁻¹ ∙
              (const-cong (pair-pre-iterated u v p q) ∙
                const-comp (pair-pre u v (p ∘ q)) (comp-assoc q p (pair u v)))

        abstract
          component-computation : (Δ ∙ pair⁼ A₀ A₁) =₁ Γ′
          component-computation = pair⁼-cong source-square target-square ∙
            (pair⁼-comp δ₀ A₀ δ₁ A₁) ⁻¹

          right-computation : ((Δ ∙ P₂) ∙ A) =₁ (P′ ∙ restricted)
          right-computation = comp₌-cong (id₌ P′)
              ((preWhisker-comp₌ (pair⁼ α β) (const {P = E} (pair-pre u v p)) q) ⁻¹) ∙
            (comp₌-assoc P′ (pair⁼ α β ▷ q) P₀ ∙
            (comp₌-cong ((pair-pre-natural-inputs α β q) ⁻¹) (id₌ P₀) ∙
            ((comp₌-assoc Γ′ P₁ P₀) ⁻¹ ∙
            (comp₌-cong component-computation (id₌ (P₁ ∙ P₀)) ∙
            ((comp₌-assoc Δ (pair⁼ A₀ A₁) (P₁ ∙ P₀)) ⁻¹ ∙
            (comp₌-cong (id₌ Δ) constant-iteration ∙
              comp₌-assoc Δ P₂ A))))))

          left-computation : ((P′ ∙ restricted-identification) ∙ A) =₁ (P′ ∙ restricted)
          left-computation = comp₌-cong (id₌ P′) (inv-comp-right restricted A) ∙
            comp₌-assoc P′ (restricted ∙ A ⁻¹) A

      abstract
        restriction-square : (P′ ∙ restricted-identification) =₁ (Δ ∙ P₂)
        restriction-square = cancel-right A (right-computation ⁻¹ ∙ left-computation)
```
