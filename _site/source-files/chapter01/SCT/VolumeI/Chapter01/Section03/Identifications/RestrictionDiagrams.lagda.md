# Restriction diagrams and staged evaluation

A restriction diagram consists of functors `r : R → X`, `t : Q → R`,
`s : Q → X` and an identification `δ : r ∘ t = s`: restricting along `r`
and then `t` is identified with restricting along `s`. An evaluation of a
functor `b : X → A` along such a diagram evaluates its restriction in two
ways: directly, by `direct : b ∘ s = b₃`, and in stages, by
`first-stage : b ∘ r = b₁`, `second-stage : b₁ ∘ t = b₂` and a final
`finish : b₂ = b₃`. Both give an identification `(b ∘ r) ∘ t = b₃`:

    direct-route = direct ∙ ((b ◁ δ) ∙ comp-assoc t r b)
    staged-route = finish ∙ (second-stage ∙ (first-stage ▷ t))

and the evaluation is compatible when the two routes are identified.
Compatible evaluations are closed under pairing
(`Products.PairingSquares.pair-compatible`), postcomposition with a functor
(`post-compatible` below) and therefore under binary functors
(`Products.BinaryFunctors.binary-compatible`). An assembly of paired or
binary routes is the compatibility of the corresponding evaluation.

The diagram and the evaluations are identification families with a common
parameter `E`; the fixed associator enters as a constant family. At `E = One`
the compatibility is also stated with the associator itself
(`Compatible-One`); the two forms differ by `const-One`. Replacing the four
identifications of an evaluation by identified ones preserves compatibility
(`compatible-replace`). The fields of a diagram are `outer = r`,
`inner = t`, `composite = s` and `commutes = δ`. Constructions that exist
only for individual identifications, such as `post-evaluation`, carry no
`-One` suffix; the suffix marks an individual instance of a family statement
with the same stem.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-changed-restriction)
```

## Restriction diagrams and evaluations

```agda
module _ {Γ : Context} {E Q : CAT Γ} where
  open Terms.InContext Q using (Term)
  open Terms.Equalities E using (_＝_)

  record RestrictionDiagram (R X : CAT Γ) : Set m where
    constructor restriction-diagram
    field
      outer : MAP R X
      inner : Term R
      composite : Term X
      commutes : (outer ∘ inner) ＝ composite

  module _ {R X : CAT Γ} (ρ : RestrictionDiagram R X) where
    open RestrictionDiagram ρ

    restriction-route : {A : CAT Γ} (b : MAP X A)
      → ((b ∘ outer) ∘ inner) ＝ (b ∘ composite)
    restriction-route b = (b ◁ commutes) ∙ const (comp-assoc inner outer b)

    record Evaluation {A : CAT Γ} (b : MAP X A) (b₁ : MAP R A) (b₂ b₃ : Term A) : Set m where
      constructor evaluation
      field
        direct : (b ∘ composite) ＝ b₃
        first-stage : (b ∘ outer) ＝ b₁
        second-stage : (b₁ ∘ inner) ＝ b₂
        finish : b₂ ＝ b₃

      direct-route : ((b ∘ outer) ∘ inner) ＝ b₃
      direct-route = direct ∙ restriction-route b

      staged-route : ((b ∘ outer) ∘ inner) ＝ b₃
      staged-route = finish ∙ (second-stage ∙ (first-stage ▷ inner))

    Compatible : {A : CAT Γ} {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
      → Evaluation b b₁ b₂ b₃ → Set m
    Compatible e = Evaluation.direct-route e =₁ Evaluation.staged-route e

    compatible-replace : {A : CAT Γ} {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
      {e e′ : Evaluation b b₁ b₂ b₃}
      → Evaluation.direct e =₁ Evaluation.direct e′
      → Evaluation.first-stage e =₁ Evaluation.first-stage e′
      → Evaluation.second-stage e =₁ Evaluation.second-stage e′
      → Evaluation.finish e =₁ Evaluation.finish e′
      → Compatible e → Compatible e′
    compatible-replace {b = b} direct first-stage second-stage finish compatible =
      comp₌-cong finish (comp₌-cong second-stage (preWhisker inner ◁ first-stage)) ∙
        (compatible ∙ (comp₌-cong direct (id₌ (restriction-route b))) ⁻¹)
```

## Individual evaluations

At `E = One` the restriction route can use the associator itself.

```agda
module _ {Γ : Context} {Q R X : CAT Γ} (ρ : RestrictionDiagram {E = One} {Q = Q} R X) where
  open Terms.InContext Q using (Term)
  open RestrictionDiagram ρ
  open Evaluation

  restriction-route-One : {A : CAT Γ} (b : MAP X A)
    → ((b ∘ outer) ∘ inner) =₁ (b ∘ composite)
  restriction-route-One b = (b ◁ commutes) ∙ comp-assoc inner outer b

  Compatible-One : {A : CAT Γ} {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
    → Evaluation ρ b b₁ b₂ b₃ → Set m
  Compatible-One {b = b} e = (direct e ∙ restriction-route-One b) =₂ staged-route e

  private
    route-const-One : {A : CAT Γ} (b : MAP X A)
      → restriction-route ρ b =₂ restriction-route-One b
    route-const-One b = comp₌-cong (id₌ (b ◁ commutes)) (const-One (comp-assoc inner outer b))

  compatible-One : {A : CAT Γ} {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
    {e : Evaluation ρ b b₁ b₂ b₃} → Compatible ρ e → Compatible-One e
  compatible-One {b = b} {e = e} compatible =
    compatible ∙ comp₌-cong (id₌ (direct e)) ((route-const-One b) ⁻¹)

  compatible-from-One : {A : CAT Γ} {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
    {e : Evaluation ρ b b₁ b₂ b₃} → Compatible-One e → Compatible ρ e
  compatible-from-One {b = b} {e = e} compatible =
    compatible ∙ comp₌-cong (id₌ (direct e)) (route-const-One b)
```

## Postcomposition

Postcomposing every step of an individual evaluation with `F`, and
reassociating, gives an evaluation of `F ∘ b`. It is compatible when the
given evaluation is; this is `post-changed-restriction` of
TriangleCoherence.

```agda
  post-evaluation : {A B : CAT Γ} (F : MAP A B)
    {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A}
    → Evaluation ρ b b₁ b₂ b₃ → Evaluation ρ (F ∘ b) (F ∘ b₁) (F ∘ b₂) (F ∘ b₃)
  post-evaluation F {b} {b₁} e = evaluation
    (post-triangle F b composite (direct e))
    (post-triangle F b outer (first-stage e))
    (post-triangle F b₁ inner (second-stage e))
    (F ◁ finish e)

  post-compatible : {A B : CAT Γ} (F : MAP A B)
    {b : MAP X A} {b₁ : MAP R A} {b₂ b₃ : Term A} (e : Evaluation ρ b b₁ b₂ b₃)
    → Compatible-One e → Compatible-One (post-evaluation F e)
  post-compatible F {b} e compatible =
    post-changed-restriction F b outer inner composite commutes
      (first-stage e) (second-stage e) (direct e) (finish e) compatible
```
