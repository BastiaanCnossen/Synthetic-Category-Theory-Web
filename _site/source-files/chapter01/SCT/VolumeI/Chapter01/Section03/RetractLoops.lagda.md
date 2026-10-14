# Retracts and the loop formulation

The first rebuild recorded a retract by its two squares, endpoint laws
`α : id C =₁ h ∘ g` and `β : j ∘ k =₁ id D`, and a compatibility
`id₌ f =₂ loop`, where `loop : f =₁ f` runs around the pasted diagram. The
new interface records the endpoint laws in the opposite domain orientation
as the sides of a `SquareEquality`, whose compatibility compares the pasted
cell with the cell of the identity square. The adapters below convert either
compatibility into the other, for fixed squares, with the domain law
inverted explicitly. They construct the stated data; they do not claim that
the two conversions are mutually inverse on higher data.

Write `λ = comp-unitˡ f`, `ρ = comp-unitʳ f` and `c` for the cell of the
pasted square. The old loop is the right-nested composite

    λ ∙ ((β ▷ f) ∙ (a₁ ∙ (b₁ ∙ (c₁ ∙ (d₁ ∙ (e₁ ∙ ((f ◁ α) ∙ ρ ⁻¹)))))))

where `c = a₁ ∙ (b₁ ∙ (c₁ ∙ (d₁ ∙ e₁)))` are the five factors of the pasted
cell. After reassociating it is `λ ∙ ((β ▷ f) ∙ (c ∙ ((f ◁ α) ∙ ρ ⁻¹)))`.
Both adapters then use only the vertical calculus, preservation of vertical
composites and identities by whiskering, and `const-One` for the final
identity identification.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.RetractLoops where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; module Composition)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp₌-unitˡ; comp₌-unitʳ; comp₌-inverseˡ; comp₌-inverseʳ;
    inv-comp-left; comp-inv-right; postWhisker-comp₌; post-constant; const-cong; const-One)
open import SCT.VolumeI.Chapter01.Section03.Squares
open import SCT.VolumeI.Chapter01.Section03.Retracts using (Retract)
open Operations
open Composition
```

```agda
module LoopCompatibility {Γ : Context} {C D C′ D′ : CAT Γ}
  {f : MAP C D} {f′ : MAP C′ D′}
  (inclusion : Square f f′) (retraction : Square f′ f) where

  private
    g = Square.source-map inclusion
    k = Square.target-map inclusion
    h = Square.source-map retraction
    j = Square.target-map retraction
    λf = comp-unitˡ f
    ρf = comp-unitʳ f

    a₁ : (j ∘ (k ∘ f)) =₁ ((j ∘ k) ∘ f)
    a₁ = (comp-assoc f k j) ⁻¹
    b₁ : (j ∘ (f′ ∘ g)) =₁ (j ∘ (k ∘ f))
    b₁ = j ◁ Square.cell inclusion
    c₁ : ((j ∘ f′) ∘ g) =₁ (j ∘ (f′ ∘ g))
    c₁ = comp-assoc g f′ j
    d₁ : ((f ∘ h) ∘ g) =₁ ((j ∘ f′) ∘ g)
    d₁ = Square.cell retraction ▷ g
    e₁ : (f ∘ (h ∘ g)) =₁ ((f ∘ h) ∘ g)
    e₁ = (comp-assoc g h f) ⁻¹

    pasted : (f ∘ (h ∘ g)) =₁ ((j ∘ k) ∘ f)
    pasted = Square.cell (comp-square retraction inclusion)

    identity-cell : (f ∘ id C) =₁ (id D ∘ f)
    identity-cell = Square.cell (id-square f)

    nested : (f =₁ (f ∘ (h ∘ g))) → f =₁ ((j ∘ k) ∘ f)
    nested T = a₁ ∙ (b₁ ∙ (c₁ ∙ (d₁ ∙ (e₁ ∙ T))))

    reassociate : (T : f =₁ (f ∘ (h ∘ g))) → (pasted ∙ T) =₂ nested T
    reassociate T =
      comp₌-cong (id₌ a₁)
        (comp₌-cong (id₌ b₁)
          (comp₌-cong (id₌ c₁) (comp₌-assoc d₁ e₁ T) ∙
            comp₌-assoc c₁ (d₁ ∙ e₁) T) ∙
          comp₌-assoc b₁ (c₁ ∙ (d₁ ∙ e₁)) T) ∙
        comp₌-assoc a₁ (b₁ ∙ (c₁ ∙ (d₁ ∙ e₁))) T

    T-from : id C =₁ (h ∘ g) → f =₁ (f ∘ (h ∘ g))
    T-from α = (f ◁ α) ∙ ρf ⁻¹

    cancel-whiskered : (p : (h ∘ g) =₁ id C) (q : id C =₁ (h ∘ g))
      → (p ∙ q) =₂ const (id₌ (id C))
      → ((f ◁ p) ∙ ((f ◁ q) ∙ ρf ⁻¹)) =₂ ρf ⁻¹
    cancel-whiskered p q e =
      comp₌-unitˡ (ρf ⁻¹) ∙
        (comp₌-cong
          (const-cong (postWhisker-id₌ f (id C)) ∙
            (post-constant f (id₌ (id C)) ∙
              ((postWhisker f ◁ e) ∙ (postWhisker-comp₌ f p q) ⁻¹)))
          (id₌ (ρf ⁻¹)) ∙
          (comp₌-assoc (f ◁ p) (f ◁ q) (ρf ⁻¹)) ⁻¹)

  loop : id C =₁ (h ∘ g) → (j ∘ k) =₁ id D → f =₁ f
  loop α β = λf ∙ ((β ▷ f) ∙ nested (T-from α))
```

From a `SquareEquality` with sides `s` and `t`, take `α = s ⁻¹` and `β = t`.
Reassociate the loop, replace `(t ▷ f) ∙ c` by `(λ ⁻¹ ∙ ρ) ∙ (f ◁ s)`
using the compatibility, cancel `f ◁ s` against `f ◁ s ⁻¹`, and then cancel
the unitors.

```agda
  square-equality-to-loop
    : (E : SquareEquality (comp-square retraction inclusion) (id-square f))
    → id₌ f =₂ loop ((SquareEquality.source-identification E) ⁻¹)
                    (SquareEquality.target-identification E)
  square-equality-to-loop E =
    let s = SquareEquality.source-identification E
        t = SquareEquality.target-identification E
        T = T-from (s ⁻¹)
        to-unitor : ((t ▷ f) ∙ nested T) =₂ λf ⁻¹
        to-unitor = comp-inv-right (λf ⁻¹) ρf ∙
          (comp₌-cong (id₌ identity-cell) (cancel-whiskered s (s ⁻¹) (comp₌-inverseʳ s)) ∙
            (comp₌-assoc identity-cell (f ◁ s) T ∙
              (comp₌-cong (SquareEquality.compatibility E) (id₌ T) ∙
                ((comp₌-assoc (t ▷ f) pasted T) ⁻¹ ∙
                  comp₌-cong (id₌ (t ▷ f)) ((reassociate T) ⁻¹)))))
        to-identity : loop (s ⁻¹) t =₂ id₌ f
        to-identity = const-One (id₌ f) ∙
          (comp₌-inverseʳ λf ∙ comp₌-cong (id₌ λf) to-unitor)
    in to-identity ⁻¹
```

Conversely, from `κ : id₌ f =₂ loop α β` take the sides `α ⁻¹` and `β`.
Write `P = (β ▷ f) ∙ c`, `Q = (λ ⁻¹ ∙ ρ) ∙ (f ◁ α ⁻¹)` and
`T = (f ◁ α) ∙ ρ ⁻¹`. The loop law gives `P ∙ T =₂ λ ⁻¹` after cancelling
`λ`; cancelling `f ◁ α ⁻¹` against `f ◁ α` gives `Q ∙ T =₂ λ ⁻¹`. Cancelling
`T` on the right identifies `P` with `Q`, the required compatibility.

```agda
  loop-to-square-equality : (α : id C =₁ (h ∘ g)) (β : (j ∘ k) =₁ id D)
    → id₌ f =₂ loop α β
    → SquareEquality (comp-square retraction inclusion) (id-square f)
  loop-to-square-equality α β κ =
    let P = (β ▷ f) ∙ pasted
        Q = identity-cell ∙ (f ◁ α ⁻¹)
        T = T-from α
        loop-reduced : (λf ∙ (P ∙ T)) =₂ id₌ f
        loop-reduced = κ ⁻¹ ∙
          comp₌-cong (id₌ λf)
            (comp₌-cong (id₌ (β ▷ f)) (reassociate T) ∙ comp₌-assoc (β ▷ f) pasted T)
        P-T : (P ∙ T) =₂ λf ⁻¹
        P-T = comp₌-unitʳ (λf ⁻¹) ∙
          (comp₌-cong (id₌ (λf ⁻¹)) ((const-One (id₌ f)) ⁻¹) ∙
            (comp₌-cong (id₌ (λf ⁻¹)) loop-reduced ∙ (inv-comp-left λf (P ∙ T)) ⁻¹))
        Q-T : (Q ∙ T) =₂ λf ⁻¹
        Q-T = comp-inv-right (λf ⁻¹) ρf ∙
          (comp₌-cong (id₌ identity-cell) (cancel-whiskered (α ⁻¹) α (comp₌-inverseˡ α)) ∙
            comp₌-assoc identity-cell (f ◁ α ⁻¹) T)
    in record
      { source-identification = α ⁻¹
      ; target-identification = β
      ; compatibility = comp-inv-right Q T ∙
          (comp₌-cong ((Q-T) ⁻¹ ∙ P-T) (id₌ (T ⁻¹)) ∙ (comp-inv-right P T) ⁻¹)
      }
```

For a retract, the first adapter gives the loop compatibility of its data;
the second builds a retract from data with a loop compatibility.

```agda
module _ {Γ : Context} {C D C′ D′ : CAT Γ} {f : MAP C D} {f′ : MAP C′ D′} where
  retract-loop-compatibility : (R : Retract f f′)
    → let open Retract R
          E = retraction-law
      in id₌ f =₂ LoopCompatibility.loop map retraction
           ((SquareEquality.source-identification E) ⁻¹)
           (SquareEquality.target-identification E)
  retract-loop-compatibility R =
    LoopCompatibility.square-equality-to-loop (Retract.map R) (Retract.retraction R)
      (Retract.retraction-law R)

  retract-from-loop : (inclusion : Square f f′) (retraction : Square f′ f)
    → (α : id C =₁ (Square.source-map retraction ∘ Square.source-map inclusion))
    → (β : (Square.target-map retraction ∘ Square.target-map inclusion) =₁ id D)
    → id₌ f =₂ LoopCompatibility.loop inclusion retraction α β
    → Retract f f′
  retract-from-loop inclusion retraction α β κ = record
    { map = inclusion
    ; retraction = retraction
    ; retraction-law = LoopCompatibility.loop-to-square-equality inclusion retraction α β κ
    }
```
