# Binary functors

A functor `F : A × B → C` applied to two functors with a common source is
`binary-apply F f x = F ∘ pair f x`. Postcomposing pairing with `F` gives its
action `binary-cong` on identification families and its restriction
comparison `binary-pre`, the postcomposed triangle of `pair-pre`. Each law of
pairing and restriction gives a law of the binary action by postcomposition.
Evaluation of mapping animae in Section04 is an instance.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-comp; whisker-mixed)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-iterated-restriction)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-evaluations-One; pair-compatible-One)
```

## The binary action

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-apply : {A B C : CAT Γ} → MAP (A × B) C → Term A → Term B → Term C
    binary-apply F f x = F ∘ pair f x

  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    binary-cong : {A B C : CAT Γ} (F : MAP (A × B) C)
      {f g : Term A} {x y : Term B}
      → (f ＝ g) → (x ＝ y) → ((binary-apply F f x) ＝ (binary-apply F g y))
    binary-cong F α β = F ◁ pair⁼ α β

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-pre : {Y A B C : CAT Γ} (F : MAP (A × B) C)
      (f : Term A) (x : Term B) (r : MAP Y X)
      → (binary-apply F f x ∘ r) =₁ binary-apply F (f ∘ r) (x ∘ r)
    binary-pre F f x r = post-triangle F (pair f x) r (pair-pre f x r)

  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    binary-cong-comp : {A B C : CAT Γ} (F : MAP (A × B) C)
      {f₀ f₁ f₂ : Term A} {x₀ x₁ x₂ : Term B}
      (α₂ : f₁ ＝ f₂) (α₁ : f₀ ＝ f₁)
      (β₂ : x₁ ＝ x₂) (β₁ : x₀ ＝ x₁)
      → binary-cong F (α₂ ∙ α₁) (β₂ ∙ β₁) =₁ (binary-cong F α₂ β₂ ∙ binary-cong F α₁ β₁)
    binary-cong-comp F α₂ α₁ β₂ β₁ =
      postWhisker-comp₌ F (pair⁼ α₂ β₂) (pair⁼ α₁ β₁) ∙
        (postWhisker F ◁ pair⁼-comp α₂ α₁ β₂ β₁)

    binary-cong₂ : {A B C : CAT Γ} (F : MAP (A × B) C)
      {f f′ : Term A} {x x′ : Term B}
      {α α′ : f ＝ f′} {β β′ : x ＝ x′}
      → α =₁ α′ → β =₁ β′ → binary-cong F α β =₁ binary-cong F α′ β′
    binary-cong₂ F p q = postWhisker F ◁ pair⁼-cong p q

  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-cong-id : {A B C : CAT Γ} (F : MAP (A × B) C) (f : Term A) (x : Term B)
      → binary-cong F (const {P = E} (id₌ f)) (const (id₌ x)) =₁ const (id₌ (binary-apply F f x))
    binary-cong-id  F f x =
      const-cong (postWhisker-id₌ F (pair f x)) ∙
        (post-constant F (id₌ (pair f x)) ∙ (postWhisker F ◁ pair⁼-id f x))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-cong-id-One : {A B C : CAT Γ} (F : MAP (A × B) C) (f : Term A) (x : Term B)
      → binary-cong F (id₌ f) (id₌ x) =₂ id₌ (binary-apply F f x)
    binary-cong-id-One F f x =
      postWhisker-id₌ F (pair f x) ∙ (postWhisker F ◁ pair⁼-id-One f x)

  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    binary-combine : {A B C : CAT Γ} (F : MAP (A × B) C)
      {f₀ f₁ f₂ : Term A} {x₀ x₁ x₂ : Term B} {source : Term C}
      (α : f₁ ＝ f₂) (β : x₁ ＝ x₂)
      (γ : f₀ ＝ f₁) (δ : x₀ ＝ x₁)
      (base : (source ＝ (binary-apply F f₀ x₀)))
      → (binary-cong F α β ∙ (binary-cong F γ δ ∙ base)) =₁
          (binary-cong F (α ∙ γ) (β ∙ δ) ∙ base)
    binary-combine F α β γ δ base =
      comp₌-cong ((binary-cong-comp F α γ β δ) ⁻¹) (id₌ base) ∙
        (comp₌-assoc (binary-cong F α β) (binary-cong F γ δ) base) ⁻¹
```

## Naturality of restriction

```agda
module _ {Γ : Context} where
  module _ {E X : CAT Γ} where
    open Terms.InContext X using (Term)
    open Terms.Equalities E using (_＝_)

    binary-pre-inputs : {Y A B C : CAT Γ} (F : MAP (A × B) C)
      {x x′ : Term A} {y y′ : Term B}
      (α : x ＝ x′) (β : y ＝ y′) (r : MAP Y X)
      → SquareCell₌ (binary-cong F α β ▷ r) (binary-cong F (α ▷ r) (β ▷ r))
          (const (binary-pre F x y r)) (const (binary-pre F x′ y′ r))
    binary-pre-inputs  F {x} {x′} {y} {y′} α β r =
      replace-sides₌
        (const-comp {X = E} (F ◁ pair-pre x y r) (comp-assoc r (pair x y) F) ∙
          comp₌-cong (post-constant F (pair-pre x y r)) (id₌ (const (comp-assoc r (pair x y) F))))
        (const-comp {X = E} (F ◁ pair-pre x′ y′ r) (comp-assoc r (pair x′ y′) F) ∙
          comp₌-cong (post-constant F (pair-pre x′ y′ r)) (id₌ (const (comp-assoc r (pair x′ y′) F))))
        (paste-square₌ (whisker-mixed (pair⁼ α β) r F)
          (post-square₌ F (pair-pre-natural-inputs α β r)))

    binary-pre-substitution : {Y A B C : CAT Γ} (F : MAP (A × B) C)
      (x : Term A) (y : Term B) {r s : MAP Y X} (γ : r ＝ s)
      → SquareCell₌ ((F ∘ pair x y) ◁ γ) (binary-cong F (x ◁ γ) (y ◁ γ))
          (const (binary-pre F x y r)) (const (binary-pre F x y s))
    binary-pre-substitution  F x y {r} {s} γ =
      replace-sides₌
        (const-comp {X = E} (F ◁ pair-pre x y r) (comp-assoc r (pair x y) F) ∙
          comp₌-cong (post-constant F (pair-pre x y r)) (id₌ (const (comp-assoc r (pair x y) F))))
        (const-comp {X = E} (F ◁ pair-pre x y s) (comp-assoc s (pair x y) F) ∙
          comp₌-cong (post-constant F (pair-pre x y s)) (id₌ (const (comp-assoc s (pair x y) F))))
        (paste-square₌ (postWhisker-comp γ (pair x y) F)
          (post-square₌ F (pair-pre-natural-substitution x y γ)))

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-pre-inputs-One : {Y A B C : CAT Γ} (F : MAP (A × B) C)
      {x x′ : Term A} {y y′ : Term B}
      (α : x =₁ x′) (β : y =₁ y′) (r : MAP Y X)
      → SquareCell₌ (binary-cong F α β ▷ r) (binary-cong F (α ▷ r) (β ▷ r))
          (binary-pre F x y r) (binary-pre F x′ y′ r)
    binary-pre-inputs-One F α β r = unconst-sides₌ (binary-pre-inputs F α β r)

    binary-pre-substitution-One : {Y A B C : CAT Γ} (F : MAP (A × B) C)
      (x : Term A) (y : Term B) {r s : MAP Y X} (γ : r =₁ s)
      → SquareCell₌ ((F ∘ pair x y) ◁ γ) (binary-cong F (x ◁ γ) (y ◁ γ))
          (binary-pre F x y r) (binary-pre F x y s)
    binary-pre-substitution-One F x y γ = unconst-sides₌ (binary-pre-substitution F x y γ)
```

## Iterated and staged restriction

Restricting along `σ ∘ τ` agrees with restricting along `σ` and then `τ`;
this is the postcomposition of `pair-pre-iterated`. Along a restriction
diagram, two evaluations give an evaluation of the binary action whose steps
are the binary actions of the coordinate steps followed by `binary-pre`. It
is compatible when the coordinate evaluations are: postcompose the paired
evaluation (`post-compatible`) and split each postwhiskered step into the
binary action and `binary-pre`. These are fixed individual computations,
like `binary-pre` itself.

```agda
module _ {Γ : Context} where
  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    binary-pre-iterated : {A B C : CAT Γ}
      (F : MAP (A × B) C) (f : Term A) (x : Term B) (σ : MAP R X) (τ : MAP Q R)
      → (binary-pre F f x (σ ∘ τ) ∙ comp-assoc τ σ (F ∘ pair f x)) =₂
          (binary-cong F (comp-assoc τ σ f) (comp-assoc τ σ x) ∙
            (binary-pre F (f ∘ σ) (x ∘ σ) τ ∙ (binary-pre F f x σ ▷ τ)))
    binary-pre-iterated F f x σ τ = post-iterated-restriction F (pair f x) σ τ
      (pair-pre f x σ) (pair-pre (f ∘ σ) (x ∘ σ) τ) (pair-pre f x (σ ∘ τ))
      (pair⁼ (comp-assoc τ σ f) (comp-assoc τ σ x)) (pair-pre-iterated f x σ τ)

module _ {Γ : Context} {Q R X : CAT Γ} (ρ : RestrictionDiagram {E = One} {Q = Q} R X) where
  open Terms.InContext Q using (Term)
  open RestrictionDiagram ρ
  open Evaluation

  binary-evaluations : {A B C : CAT Γ} (F : MAP (A × B) C)
    {H : MAP X A} {K : MAP X B} {b₁ : MAP R A} {c₁ : MAP R B}
    {b₂ b₃ : Term A} {c₂ c₃ : Term B}
    → Evaluation ρ H b₁ b₂ b₃ → Evaluation ρ K c₁ c₂ c₃
    → Evaluation ρ (binary-apply F H K) (binary-apply F b₁ c₁)
        (binary-apply F b₂ c₂) (binary-apply F b₃ c₃)
  binary-evaluations F {H} {K} {b₁} {c₁} e₁ e₂ = evaluation
    (binary-cong F (direct e₁) (direct e₂) ∙ binary-pre F H K composite)
    (binary-cong F (first-stage e₁) (first-stage e₂) ∙ binary-pre F H K outer)
    (binary-cong F (second-stage e₁) (second-stage e₂) ∙ binary-pre F b₁ c₁ inner)
    (binary-cong F (finish e₁) (finish e₂))

  binary-compatible : {A B C : CAT Γ} (F : MAP (A × B) C)
    {H : MAP X A} {K : MAP X B} {b₁ : MAP R A} {c₁ : MAP R B}
    {b₂ b₃ : Term A} {c₂ c₃ : Term B}
    (e₁ : Evaluation ρ H b₁ b₂ b₃) (e₂ : Evaluation ρ K c₁ c₂ c₃)
    → Compatible-One ρ e₁ → Compatible-One ρ e₂
    → Compatible-One ρ (binary-evaluations F e₁ e₂)
  binary-compatible F {H} {K} {b₁} {c₁} e₁ e₂ first-compatible second-compatible =
    let paired = pair-evaluations-One ρ e₁ e₂
    in compatible-One ρ {e = binary-evaluations F e₁ e₂}
      (compatible-replace ρ {e = post-evaluation ρ F paired} {e′ = binary-evaluations F e₁ e₂}
        (postwhiskered-composite F (pair⁼ (direct e₁) (direct e₂)) (pair-pre H K composite)
          (comp-assoc composite (pair H K) F))
        (postwhiskered-composite F (pair⁼ (first-stage e₁) (first-stage e₂)) (pair-pre H K outer)
          (comp-assoc outer (pair H K) F))
        (postwhiskered-composite F (pair⁼ (second-stage e₁) (second-stage e₂))
          (pair-pre b₁ c₁ inner) (comp-assoc inner (pair b₁ c₁) F))
        (id₌ (binary-cong F (finish e₁) (finish e₂)))
        (compatible-from-One ρ
          (post-compatible ρ F paired
            (pair-compatible-One ρ e₁ e₂ first-compatible second-compatible))))
```

## Normalizing a route of binary actions

A route that changes the first input by `γ`, `β`, `α` and the second by `ξ`
collapses to a single binary action on the composite coordinate.

```agda
module _ {Γ : Context} where
  module _ {E P : CAT Γ} where
    open Terms.InContext P using (Term)
    open Terms.Equalities E using (_＝_)

    module ActionRouteNormalization {A B Z : CAT Γ} (F : MAP (A × B) Z)
      {k₀ k₁ k₂ k₃ : Term A} {u v : Term B}
      (α : k₂ ＝ k₃) (β : k₁ ＝ k₂) (γ : k₀ ＝ k₁)
      (ξ : u ＝ v) (coordinate : k₀ ＝ k₃)
      {S N O : Term Z}
      (after : N ＝ binary-apply F k₂ v) (e : S ＝ N)
      (sourceAfter : S ＝ binary-apply F k₁ v)
      (tail : S ＝ binary-apply F k₀ u)
      (outer : binary-apply F k₃ v ＝ O) where

      first : binary-apply F k₂ v ＝ binary-apply F k₃ v
      first = binary-cong F α (const (id₌ v))

      second : binary-apply F k₁ v ＝ binary-apply F k₂ v
      second = binary-cong F β (const (id₌ v))

      third : binary-apply F k₀ u ＝ binary-apply F k₁ v
      third = binary-cong F γ ξ

      abstract
        normalize : (α ∙ (β ∙ γ)) =₁ coordinate
          → (after ∙ e) =₁ (second ∙ sourceAfter)
          → sourceAfter =₁ (third ∙ tail)
          → ((outer ∙ (first ∙ after)) ∙ e) =₁
            (outer ∙ (binary-cong F coordinate ξ ∙ tail))
        normalize coordinate-law natural restrict =
          let joinInner = comp₌-cong
                  (binary-cong₂ F (id₌ (β ∙ γ)) (comp₌-unitˡ ξ)) (id₌ tail) ∙
                binary-combine F β (const (id₌ v)) γ ξ tail
              joinOuter = comp₌-cong
                  (binary-cong₂ F coordinate-law (comp₌-unitˡ ξ)) (id₌ tail) ∙
                binary-combine F α (const (id₌ v)) (β ∙ γ) ξ tail
              reassociate = comp₌-cong (id₌ outer) (comp₌-assoc first after e) ∙
                comp₌-assoc outer (first ∙ after) e
              restricted = comp₌-cong (id₌ second) restrict ∙ natural
          in comp₌-cong (id₌ outer)
              (joinOuter ∙ comp₌-cong (id₌ first) (joinInner ∙ restricted)) ∙
            reassociate
```
