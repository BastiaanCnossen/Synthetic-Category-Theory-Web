# Horizontal composition of identifications

The paragraph following the interchange axiom asserts that the derived
horizontal composite preserves identities and vertical composites. Both are
stated for families with an arbitrary common parameter category.

Preservation of identities is the shared normalization
`Specialization.hcomp-id₌`: the horizontal composite of the constant identity
families of `g` and `f` is identified with the constant identity family of
`g ∘ f`. The joint interchange law in its family form is
`Specialization.interchange`; no separate alias is introduced here.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.HorizontalComposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; reassociateFour; postWhisker-comp₌; preWhisker-comp₌; interchange)
```

## Preservation of vertical composition

For four families with a common parameter, expand both horizontal
composites using preservation of vertical composition by whiskering,
exchange the middle pair by interchange, and reassociate. Only the primitive
whiskering and interchange axioms and the vertical calculus are used; the
five whiskering laws for composite functors are not.

```agda
module _ {Γ : Context} where
  module _ {X C : CAT Γ} where
    open Terms.InContext C using (Term)
    open Terms.Equalities X using (_＝_)

    hcomp-comp₌ : {D E : CAT Γ} {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
      (β₂ : g₁ ＝ g₂) (β₁ : g₀ ＝ g₁)
      (α₂ : f₁ ＝ f₂) (α₁ : f₀ ＝ f₁)
      → ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) =₁ ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))
    hcomp-comp₌ {f₁ = f₁} {f₂} {g₀ = g₀} {g₁} β₂ β₁ α₂ α₁ =
      let δ = β₂ ▷ f₂
          γ = β₁ ▷ f₂
          β = g₀ ◁ α₂
          α = g₀ ◁ α₁
          γ′ = g₁ ◁ α₂
          β′ = β₁ ▷ f₁
          expand : ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) =₁ ((δ ∙ γ) ∙ (β ∙ α))
          expand = comp₌-cong
            (preWhisker-comp₌ β₂ β₁ f₂)
            (postWhisker-comp₌ g₀ α₂ α₁)
          exchange : (δ ∙ ((γ ∙ β) ∙ α)) =₁ (δ ∙ ((γ′ ∙ β′) ∙ α))
          exchange = comp₌-cong (id₌ δ)
            (comp₌-cong (interchange β₁ α₂) (id₌ α))
      in (reassociateFour δ γ′ β′ α) ⁻¹
         ∙ (exchange ∙ (reassociateFour δ γ β α ∙ expand))
```

The fourfold reassociation is a finite pasting of the family associativity
law. The proof supplies an explicit witness and asserts no uniqueness of
all possible pastings.
