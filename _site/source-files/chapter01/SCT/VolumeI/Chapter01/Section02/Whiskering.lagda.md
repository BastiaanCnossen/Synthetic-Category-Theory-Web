# Whiskering and composition of functors

The five laws below compare whiskering by identity functors and by composite
functors. They concern the functors doing the whiskering. This is distinct
from the preservation of identity identifications and vertical composites by
a fixed whiskering functor (`id₌` and `comp₌` rather than `id` and `∘`),
which are supplied axioms or their specializations.

Each law is a consequence of unitor or associator naturality, applied to
families with an arbitrary common parameter. Insert constant identity
families as some of the inputs of the prescribed naturality square; then
normalize its two horizontal edges, using the shared identifications of
horizontal composites with identities. The result is again an equation
between two composites with the prescribed constant sides. These proofs
introduce no assumption and do not use interchange. As in the first rebuild,
the five proofs are opaque: clients use their statements, not their bodies.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.Whiskering where

import SCT.VolumeI.Chapter01.Section02.Naturality as N

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
```

## Identity functors

Unitor naturality for a family `α`, with the identity identification of the
identity functor on the other side, is the law for whiskering by that identity.

```agda
module _ {Γ : Context} where
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    opaque

      postWhisker-id : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
        → (const (comp-unitˡ g) ∙ (id D ◁ α)) =₁ (α ∙ const (comp-unitˡ f))
      postWhisker-id {D = D} {g = g} α = unitˡ-natural α ∙
        (comp₌-cong (id₌ (const (comp-unitˡ g))) (hcomp-id-outer (id D) α)) ⁻¹

      preWhisker-id : {C D : CAT Γ} {f g : MAP C D} (α : f ＝ g)
        → (const (comp-unitʳ g) ∙ (α ▷ id C)) =₁ (α ∙ const (comp-unitʳ f))
      preWhisker-id {C = C} {g = g} α = unitʳ-natural α ∙
        (comp₌-cong (id₌ (const (comp-unitʳ g))) (hcomp-id-inner α (id C))) ⁻¹
```

## Composite functors

The three laws insert, respectively, the inputs `(id v, id u, α)`,
`(α, id k, id l)` and `(id u, α, id k)` into associator naturality, where
each identity stands for its constant family. The calculations
`normalize-top` and `normalize-bottom` identify the top and bottom edges of
the prescribed square with the required whiskerings; the vertical sides are
the constant associators throughout.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    opaque

      postWhisker-comp : {C D E F : CAT Γ} {f g : MAP C D}
        (α : f ＝ g) (u : MAP D E) (v : MAP E F)
        → N.NaturalityAt (N.Post (v ∘ u) (N.Input C D)) (N.Post v (N.Post u (N.Input C D)))
            (λ q → comp-assoc q u v) α
      postWhisker-comp {f = f} {g} α u v =
        let normalize-top : ((const (id₌ v) ⋆ const (id₌ u)) ⋆ α) =₁ ((v ∘ u) ◁ α)
            normalize-top = hcomp-id-outer (v ∘ u) α ∙
              hcomp-cong (hcomp-id₌ v u) (id₌ α)
            normalize-bottom : (const (id₌ v) ⋆ (const (id₌ u) ⋆ α)) =₁ (v ◁ (u ◁ α))
            normalize-bottom = (postWhisker v ◁ hcomp-id-outer u α) ∙
              hcomp-id-outer v (const (id₌ u) ⋆ α)
        in comp₌-cong normalize-bottom (id₌ (const (comp-assoc f u v))) ∙
          (assoc-natural (const (id₌ v)) (const (id₌ u)) α ∙
            (comp₌-cong (id₌ (const (comp-assoc g u v))) normalize-top) ⁻¹)

      preWhisker-comp : {A B C D : CAT Γ} {f g : MAP C D}
        (α : f ＝ g) (k : MAP B C) (l : MAP A B)
        → (const (comp-assoc l k g) ∙ ((α ▷ k) ▷ l)) =₁
            ((α ▷ (k ∘ l)) ∙ const (comp-assoc l k f))
      preWhisker-comp {f = f} {g} α k l =
        let normalize-top : ((α ⋆ const (id₌ k)) ⋆ const (id₌ l)) =₁ ((α ▷ k) ▷ l)
            normalize-top = (preWhisker l ◁ hcomp-id-inner α k) ∙
              hcomp-id-inner (α ⋆ const (id₌ k)) l
            normalize-bottom : (α ⋆ (const (id₌ k) ⋆ const (id₌ l))) =₁ (α ▷ (k ∘ l))
            normalize-bottom = hcomp-id-inner α (k ∘ l) ∙
              hcomp-cong (id₌ α) (hcomp-id₌ k l)
        in comp₌-cong normalize-bottom (id₌ (const (comp-assoc l k f))) ∙
          (assoc-natural α (const (id₌ k)) (const (id₌ l)) ∙
            (comp₌-cong (id₌ (const (comp-assoc l k g))) normalize-top) ⁻¹)

      whisker-mixed : {B C D E : CAT Γ} {f g : MAP C D}
        (α : f ＝ g) (k : MAP B C) (u : MAP D E)
        → (const (comp-assoc k g u) ∙ ((u ◁ α) ▷ k)) =₁
            ((u ◁ (α ▷ k)) ∙ const (comp-assoc k f u))
      whisker-mixed {f = f} {g} α k u =
        let normalize-top : ((const (id₌ u) ⋆ α) ⋆ const (id₌ k)) =₁ ((u ◁ α) ▷ k)
            normalize-top = (preWhisker k ◁ hcomp-id-outer u α) ∙
              hcomp-id-inner (const (id₌ u) ⋆ α) k
            normalize-bottom : (const (id₌ u) ⋆ (α ⋆ const (id₌ k))) =₁ (u ◁ (α ▷ k))
            normalize-bottom = (postWhisker u ◁ hcomp-id-inner α k) ∙
              hcomp-id-outer u (α ⋆ const (id₌ k))
        in comp₌-cong normalize-bottom (id₌ (const (comp-assoc k f u))) ∙
          (assoc-natural (const (id₌ u)) α (const (id₌ k)) ∙
            (comp₌-cong (id₌ (const (comp-assoc k g u))) normalize-top) ⁻¹)
```

For individual identifications take `X = One`. The sides are then constant
families over `One`; `const-One` identifies them with the associators and
unitors themselves where a client needs the unparameterized equation.

## Naturality in the innermost variable

The adapter uses the same chosen opaque calculation and constant associators.

```agda
module _ {Γ : Context} where
  postWhisker-comp-naturality : {B C D E : CAT Γ} (u : MAP C D) (v : MAP D E)
    → N.Naturality (N.Post (v ∘ u) (N.Input B C)) (N.Post v (N.Post u (N.Input B C)))
        (λ f → comp-assoc f u v)
  postWhisker-comp-naturality u v α = postWhisker-comp α u v
```
