# Whiskering compatibility derived from horizontal composition

The five individual-input laws are consequences of horizontal units and
associativity. Identity inputs are inserted as constant families; their
normalizations retain the vertical units and functor associators.
`derivedWhiskering` packages these proofs for downstream use. It introduces
no additional assumption, and does not use interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section02.DerivedWhiskering
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringAxioms V T P S)
  (H : Coherence.HorizontalCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.VerticalCoherence VC
open Coherence.WhiskeringAxioms W
open Coherence.HorizontalCoherence H
open Specialization V T P PL S

unitˡ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ＝ g))
  → (const (idIso g) ∙ α) =₁ α
unitˡ {f = f} {g} α = specialize (isoComp-unitˡ f g) α
  (isoComp-evaluate (const (idIso g)) (id (f ＝ g)) α
    (const-pre (idIso g) α) (comp-unitˡ α)) (comp-unitˡ α)

unitʳ : {X C D : CAT} {f g : MAP C D} (α : MAP X (f ＝ g))
  → (α ∙ const (idIso f)) =₁ α
unitʳ {f = f} {g} α = specialize (isoComp-unitʳ f g) α
  (isoComp-evaluate (id (f ＝ g)) (const (idIso f)) α
    (comp-unitˡ α) (const-pre (idIso f) α)) (comp-unitˡ α)

horizontal-identityˡ : {X C D E : CAT} {f f′ : MAP C D}
  (g : MAP D E) (α : MAP X (f ＝ f′))
  → (const (idIso g) ⋆ α) =₁ (g ◁ α)
horizontal-identityˡ {X} {f′ = f′} g α = unitˡ (g ◁ α) ∙
  isoComp-cong
    ((preWhisker-idIso g f′ ▷ terminate X) ∙
      (comp-assoc (terminate X) (idIso g) (preWhisker f′)) ⁻¹)
    (idIso (g ◁ α))

horizontal-identityʳ : {X C D E : CAT} {g g′ : MAP D E}
  (β : MAP X (g ＝ g′)) (f : MAP C D)
  → (β ⋆ const (idIso f)) =₁ (β ▷ f)
horizontal-identityʳ {X} {g = g} β f = unitʳ (β ▷ f) ∙
  isoComp-cong (idIso (β ▷ f))
    ((postWhisker-idIso g f ▷ terminate X) ∙
      (comp-assoc (terminate X) (idIso f) (postWhisker g)) ⁻¹)

horizontal-identities : {X C D E : CAT} (f : MAP C D) (g : MAP D E)
  → (const {P = X} (idIso g) ⋆ const (idIso f)) =₁ (const (idIso (g ∘ f)))
horizontal-identities {X} f g =
  (postWhisker-idIso g f ▷ terminate X) ∙
  ((comp-assoc (terminate X) (idIso f) (postWhisker g)) ⁻¹ ∙
    horizontal-identityˡ g (const (idIso f)))

hcomp-evaluate : {R X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : MAP X (g ＝ g′)) (α : MAP X (f ＝ f′)) (r : MAP R X)
  {β′ : MAP R (g ＝ g′)} {α′ : MAP R (f ＝ f′)}
  → (β ∘ r) =₁ β′ → (α ∘ r) =₁ α′
  → ((β ⋆ α) ∘ r) =₁ (β′ ⋆ α′)
hcomp-evaluate β α r b a = hcomp-cong b a ∙ hcomp-pre β α r

horizontal-assoc : {X B C D E : CAT}
  {f f′ : MAP B C} {g g′ : MAP C D} {h h′ : MAP D E}
  (γ : MAP X (h ＝ h′)) (β : MAP X (g ＝ g′)) (α : MAP X (f ＝ f′))
  → (const (comp-assoc f′ g′ h′) ∙ ((γ ⋆ β) ⋆ α)) =₁
      ((γ ⋆ (β ⋆ α)) ∙ const (comp-assoc f g h))
horizontal-assoc {f = f} {f′} {g} {g′} {h} {h′} γ β α =
  let r = pair (pair γ β) α
      first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc r pr₁ pr₁)
      second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc r pr₁ pr₂)
      third = pair-β₂ (pair γ β) α
  in specialize (hcomp-assoc f f′ g g′ h h′) r
    (isoComp-evaluate (const (comp-assoc f′ g′ h′)) (((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) ⋆ pr₂) r
      (const-pre (comp-assoc f′ g′ h′) r)
      (hcomp-evaluate ((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) pr₂ r
        (hcomp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) r first second) third))
    (isoComp-evaluate ((pr₁ ∘ pr₁) ⋆ ((pr₂ ∘ pr₁) ⋆ pr₂)) (const (comp-assoc f g h)) r
      (hcomp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ⋆ pr₂) r first
        (hcomp-evaluate (pr₂ ∘ pr₁) pr₂ r second third))
      (const-pre (comp-assoc f g h) r))

opaque
  postWhisker-id : {C D : CAT} (f g : MAP C D)
    → (const (comp-unitˡ g) ∙ (id D ◁ id (f ＝ g))) =₁
        (id (f ＝ g) ∙ const (comp-unitˡ f))
  postWhisker-id {D = D} f g = hcomp-unitˡ f g ∙
    (isoComp-cong (idIso (const (comp-unitˡ g))) (horizontal-identityˡ (id D) (id (f ＝ g)))) ⁻¹

  preWhisker-id : {C D : CAT} (f g : MAP C D)
    → (const (comp-unitʳ g) ∙ (id (f ＝ g) ▷ id C)) =₁
        (id (f ＝ g) ∙ const (comp-unitʳ f))
  preWhisker-id {C} f g = hcomp-unitʳ f g ∙
    (isoComp-cong (idIso (const (comp-unitʳ g))) (horizontal-identityʳ (id (f ＝ g)) (id C))) ⁻¹

  postWhisker-comp : {C D E F : CAT} (f g : MAP C D) (u : MAP D E) (v : MAP E F)
    → let σ = id (f ＝ g)
      in (const (comp-assoc g u v) ∙ ((v ∘ u) ◁ σ)) =₁
        ((v ◁ (u ◁ σ)) ∙ const (comp-assoc f u v))
  postWhisker-comp f g u v =
    let σ = id (f ＝ g)
        left = horizontal-identityˡ (v ∘ u) σ ∙
          hcomp-cong (horizontal-identities u v) (idIso σ)
        right = (postWhisker v ◁ horizontal-identityˡ u σ) ∙
          horizontal-identityˡ v (const (idIso u) ⋆ σ)
    in isoComp-cong right (idIso (const (comp-assoc f u v))) ∙
      (horizontal-assoc (const (idIso v)) (const (idIso u)) σ ∙
        (isoComp-cong (idIso (const (comp-assoc g u v))) left) ⁻¹)

  preWhisker-comp : {A B C D : CAT} (f g : MAP C D) (k : MAP B C) (l : MAP A B)
    → let σ = id (f ＝ g)
      in (const (comp-assoc l k g) ∙ ((σ ▷ k) ▷ l)) =₁
        ((σ ▷ (k ∘ l)) ∙ const (comp-assoc l k f))
  preWhisker-comp f g k l =
    let σ = id (f ＝ g)
        left = (preWhisker l ◁ horizontal-identityʳ σ k) ∙
          horizontal-identityʳ (σ ⋆ const (idIso k)) l
        right = horizontal-identityʳ σ (k ∘ l) ∙
          hcomp-cong (idIso σ) (horizontal-identities l k)
    in isoComp-cong right (idIso (const (comp-assoc l k f))) ∙
      (horizontal-assoc σ (const (idIso k)) (const (idIso l)) ∙
        (isoComp-cong (idIso (const (comp-assoc l k g))) left) ⁻¹)

  whisker-mixed : {B C D E : CAT} (f g : MAP C D) (k : MAP B C) (u : MAP D E)
    → let σ = id (f ＝ g)
      in (const (comp-assoc k g u) ∙ ((u ◁ σ) ▷ k)) =₁
        ((u ◁ (σ ▷ k)) ∙ const (comp-assoc k f u))
  whisker-mixed f g k u =
    let σ = id (f ＝ g)
        left = (preWhisker k ◁ horizontal-identityˡ u σ) ∙
          horizontal-identityʳ (const (idIso u) ⋆ σ) k
        right = (postWhisker u ◁ horizontal-identityʳ σ k) ∙
          horizontal-identityˡ u (σ ⋆ const (idIso k))
    in isoComp-cong right (idIso (const (comp-assoc k f u))) ∙
      (horizontal-assoc (const (idIso u)) σ (const (idIso k)) ∙
        (isoComp-cong (idIso (const (comp-assoc k g u))) left) ⁻¹)

derivedWhiskering : Coherence.WhiskeringCoherence V T P S
derivedWhiskering = record
  { axioms = W
  ; postWhisker-id = postWhisker-id
  ; preWhisker-id = preWhisker-id
  ; postWhisker-comp = postWhisker-comp
  ; preWhisker-comp = preWhisker-comp
  ; whisker-mixed = whisker-mixed
  }
```
