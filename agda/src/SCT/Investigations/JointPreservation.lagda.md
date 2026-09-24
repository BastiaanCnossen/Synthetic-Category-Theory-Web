# Joint preservation, conditional on joint interchange

This isolates the extra joint-interchange hypothesis. The shared theory uses
only the two fixed-input clauses. The investigation does not prove that joint
interchange is independent of the full manuscript axioms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.Investigations.JointPreservation
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.VerticalCoherence VC
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S

module Triple {X A B C : CAT}
  (γ : MAP X C) (β : MAP X B) (α : MAP X A) where

  parameters : MAP X ((C × B) × A)
  parameters = pair (pair γ β) α

  first : ((pr₁ ∘ pr₁) ∘ parameters) =₁ γ
  first = pair-β₁ γ β ∙
    ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc parameters pr₁ pr₁)

  second : ((pr₂ ∘ pr₁) ∘ parameters) =₁ β
  second = pair-β₂ γ β ∙
    ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc parameters pr₁ pr₂)

  third : (pr₂ ∘ parameters) =₁ α
  third = pair-β₂ (pair γ β) α

isoComp-assoc-family : {X C D : CAT} {f g h k : MAP C D}
  (γ : MAP X (h ＝ k)) (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g))
  → ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))
isoComp-assoc-family {f = f} {g} {h} {k} γ β α =
  let open Triple γ β α
  in specialize (Units.isoComp-assoc-left VC f g h k) parameters
    (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ parameters
      (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) parameters first second) third)
    (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) parameters first
      (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ parameters second third))

postWhisker-isoComp-family : {X C D E : CAT} {f g h : MAP C D}
  (u : MAP D E) (τ : MAP X (g ＝ h)) (σ : MAP X (f ＝ g))
  → (u ◁ (τ ∙ σ)) =₁ ((u ◁ τ) ∙ (u ◁ σ))
postWhisker-isoComp-family {f = f} {g} {h} u τ σ =
  let parameters = pair τ σ
  in specialize (postWhisker-isoComp f g h u) parameters
    (postWhisker-evaluate u (pr₁ ∙ pr₂) parameters
      (isoComp-evaluate pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
    (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) parameters
      (postWhisker-evaluate u pr₁ parameters (pair-β₁ τ σ))
      (postWhisker-evaluate u pr₂ parameters (pair-β₂ τ σ)))

preWhisker-isoComp-family : {X B C D : CAT} {f g h : MAP C D}
  (τ : MAP X (g ＝ h)) (σ : MAP X (f ＝ g)) (k : MAP B C)
  → ((τ ∙ σ) ▷ k) =₁ ((τ ▷ k) ∙ (σ ▷ k))
preWhisker-isoComp-family {f = f} {g} {h} τ σ k =
  let parameters = pair τ σ
  in specialize (preWhisker-isoComp f g h k) parameters
    (preWhisker-evaluate (pr₁ ∙ pr₂) k parameters
      (isoComp-evaluate pr₁ pr₂ parameters (pair-β₁ τ σ) (pair-β₂ τ σ)))
    (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) parameters
      (preWhisker-evaluate pr₁ k parameters (pair-β₁ τ σ))
      (preWhisker-evaluate pr₂ k parameters (pair-β₂ τ σ)))

reassociateFour-family : {X C D : CAT} {f g h i j : MAP C D}
  (δ : MAP X (i ＝ j)) (γ : MAP X (h ＝ i))
  (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g))
  → ((δ ∙ γ) ∙ (β ∙ α)) =₁ (δ ∙ ((γ ∙ β) ∙ α))
reassociateFour-family δ γ β α =
  isoComp-cong (idIso δ) ((isoComp-assoc-family γ β α) ⁻¹)
  ∙ isoComp-assoc-family δ γ (β ∙ α)
```

The following record is an additional investigation hypothesis. It is not
a field of `Theory`, whose two fixed-input witnesses are supplied independently.
The converse argument below relates this extra hypothesis to joint preservation;
it does not establish independence from the complete manuscript axioms.

```agda
record JointInterchange : Set (c ⊔ m) where
  field
    interchange-joint : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
      → let X = (F ＝ G) × (h ＝ k)
            τ : MAP X (F ＝ G)
            τ = pr₁
            σ : MAP X (h ＝ k)
            σ = pr₂
        in ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))

record FamilyPreservation : Set (c ⊔ m) where
  field
    preserve : {X C D E : CAT}
      {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
      (β₂ : MAP X (g₁ ＝ g₂)) (β₁ : MAP X (g₀ ＝ g₁))
      (α₂ : MAP X (f₁ ＝ f₂)) (α₁ : MAP X (f₀ ＝ f₁))
      → ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) =₁ ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))

module Conditional (J : JointInterchange) where
  open JointInterchange J

  interchange-family : {X B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (τ : MAP X (F ＝ G)) (σ : MAP X (h ＝ k))
    → ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))
  interchange-family {F = F} {G} {h} {k} τ σ =
    let parameters = pair τ σ
    in specialize (interchange-joint F G h k) parameters
      (isoComp-evaluate (pr₁ ▷ k) (F ◁ pr₂) parameters
        (preWhisker-evaluate pr₁ k parameters (pair-β₁ τ σ))
        (postWhisker-evaluate F pr₂ parameters (pair-β₂ τ σ)))
      (isoComp-evaluate (G ◁ pr₂) (pr₁ ▷ h) parameters
        (postWhisker-evaluate G pr₂ parameters (pair-β₂ τ σ))
        (preWhisker-evaluate pr₁ h parameters (pair-β₁ τ σ)))

  hcomp-isoComp-family : {X C D E : CAT}
    {f₀ f₁ f₂ : MAP C D} {g₀ g₁ g₂ : MAP D E}
    (β₂ : MAP X (g₁ ＝ g₂)) (β₁ : MAP X (g₀ ＝ g₁))
    (α₂ : MAP X (f₁ ＝ f₂)) (α₁ : MAP X (f₀ ＝ f₁))
    → ((β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)) =₁ ((β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁))
  hcomp-isoComp-family {f₁ = f₁} {f₂} {g₀ = g₀} {g₁} β₂ β₁ α₂ α₁ =
    let δ = β₂ ▷ f₂
        γ = β₁ ▷ f₂
        β = g₀ ◁ α₂
        α = g₀ ◁ α₁
        γ′ = g₁ ◁ α₂
        β′ = β₁ ▷ f₁
        expand = isoComp-cong
          (preWhisker-isoComp-family β₂ β₁ f₂)
          (postWhisker-isoComp-family g₀ α₂ α₁)
        exchange = isoComp-cong (idIso δ)
          (isoComp-cong (interchange-family β₁ α₂) (idIso α))
    in (reassociateFour-family δ γ′ β′ α) ⁻¹
       ∙ (exchange ∙ (reassociateFour-family δ γ β α ∙ expand))

  familyPreservation : FamilyPreservation
  familyPreservation = record { preserve = hcomp-isoComp-family }

  module FourInputs {C D E : CAT}
    (f₀ f₁ f₂ : MAP C D) (g₀ g₁ g₂ : MAP D E) where

    Parameter : CAT
    Parameter = ((g₁ ＝ g₂) × (g₀ ＝ g₁)) × ((f₁ ＝ f₂) × (f₀ ＝ f₁))

    β₂ : MAP Parameter (g₁ ＝ g₂)
    β₂ = pr₁ ∘ pr₁

    β₁ : MAP Parameter (g₀ ＝ g₁)
    β₁ = pr₂ ∘ pr₁

    α₂ : MAP Parameter (f₁ ＝ f₂)
    α₂ = pr₁ ∘ pr₂

    α₁ : MAP Parameter (f₀ ＝ f₁)
    α₁ = pr₂ ∘ pr₂

    preserve-first : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
    preserve-first = (β₂ ∙ β₁) ⋆ (α₂ ∙ α₁)

    compose-first : MAP Parameter ((g₀ ∘ f₀) ＝ (g₂ ∘ f₂))
    compose-first = (β₂ ⋆ α₂) ∙ (β₁ ⋆ α₁)

    preservation : preserve-first =₁ compose-first
    preservation = hcomp-isoComp-family β₂ β₁ α₂ α₁
```

Conversely, preservation for arbitrary common parameters supplies joint
interchange by setting the last outer and first inner input to identities.
The following normalization lemmas and proof check that converse. This
establishes both implications between the displayed principles; it does not
identify their full types of chosen witnesses.

```agda
isoComp-unitˡ-family : {X C D : CAT} {f g : MAP C D}
  (α : MAP X (f ＝ g)) → (const (idIso g) ∙ α) =₁ α
isoComp-unitˡ-family {f = f} {g} α =
  specialize (isoComp-unitˡ f g) α
    (isoComp-evaluate (const (idIso g)) (id (f ＝ g)) α
      (const-pre (idIso g) α) (comp-unitˡ α))
    (comp-unitˡ α)

isoComp-unitʳ-family : {X C D : CAT} {f g : MAP C D}
  (α : MAP X (f ＝ g)) → (α ∙ const (idIso f)) =₁ α
isoComp-unitʳ-family {f = f} {g} α =
  specialize (isoComp-unitʳ f g) α
    (isoComp-evaluate (id (f ＝ g)) (const (idIso f)) α
      (comp-unitˡ α) (const-pre (idIso f) α))
    (comp-unitˡ α)

postWhisker-const : {X C D E : CAT} {f g : MAP C D}
  (u : MAP D E) (α : f =₁ g)
  → (u ◁ const {P = X} α) =₁ (const (u ◁ α))
postWhisker-const {X} u α = (comp-assoc (terminate X) α (postWhisker u)) ⁻¹

preWhisker-const : {X B C D : CAT} {f g : MAP C D}
  (α : f =₁ g) (k : MAP B C)
  → (const {P = X} α ▷ k) =₁ (const (α ▷ k))
preWhisker-const {X} α k = (comp-assoc (terminate X) α (preWhisker k)) ⁻¹

hcomp-idOuter-family : {X C D E : CAT} {f f′ : MAP C D}
  (g : MAP D E) (α : MAP X (f ＝ f′))
  → (const (idIso g) ⋆ α) =₁ (g ◁ α)
hcomp-idOuter-family {X} {f′ = f′} g α =
  isoComp-unitˡ-family (g ◁ α) ∙
    isoComp-cong
      ((preWhisker-idIso g f′ ▷ terminate X) ∙ preWhisker-const (idIso g) f′)
      (idIso (g ◁ α))

hcomp-idInner-family : {X C D E : CAT} {g g′ : MAP D E}
  (β : MAP X (g ＝ g′)) (f : MAP C D)
  → (β ⋆ const (idIso f)) =₁ (β ▷ f)
hcomp-idInner-family {X} {g = g} β f =
  isoComp-unitʳ-family (β ▷ f) ∙
    isoComp-cong (idIso (β ▷ f))
      ((postWhisker-idIso g f ▷ terminate X) ∙ postWhisker-const g (idIso f))

preservation-to-interchange : FamilyPreservation → JointInterchange
preservation-to-interchange H = record { interchange-joint = joint }
  where
  joint : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
    → let X = (F ＝ G) × (h ＝ k)
          τ : MAP X (F ＝ G)
          τ = pr₁
          σ : MAP X (h ＝ k)
          σ = pr₂
      in ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))
  joint F G h k =
    isoComp-cong (hcomp-idOuter-family G pr₂) (hcomp-idInner-family pr₁ h)
    ∙ (FamilyPreservation.preserve H (const (idIso G)) pr₁ pr₂ (const (idIso h))
       ∙ (hcomp-cong (isoComp-unitˡ-family pr₁) (isoComp-unitʳ-family pr₂)) ⁻¹)
```

Derivability from the current fixed-input axiom package remains open.
The conditional implications here make no independence claim.
