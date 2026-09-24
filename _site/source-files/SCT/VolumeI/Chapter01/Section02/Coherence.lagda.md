# Composition and its coherences

The supplied coherence families are organized alongside Section 1.2.
The primitive interface uses the two fixed-input interchange comparisons.
The five individual compatibility laws form a derived API, constructed in
`DerivedWhiskering` from the horizontal-composition axioms. The operations `α ∙ β`, `u ◁ α`, `α ▷ k`, and `β ⋆ α` apply to terms
with a common source. That source is inferred, including when it is an
isomorphism anima or a product of them. `const` is the ordinary constant
functor. No separate boundary metalanguage is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products

module SCT.VolumeI.Chapter01.Section02.Coherence
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V) where

open Vocabulary V
open Operations V
open Terminal.Constructions V T
open Products.ProductData P

record CompositionStructure : Set (c ⊔ m) where
  field
    idIso : {C D : CAT} (f : MAP C D) → f =₁ f
    isoComp : {C D : CAT} {f g h : MAP C D}
      → MAP ((g ＝ h) × (f ＝ g)) (f ＝ h)

    comp-unitˡ : {C D : CAT} (f : MAP C D) → (id D ∘ f) =₁ f
    comp-unitʳ : {C D : CAT} (f : MAP C D) → (f ∘ id C) =₁ f
    comp-assoc : {B C D E : CAT} (f : MAP B C) (g : MAP C D) (h : MAP D E)
      → ((h ∘ g) ∘ f) =₁ (h ∘ (g ∘ f))

module Composition (S : CompositionStructure) where
  open CompositionStructure S
  infixr 25 _∙_
  infixr 30 _⋆_

  _∙_ : {X C D : CAT} {f g h : MAP C D}
    → MAP X (g ＝ h) → MAP X (f ＝ g) → MAP X (f ＝ h)
  β ∙ α = isoComp ∘ pair β α

  _⋆_ : {X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
    → MAP X (g ＝ g′) → MAP X (f ＝ f′) → MAP X ((g ∘ f) ＝ (g′ ∘ f′))
  _⋆_ {f′ = f′} {g = g} β α = (β ▷ f′) ∙ (g ◁ α)

  isoHComp : {C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
    → MAP ((g ＝ g′) × (f ＝ f′)) ((g ∘ f) ＝ (g′ ∘ f′))
  isoHComp = pr₁ ⋆ pr₂
```

The identity natural isomorphism and vertical composition are supplied;
horizontal composition and its parameterized functor are definitions.
The unit and associativity fields in `CompositionStructure` are supplied
early because later signatures use them. The next five fields follow
`post:Composition_Of_Identifications`. Each is a natural isomorphism
between actual functors on the displayed parameter category.

```agda
record VerticalCoherence (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    isoComp-unitˡ : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (const (idIso g) ∙ σ) =₁ σ

    isoComp-unitʳ : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (σ ∙ const (idIso f)) =₁ σ

    isoComp-assoc : {C D : CAT} (f g h k : MAP C D)
      → let X = (h ＝ k) × ((g ＝ h) × (f ＝ g))
            α : MAP X (f ＝ g)
            α = pr₂ ∘ pr₂
            β : MAP X (g ＝ h)
            β = pr₁ ∘ pr₂
            γ : MAP X (h ＝ k)
            γ = pr₁
        in ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))

    isoComp-inverseˡ : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (σ ⁻¹ ∙ σ) =₁ (const (idIso f))

    isoComp-inverseʳ : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (σ ∙ σ ⁻¹) =₁ (const (idIso g))
```

The next record supplies whiskering and interchange comparisons.
Identity preservation has no varying isomorphism input. The remaining laws
are parameterized. The two fixed-input interchange comparisons are primitive.
Joint interchange is a separate hypothesis, used only by the conditional
`JointPreservation` module.

```agda
record WhiskeringAxioms (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    postWhisker-idIso : {C D E : CAT} (u : MAP D E) (f : MAP C D)
      → (u ◁ idIso f) =₂ (idIso (u ∘ f))

    preWhisker-idIso : {B C D : CAT} (f : MAP C D) (k : MAP B C)
      → (idIso f ▷ k) =₂ (idIso (f ∘ k))

    postWhisker-isoComp : {C D E : CAT} (f g h : MAP C D) (u : MAP D E)
      → let X = (g ＝ h) × (f ＝ g)
            σ : MAP X (f ＝ g)
            σ = pr₂
            τ : MAP X (g ＝ h)
            τ = pr₁
        in (u ◁ (τ ∙ σ)) =₁ ((u ◁ τ) ∙ (u ◁ σ))

    preWhisker-isoComp : {B C D : CAT} (f g h : MAP C D) (k : MAP B C)
      → let X = (g ＝ h) × (f ＝ g)
            σ : MAP X (f ＝ g)
            σ = pr₂
            τ : MAP X (g ＝ h)
            τ = pr₁
        in ((τ ∙ σ) ▷ k) =₁ ((τ ▷ k) ∙ (σ ▷ k))

    interchange-fixedOuter : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
      (τ : F =₁ G)
      → let σ = id (h ＝ k)
        in (const (τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ const (τ ▷ h))

    interchange-fixedInner : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
      (σ : h =₁ k)
      → let τ = id (F ＝ G)
        in ((τ ▷ k) ∙ const (F ◁ σ)) =₁ (const (G ◁ σ) ∙ (τ ▷ h))

record WhiskeringCoherence (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    axioms : WhiskeringAxioms S
  open WhiskeringAxioms axioms public
  field
    -- Derived API, constructed from horizontal coherence in DerivedWhiskering.
    postWhisker-id : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (const (comp-unitˡ g) ∙ (id D ◁ σ)) =₁
                  (σ ∙ const (comp-unitˡ f))

    preWhisker-id : {C D : CAT} (f g : MAP C D)
      → let σ = id (f ＝ g)
        in (const (comp-unitʳ g) ∙ (σ ▷ id C)) =₁
                  (σ ∙ const (comp-unitʳ f))

    postWhisker-comp : {C D E F : CAT} (f g : MAP C D) (u : MAP D E) (v : MAP E F)
      → let σ = id (f ＝ g)
        in (const (comp-assoc g u v) ∙ ((v ∘ u) ◁ σ)) =₁
                  ((v ◁ (u ◁ σ)) ∙ const (comp-assoc f u v))

    preWhisker-comp : {A B C D : CAT} (f g : MAP C D) (k : MAP B C) (l : MAP A B)
      → let σ = id (f ＝ g)
        in (const (comp-assoc l k g) ∙ ((σ ▷ k) ▷ l)) =₁
                  ((σ ▷ (k ∘ l)) ∙ const (comp-assoc l k f))

    whisker-mixed : {B C D E : CAT} (f g : MAP C D) (k : MAP B C) (u : MAP D E)
      → let σ = id (f ＝ g)
        in (const (comp-assoc k g u) ∙ ((u ◁ σ) ▷ k)) =₁
                  ((u ◁ (σ ▷ k)) ∙ const (comp-assoc k f u))
```

The next record supplies comparisons concerning the **derived** horizontal
operation (`post:Horizontal_Composition_Is_Unital_And_Associative`). Naming the
operation does not promote it to an additional primitive.

```agda
record HorizontalCoherence (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    hcomp-unitˡ : {C D : CAT} (f f′ : MAP C D)
      → let α = id (f ＝ f′)
        in (const (comp-unitˡ f′) ∙ (const (idIso (id D)) ⋆ α)) =₁
                  (α ∙ const (comp-unitˡ f))

    hcomp-unitʳ : {C D : CAT} (f f′ : MAP C D)
      → let α = id (f ＝ f′)
        in (const (comp-unitʳ f′) ∙ (α ⋆ const (idIso (id C)))) =₁
                  (α ∙ const (comp-unitʳ f))

    hcomp-assoc : {B C D E : CAT} (f f′ : MAP B C) (g g′ : MAP C D) (h h′ : MAP D E)
      → let X = ((h ＝ h′) × (g ＝ g′)) × (f ＝ f′)
            α : MAP X (f ＝ f′)
            α = pr₂
            β : MAP X (g ＝ g′)
            β = pr₂ ∘ pr₁
            γ : MAP X (h ＝ h′)
            γ = pr₁ ∘ pr₁
        in (const (comp-assoc f′ g′ h′) ∙ ((γ ⋆ β) ⋆ α)) =₁
                  ((γ ⋆ (β ⋆ α)) ∙ const (comp-assoc f g h))
```

The final record retains the book's horizontal composites literally
(`post:Pentagon_And_Triangle_Identities`). The long pentagon route is explicitly
left associated. These fields compare pastings; they are not Agda equalities.

```agda
record PentagonTriangleCoherence (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    comp-pentagon : {A B C D E : CAT} (f : MAP A B) (g : MAP B C)
      (h : MAP C D) (k : MAP D E)
      → let short = comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h)
            long = ((idIso k ⋆ comp-assoc f g h) ∙ comp-assoc f (h ∘ g) k)
                   ∙ (comp-assoc g h k ⋆ idIso f)
        in short =₂ long

    comp-triangle : {C D E : CAT} (f : MAP C D) (g : MAP D E)
      → (comp-unitʳ g ⋆ idIso f) =₂
             ((idIso g ⋆ comp-unitˡ f) ∙ comp-assoc f (id D) g)
```

Joint interchange is deliberately outside `Theory`. No assembly of the
two fixed-input witnesses into this family is assumed.

```agda
record JointInterchange (S : CompositionStructure) : Set (c ⊔ m) where
  open CompositionStructure S
  open Composition S
  field
    interchange-joint : {B C D : CAT} (F G : MAP C D) (h k : MAP B C)
      → let τ : MAP ((F ＝ G) × (h ＝ k)) (F ＝ G)
            τ = pr₁
            σ : MAP ((F ＝ G) × (h ＝ k)) (h ＝ k)
            σ = pr₂
        in ((τ ▷ k) ∙ (F ◁ σ)) =₁ ((G ◁ σ) ∙ (τ ▷ h))

```
