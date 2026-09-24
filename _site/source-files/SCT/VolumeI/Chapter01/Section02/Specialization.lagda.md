# Specializing parameterized comparisons

This module proves comparison lemmas from the supplied Section 1 interface.
In particular, product comparison lifting retains its two projection
witnesses, and the left and right vertical unit laws are specialized to
absolute natural isomorphisms without treating associativity as Agda equality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section02.Specialization
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Products.Comparison V P
open Products.ProductLaws PL
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
```

First apply the chosen inverse to the specified product comparison. The
resulting `image` comparison will supply both projection witnesses.

```agda
module ProductLift {X C D : CAT} {f g : MAP X (C × D)}
  (α : (pr₁ ∘ f) =₁ (pr₁ ∘ g))
  (β : (pr₂ ∘ f) =₁ (pr₂ ∘ g)) where

  private
    comparison = product-isoMap f g
    witness = product-isoMap-isEquiv f g
    back = IsEquiv.inverse witness
    point = pair α β

  lift : f =₁ g
  lift = back ∘ point

  image : (comparison ∘ lift) =₁ point
  image = comp-unitˡ point ∙
    ((IsEquiv.retractionIso witness ▷ point) ⁻¹ ∙
     (comp-assoc point back comparison) ⁻¹)

  β₁ : (pr₁ ◁ lift) =₂ α
  β₁ = ((pair-β₁ α β ∙ (pr₁ ◁ image)) ∙ comp-assoc lift comparison pr₁)
       ∙ (pair-β₁ (postWhisker pr₁) (postWhisker pr₂) ▷ lift) ⁻¹

  β₂ : (pr₂ ◁ lift) =₂ β
  β₂ = ((pair-β₂ α β ∙ (pr₂ ◁ image)) ∙ comp-assoc lift comparison pr₂)
       ∙ (pair-β₂ (postWhisker pr₁) (postWhisker pr₂) ▷ lift) ⁻¹

pair-iso : {X C D : CAT} {f g : MAP X (C × D)}
  → (pr₁ ∘ f) =₁ (pr₁ ∘ g) → (pr₂ ∘ f) =₁ (pr₂ ∘ g) → f =₁ g
pair-iso = ProductLift.lift

pair-iso-β₁ : {X C D : CAT} {f g : MAP X (C × D)}
  (α : (pr₁ ∘ f) =₁ (pr₁ ∘ g)) (β : (pr₂ ∘ f) =₁ (pr₂ ∘ g))
  → (pr₁ ◁ pair-iso α β) =₂ α
pair-iso-β₁ = ProductLift.β₁

pair-iso-β₂ : {X C D : CAT} {f g : MAP X (C × D)}
  (α : (pr₁ ∘ f) =₁ (pr₁ ∘ g)) (β : (pr₂ ∘ f) =₁ (pr₂ ∘ g))
  → (pr₂ ◁ pair-iso α β) =₂ β
pair-iso-β₂ = ProductLift.β₂
```

Pairing respects comparisons and precomposition through specified natural
isomorphisms. In `pair-pre`, the inverse associator exposes each projection
before the product beta comparison is used.

```agda
pair-cong : {X C D : CAT} {a a′ : MAP X C} {b b′ : MAP X D}
  → a =₁ a′ → b =₁ b′ → (pair a b) =₁ (pair a′ b′)
pair-cong {a = a} {a′} {b} {b′} α β = pair-iso
  ((pair-β₁ a′ b′) ⁻¹ ∙ (α ∙ pair-β₁ a b))
  ((pair-β₂ a′ b′) ⁻¹ ∙ (β ∙ pair-β₂ a b))

pair-pre : {R X C D : CAT} (a : MAP X C) (b : MAP X D) (r : MAP R X)
  → (pair a b ∘ r) =₁ (pair (a ∘ r) (b ∘ r))
pair-pre a b r = pair-iso
  ((pair-β₁ (a ∘ r) (b ∘ r)) ⁻¹ ∙
    ((pair-β₁ a b ▷ r) ∙ (comp-assoc r (pair a b) pr₁) ⁻¹))
  ((pair-β₂ (a ∘ r) (b ∘ r)) ⁻¹ ∙
    ((pair-β₂ a b ▷ r) ∙ (comp-assoc r (pair a b) pr₂) ⁻¹))

isoComp-cong : {X C D : CAT} {f g h : MAP C D}
  {β β′ : MAP X (g ＝ h)} {α α′ : MAP X (f ＝ g)}
  → β =₁ β′ → α =₁ α′ → (β ∙ α) =₁ (β′ ∙ α′)
isoComp-cong b a = isoComp ◁ pair-cong b a

isoComp-pre : {R X C D : CAT} {f g h : MAP C D}
  (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g)) (r : MAP R X)
  → ((β ∙ α) ∘ r) =₁ ((β ∘ r) ∙ (α ∘ r))
isoComp-pre β α r = (isoComp ◁ pair-pre β α r) ∙ comp-assoc r (pair β α) isoComp
```

Whiskering and inversion commute with precomposition through the external
associator. Constants also use uniqueness of maps to the terminal category.

```agda
postWhisker-pre : {R X C D E : CAT} {f g : MAP C D}
  (u : MAP D E) (α : MAP X (f ＝ g)) (r : MAP R X)
  → ((u ◁ α) ∘ r) =₁ (u ◁ (α ∘ r))
postWhisker-pre u α r = comp-assoc r α (postWhisker u)

preWhisker-pre : {R X B C D : CAT} {f g : MAP C D}
  (α : MAP X (f ＝ g)) (k : MAP B C) (r : MAP R X)
  → ((α ▷ k) ∘ r) =₁ ((α ∘ r) ▷ k)
preWhisker-pre α k r = comp-assoc r α (preWhisker k)

⁻¹-pre : {R X C D : CAT} {f g : MAP C D}
  (α : MAP X (f ＝ g)) (r : MAP R X)
  → (α ⁻¹ ∘ r) =₁ ((α ∘ r) ⁻¹)
⁻¹-pre α r = comp-assoc r α ＝-inv

const-pre : {R X C : CAT} (x : Obj-abs C) (r : MAP R X)
  → (const x ∘ r) =₁ (const x)
const-pre {R} {X} x r =
  (x ◁ terminal-iso (terminate X ∘ r) (terminate R)) ∙ comp-assoc r (terminate X) x

const-One : {C : CAT} (x : Obj-abs C) → (const {P = One} x) =₁ x
const-One x = comp-unitʳ x ∙ (x ◁ terminal-iso (terminate One) (id One))

hcomp-pre : {R X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : MAP X (g ＝ g′)) (α : MAP X (f ＝ f′)) (r : MAP R X)
  → ((β ⋆ α) ∘ r) =₁ ((β ∘ r) ⋆ (α ∘ r))
hcomp-pre {f′ = f′} {g = g} β α r =
  isoComp-cong (preWhisker-pre β f′ r) (postWhisker-pre g α r)
  ∙ isoComp-pre (β ▷ f′) (g ◁ α) r

hcomp-cong : {X C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  {β β′ : MAP X (g ＝ g′)} {α α′ : MAP X (f ＝ f′)}
  → β =₁ β′ → α =₁ α′ → (β ⋆ α) =₁ (β′ ⋆ α′)
hcomp-cong {f′ = f′} {g = g} b a =
  isoComp-cong (preWhisker f′ ◁ b) (postWhisker g ◁ a)

isoHComp-at : {C D E : CAT} {f f′ : MAP C D} {g g′ : MAP D E}
  (β : g =₁ g′) (α : f =₁ f′)
  → (isoHComp ∘ pair β α) =₂ (β ⋆ α)
isoHComp-at β α = hcomp-cong (pair-β₁ β α) (pair-β₂ β α)
                 ∙ hcomp-pre pr₁ pr₂ (pair β α)
```

Finally specialize a comparison, keeping the normalization of its two
boundaries explicit. The result below is composition of supplied witnesses;
it does not postulate coherent normalization of all expressions.

```agda
specialize : {R X Y : CAT} {f g : MAP X Y} {f′ g′ : MAP R Y}
  → f =₁ g → (r : MAP R X)
  → (f ∘ r) =₁ f′ → (g ∘ r) =₁ g′ → f′ =₁ g′
specialize κ r left right = (right ∙ (κ ▷ r)) ∙ left ⁻¹

isoComp-evaluate : {R X C D : CAT} {f g h : MAP C D}
  (β : MAP X (g ＝ h)) (α : MAP X (f ＝ g)) (r : MAP R X)
  {β′ : MAP R (g ＝ h)} {α′ : MAP R (f ＝ g)}
  → (β ∘ r) =₁ β′ → (α ∘ r) =₁ α′
  → ((β ∙ α) ∘ r) =₁ (β′ ∙ α′)
isoComp-evaluate β α r b a = isoComp-cong b a ∙ isoComp-pre β α r

postWhisker-evaluate : {R X C D E : CAT} {f g : MAP C D}
  (u : MAP D E) (α : MAP X (f ＝ g)) (r : MAP R X)
  {α′ : MAP R (f ＝ g)} → (α ∘ r) =₁ α′
  → ((u ◁ α) ∘ r) =₁ (u ◁ α′)
postWhisker-evaluate u α r a = (postWhisker u ◁ a) ∙ postWhisker-pre u α r

preWhisker-evaluate : {R X B C D : CAT} {f g : MAP C D}
  (α : MAP X (f ＝ g)) (k : MAP B C) (r : MAP R X)
  {α′ : MAP R (f ＝ g)} → (α ∘ r) =₁ α′
  → ((α ▷ k) ∘ r) =₁ (α′ ▷ k)
preWhisker-evaluate α k r a = (preWhisker k ◁ a) ∙ preWhisker-pre α k r

const-evaluate : {X C : CAT} (x : Obj-abs C) (r : Obj-abs X)
  → (const x ∘ r) =₁ x
const-evaluate x r = const-One x ∙ const-pre x r

module TriplePoint {A B C : CAT} (γ : Obj-abs C) (β : Obj-abs B) (α : Obj-abs A) where
  point : Obj-abs ((C × B) × A)
  point = pair (pair γ β) α

  first : ((pr₁ ∘ pr₁) ∘ point) =₁ γ
  first = pair-β₁ γ β ∙ ((pr₁ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₁)

  second : ((pr₂ ∘ pr₁) ∘ point) =₁ β
  second = pair-β₂ γ β ∙ ((pr₂ ◁ pair-β₁ (pair γ β) α) ∙ comp-assoc point pr₁ pr₂)

  third : (pr₂ ∘ point) =₁ α
  third = pair-β₂ (pair γ β) α

module Units (VC : Coherence.VerticalCoherence V T P S) where
  open Coherence.VerticalCoherence VC

  isoComp-unitˡ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (idIso g ∙ α) =₂ α
  isoComp-unitˡ-at {f = f} {g} α =
    specialize (isoComp-unitˡ f g) α
      (isoComp-cong (const-One (idIso g) ∙ const-pre (idIso g) α) (comp-unitˡ α)
       ∙ isoComp-pre (const (idIso g)) (id (f ＝ g)) α)
      (comp-unitˡ α)

  isoComp-unitʳ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ∙ idIso f) =₂ α
  isoComp-unitʳ-at {f = f} {g} α =
    specialize (isoComp-unitʳ f g) α
      (isoComp-cong (comp-unitˡ α) (const-One (idIso f) ∙ const-pre (idIso f) α)
       ∙ isoComp-pre (id (f ＝ g)) (const (idIso f)) α)
      (comp-unitˡ α)

  isoComp-inverseˡ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ⁻¹ ∙ α) =₂ (idIso f)
  isoComp-inverseˡ-at {f = f} {g} α =
    specialize (isoComp-inverseˡ f g) α
      (isoComp-evaluate ((id (f ＝ g)) ⁻¹) (id (f ＝ g)) α
        ((＝-inv ◁ comp-unitˡ α) ∙ ⁻¹-pre (id (f ＝ g)) α)
        (comp-unitˡ α))
      (const-evaluate (idIso f) α)

  isoComp-inverseʳ-at : {C D : CAT} {f g : MAP C D} (α : f =₁ g)
    → (α ∙ α ⁻¹) =₂ (idIso g)
  isoComp-inverseʳ-at {f = f} {g} α =
    specialize (isoComp-inverseʳ f g) α
      (isoComp-evaluate (id (f ＝ g)) ((id (f ＝ g)) ⁻¹) α
        (comp-unitˡ α)
        ((＝-inv ◁ comp-unitˡ α) ∙ ⁻¹-pre (id (f ＝ g)) α))
      (const-evaluate (idIso g) α)

  -- Reassociate the primitive right-nested parameter product explicitly.
  isoComp-assoc-left : {C D : CAT} (f g h k : MAP C D)
    → let X = ((h ＝ k) × (g ＝ h)) × (f ＝ g)
          α : MAP X (f ＝ g)
          α = pr₂
          β : MAP X (g ＝ h)
          β = pr₂ ∘ pr₁
          γ : MAP X (h ＝ k)
          γ = pr₁ ∘ pr₁
      in ((γ ∙ β) ∙ α) =₁ (γ ∙ (β ∙ α))
  isoComp-assoc-left f g h k =
    let γ = pr₁ ∘ pr₁
        β = pr₂ ∘ pr₁
        α = pr₂
        r = pair γ (pair β α)
        first = pair-β₁ γ (pair β α)
        second = pair-β₁ β α ∙ ((pr₁ ◁ pair-β₂ γ (pair β α)) ∙ comp-assoc r pr₂ pr₁)
        third = pair-β₂ β α ∙ ((pr₂ ◁ pair-β₂ γ (pair β α)) ∙ comp-assoc r pr₂ pr₂)
    in specialize (isoComp-assoc f g h k) r
      (isoComp-evaluate (pr₁ ∙ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) r
        (isoComp-evaluate pr₁ (pr₁ ∘ pr₂) r first second) third)
      (isoComp-evaluate pr₁ ((pr₁ ∘ pr₂) ∙ (pr₂ ∘ pr₂)) r first
        (isoComp-evaluate (pr₁ ∘ pr₂) (pr₂ ∘ pr₂) r second third))

  isoComp-assoc-at : {C D : CAT} {f g h k : MAP C D}
    (γ : h =₁ k) (β : g =₁ h) (α : f =₁ g)
    → ((γ ∙ β) ∙ α) =₂ (γ ∙ (β ∙ α))
  isoComp-assoc-at {f = f} {g} {h} {k} γ β α =
    let open TriplePoint γ β α
    in specialize (isoComp-assoc-left f g h k) point
      (isoComp-evaluate ((pr₁ ∘ pr₁) ∙ (pr₂ ∘ pr₁)) pr₂ point
        (isoComp-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) point first second) third)
      (isoComp-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ∙ pr₂) point first
        (isoComp-evaluate (pr₂ ∘ pr₁) pr₂ point second third))

module Whiskering (W : Coherence.WhiskeringCoherence V T P S) where
  open Coherence.WhiskeringCoherence W

  postWhisker-isoComp-at : {C D E : CAT} {f g h : MAP C D}
    (u : MAP D E) (τ : g =₁ h) (σ : f =₁ g)
    → (u ◁ (τ ∙ σ)) =₂ ((u ◁ τ) ∙ (u ◁ σ))
  postWhisker-isoComp-at {f = f} {g} {h} u τ σ =
    let point = pair τ σ
    in specialize (postWhisker-isoComp f g h u) point
      (postWhisker-evaluate u (pr₁ ∙ pr₂) point
        (isoComp-evaluate pr₁ pr₂ point (pair-β₁ τ σ) (pair-β₂ τ σ)))
      (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) point
        (postWhisker-evaluate u pr₁ point (pair-β₁ τ σ))
        (postWhisker-evaluate u pr₂ point (pair-β₂ τ σ)))

  preWhisker-isoComp-at : {B C D : CAT} {f g h : MAP C D}
    (τ : g =₁ h) (σ : f =₁ g) (k : MAP B C)
    → ((τ ∙ σ) ▷ k) =₂ ((τ ▷ k) ∙ (σ ▷ k))
  preWhisker-isoComp-at {f = f} {g} {h} τ σ k =
    let point = pair τ σ
    in specialize (preWhisker-isoComp f g h k) point
      (preWhisker-evaluate (pr₁ ∙ pr₂) k point
        (isoComp-evaluate pr₁ pr₂ point (pair-β₁ τ σ) (pair-β₂ τ σ)))
      (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) point
        (preWhisker-evaluate pr₁ k point (pair-β₁ τ σ))
        (preWhisker-evaluate pr₂ k point (pair-β₂ τ σ)))

  interchange-at : {B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (τ : F =₁ G) (σ : h =₁ k)
    → ((τ ▷ k) ∙ (F ◁ σ)) =₂ ((G ◁ σ) ∙ (τ ▷ h))
  interchange-at {F = F} {G} {h} {k} τ σ =
    specialize (interchange-fixedOuter F G h k τ) σ
      (isoComp-evaluate (const (τ ▷ k)) (F ◁ id (h ＝ k)) σ
        (const-evaluate (τ ▷ k) σ)
        (postWhisker-evaluate F (id (h ＝ k)) σ (comp-unitˡ σ)))
      (isoComp-evaluate (G ◁ id (h ＝ k)) (const (τ ▷ h)) σ
        (postWhisker-evaluate G (id (h ＝ k)) σ (comp-unitˡ σ))
        (const-evaluate (τ ▷ h) σ))
```

```agda
module JointWhiskering (J : Coherence.JointInterchange V T P S) where
  open Coherence.JointInterchange J

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

```
